use std::collections::HashMap;
use std::str::FromStr;

use cranelift::prelude::{
    isa, settings, types, AbiParam, Configurable, EntityRef, FunctionBuilder,
    FunctionBuilderContext, IntCC, Value, Variable,
};
use cranelift_codegen::binemit::NullTrapSink;
use cranelift_codegen::ir::InstBuilder;
use cranelift_codegen::CodegenError;
use cranelift_module::{FuncId, Linkage, Module, ModuleError};
use cranelift_preopt::optimize;
use cranelift_simplejit::{SimpleJITBuilder, SimpleJITModule};
use target_lexicon::triple;

use crate::inference::*;

type Result<T, E = Error> = std::result::Result<T, E>;

#[derive(Debug)]
pub enum Error {
    CraneliftCodegen(CodegenError),
    Undefined(&'static str),
    WrongArgumentCount,
    NotImplemented,
    CraneliftModule(ModuleError),
    FnRedef,
}

impl From<ModuleError> for Error {
    fn from(error: ModuleError) -> Self {
        Error::CraneliftModule(error)
    }
}

impl From<CodegenError> for Error {
    fn from(error: CodegenError) -> Self {
        Error::CraneliftCodegen(error)
    }
}

#[derive(Debug)]
pub struct Function {
    pub prototype: Prototype,
    pub body: Expr,
}

#[derive(Debug)]
pub struct Prototype {
    pub function_name: String,
    pub parameters: Vec<String>,
}

pub struct Generator {
    builder_context: FunctionBuilderContext,
    functions: HashMap<String, CompiledFunction>,
    module: SimpleJITModule,
    variable_builder: VariableBuilder,
}

impl Default for Generator {
    fn default() -> Self {
        let mut flag_builder = settings::builder();
        flag_builder
            .set("opt_level", "speed_and_size")
            .expect("set optlevel");
        let isa_builder = isa::lookup(triple!("x86_64-unknown-unknown-elf")).expect("isa");
        let isa = isa_builder.finish(settings::Flags::new(flag_builder));
        let builder = SimpleJITBuilder::with_isa(isa, cranelift_module::default_libcall_names());
        Self {
            builder_context: FunctionBuilderContext::new(),
            functions: HashMap::new(),
            module: SimpleJITModule::new(builder),
            variable_builder: VariableBuilder::new(),
        }
    }
}

impl Generator {
    pub fn prototype(&mut self, prototype: &Prototype, linkage: Linkage) -> Result<FuncId> {
        let fn_name = &prototype.function_name;
        let params = &prototype.parameters;
        match self.functions.get(fn_name) {
            None => {
                let mut sig = self.module.make_signature();
                for _p in params {
                    sig.params.push(AbiParam::new(types::I64));
                }
                sig.returns.push(AbiParam::new(types::I64));
                let id = self.module.declare_function(&fn_name, linkage, &sig)?;
                self.functions.insert(
                    fn_name.to_string(),
                    CompiledFunction {
                        defined: false,
                        id,
                        param_count: params.len(),
                    },
                );
                Ok(id)
            }
            Some(func) => {
                if func.defined {
                    return Err(Error::FnRedef);
                }
                if func.param_count != params.len() {
                    return Err(Error::WrongArgumentCount);
                }
                Ok(func.id)
            }
        }
    }

    pub fn function(&mut self, func: Function) -> Result<*const u8> {
        let mut ctx = self.module.make_context();
        let sig = &mut ctx.func.signature;
        let params = &func.prototype.parameters;
        for _p in params {
            sig.params.push(AbiParam::new(types::I64));
        }
        sig.returns.push(AbiParam::new(types::I64));
        let fn_name = func.prototype.function_name.to_string();
        let func_id = self.prototype(&func.prototype, Linkage::Export)?;

        let mut builder = FunctionBuilder::new(&mut ctx.func, &mut self.builder_context);
        let entry_block = builder.create_block();
        builder.append_block_params_for_function_params(entry_block);
        builder.switch_to_block(entry_block);
        builder.seal_block(entry_block);

        let mut vals = HashMap::new();
        for (i, name) in params.iter().enumerate() {
            let val = builder.block_params(entry_block)[i];
            let var = self.variable_builder.create_var(&mut builder, val);
            vals.insert(name.clone(), var);
        }

        if let Some(ref mut function) = self.functions.get_mut(&fn_name) {
            function.defined = true;
        }

        let mut generator = FunctionGenerator {
            builder,
            functions: &self.functions,
            module: &mut self.module,
            values: vals,
        };
        let ret = match generator.expr(func.body) {
            Ok(value) => value,
            Err(error) => {
                generator.builder.finalize();
                self.functions.remove(&fn_name);
                return Err(error);
            }
        };
        generator.builder.ins().return_(&[ret]);
        generator.builder.finalize();
        optimize(&mut ctx, &*self.module.isa())?;
        println!("{}", ctx.func.display(None).to_string());

        self.module
            .define_function(func_id, &mut ctx, &mut NullTrapSink {})?;
        self.module.clear_context(&mut ctx);
        self.module.finalize_definitions();

        Ok(self.module.get_finalized_function(func_id))
    }
}

struct VariableBuilder {
    index: usize,
}

impl VariableBuilder {
    fn new() -> Self {
        Self { index: 0 }
    }
    fn create_var(&mut self, builder: &mut FunctionBuilder, value: Value) -> Variable {
        let variable = Variable::new(self.index);
        builder.declare_var(variable, types::I64);
        self.index += 1;
        builder.def_var(variable, value);
        variable
    }
}

struct CompiledFunction {
    defined: bool,
    id: FuncId,
    param_count: usize,
}

pub struct FunctionGenerator<'a> {
    builder: FunctionBuilder<'a>,
    functions: &'a HashMap<String, CompiledFunction>,
    module: &'a mut SimpleJITModule,
    values: HashMap<String, Variable>,
}

impl<'a> FunctionGenerator<'a> {
    fn expr(&mut self, expr: Expr) -> Result<Value> {
        let value = match expr {
            Expr::ELit(lit) => match lit {
                Lit::LInt(n) => self.builder.ins().iconst(types::I64, n),
                Lit::LBool(b) => self.builder.ins().bconst(types::B1, b),
                Lit::LChar(s) => self.builder.ins().iconst(types::I8, s as i64),
            },

            Expr::EVar(name) => match self.values.get(&name) {
                Some(&variable) => self.builder.use_var(variable),
                None => return Err(Error::Undefined("variable")),
            },

            Expr::EBinop(binop) => match binop {
                BinOp::Add(lhs, rhs) => {
                    let lhs = self.expr(*lhs)?;
                    let rhs = self.expr(*rhs)?;
                    self.builder.ins().iadd(lhs, rhs)
                }
                BinOp::Sub(lhs, rhs) => {
                    let lhs = self.expr(*lhs)?;
                    let rhs = self.expr(*rhs)?;
                    self.builder.ins().isub(lhs, rhs)
                }
                BinOp::Mul(lhs, rhs) => {
                    let lhs = self.expr(*lhs)?;
                    let rhs = self.expr(*rhs)?;
                    self.builder.ins().imul(lhs, rhs)
                }
                BinOp::Div(lhs, rhs) => {
                    let lhs = self.expr(*lhs)?;
                    let rhs = self.expr(*rhs)?;
                    self.builder.ins().udiv(lhs, rhs)
                }
                BinOp::Eq(lhs, rhs) => self.icmp(IntCC::Equal, *lhs, *rhs)?,
                BinOp::Ne(lhs, rhs) => self.icmp(IntCC::NotEqual, *lhs, *rhs)?,
                BinOp::Lt(lhs, rhs) => self.icmp(IntCC::SignedLessThan, *lhs, *rhs)?,
                BinOp::Le(lhs, rhs) => self.icmp(IntCC::SignedGreaterThanOrEqual, *lhs, *rhs)?,
                BinOp::Gt(lhs, rhs) => self.icmp(IntCC::SignedGreaterThan, *lhs, *rhs)?,
                BinOp::Ge(lhs, rhs) => self.icmp(IntCC::SignedGreaterThanOrEqual, *lhs, *rhs)?,
            },
            Expr::ECall(name, args) => match self.functions.get(&name) {
                Some(func) => {
                    if func.param_count != args.len() {
                        return Err(Error::WrongArgumentCount);
                    }
                    let local_func = self
                        .module
                        .declare_func_in_func(func.id, &mut self.builder.func);
                    let arguments: Result<Vec<_>> =
                        args.into_iter().map(|arg| self.expr(arg)).collect();
                    let arguments = arguments?;
                    let call = self.builder.ins().call(local_func, &arguments);
                    self.builder.inst_results(call)[0]
                }
                None => return Err(Error::Undefined("function")),
            },
            Expr::EIf(cond, then_body, else_body) => {
                let cond_val = self.expr(*cond)?;

                let then_block = self.builder.create_block();
                let else_block = self.builder.create_block();
                let merge_block = self.builder.create_block();

                self.builder.append_block_param(merge_block, types::I64);

                self.builder.ins().brz(cond_val, else_block, &[]);
                self.builder.ins().jump(then_block, &[]);

                self.builder.switch_to_block(then_block);
                self.builder.seal_block(then_block);

                let then_ret = self.expr(*then_body)?;

                self.builder.ins().jump(merge_block, &[then_ret]);

                self.builder.switch_to_block(else_block);
                self.builder.seal_block(else_block);

                let else_ret = self.expr(*else_body)?;

                self.builder.ins().jump(merge_block, &[else_ret]);

                self.builder.switch_to_block(merge_block);
                self.builder.seal_block(merge_block);

                let phi = self.builder.block_params(merge_block)[0];
                phi
            }
            _ => return Err(Error::NotImplemented),
        };
        Ok(value)
    }

    fn icmp(&mut self, cmp: IntCC, lhs: Expr, rhs: Expr) -> Result<Value> {
        let lhs = self.expr(lhs)?;
        let rhs = self.expr(rhs)?;
        let c = self.builder.ins().icmp(cmp, lhs, rhs);
        Ok(self.builder.ins().bint(types::B1, c))
    }
}

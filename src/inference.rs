use std::collections::{HashMap, HashSet};

#[derive(Clone, Debug)]
pub enum BinOp {
    Eq(Box<Expr>, Box<Expr>),
    Ne(Box<Expr>, Box<Expr>),
    Lt(Box<Expr>, Box<Expr>),
    Le(Box<Expr>, Box<Expr>),
    Gt(Box<Expr>, Box<Expr>),
    Ge(Box<Expr>, Box<Expr>),
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Div(Box<Expr>, Box<Expr>),
}

#[derive(Debug)]
pub enum Error {
    DoesNotOccur,
    CantUnify,
    UnboundVar,
}

type Result<T, E = Error> = std::result::Result<T, E>;

#[derive(Clone, Debug)]
pub enum Expr {
    EVar(String),
    ELit(Lit),
    EApp(Box<Expr>, Box<Expr>),
    ECall(String, Vec<Expr>),
    ELam(String, Box<Expr>),
    ELet(String, Box<Expr>, Box<Expr>),
    ELetRec(String, Box<Expr>, Box<Expr>),
    EBinop(BinOp),
    EAssign(String, Box<Expr>),
    EIf(Box<Expr>, Box<Expr>, Box<Expr>),
}

#[derive(Clone, Debug)]
pub enum Lit {
    LInt(i64),
    LBool(bool),
    LChar(char),
}

#[derive(Clone, Debug, PartialEq)]
pub enum Type {
    TVar(String),
    TInt,
    TBool,
    TChar,
    TCustom(String, Vec<Type>),
    TFun(Box<Type>, Box<Type>),
}

type Subst = HashMap<String, Type>;

impl Type {
    fn free_vars(&self) -> HashSet<String> {
        match self {
            Type::TVar(name) => {
                let mut h = HashSet::new();
                h.insert(name.clone());
                h
            }
            Type::TInt | Type::TBool | Type::TChar => HashSet::new(),
            Type::TCustom(_, ts) => ts
                .iter()
                .map(|t| t.free_vars())
                .flatten()
                .collect::<HashSet<_>>(),
            Type::TFun(a, b) => a
                .free_vars()
                .iter()
                .cloned()
                .chain(b.free_vars().iter().cloned())
                .collect(),
        }
    }

    fn apply_subst(&self, s: &Subst) -> Type {
        match self {
            Type::TVar(name) => s
                .get(name)
                .cloned()
                .unwrap_or_else(|| Type::TVar(name.to_owned())),
            Type::TCustom(name, ts) => {
                Type::TCustom(name.clone(), ts.iter().map(|t| t.apply_subst(&s)).collect())
            }
            Type::TFun(a, b) => Type::TFun(Box::new(a.apply_subst(s)), Box::new(b.apply_subst(s))),
            _ => self.clone(),
        }
    }
}

#[derive(Clone, Debug)]
struct Scheme {
    vars: HashSet<String>,
    t: Type,
}

impl Scheme {
    fn free_vars(&self) -> HashSet<String> {
        self.vars
            .iter()
            .cloned()
            .chain(self.t.free_vars())
            .collect()
    }

    fn apply_subst(&self, s: &Subst) -> Scheme {
        let remain = s
            .clone()
            .into_iter()
            .filter(|(key, _)| !self.vars.contains(key))
            .collect();
        Scheme {
            vars: self.vars.clone(),
            t: self.t.apply_subst(&remain),
        }
    }
}

#[derive(Clone, Default, Debug)]
struct TypeEnv(HashMap<String, Scheme>);

impl TypeEnv {
    fn free_vars(&self) -> HashSet<String> {
        self.0.values().map(Scheme::free_vars).flatten().collect()
    }

    fn apply_subst(&self, s: &Subst) -> TypeEnv {
        TypeEnv(
            self.0
                .iter()
                .map(|(n, sch)| (n.clone(), sch.apply_subst(&s)))
                .collect(),
        )
    }

    fn generalize(&self, t: &Type) -> Scheme {
        Scheme {
            vars: t
                .free_vars()
                .difference(&self.free_vars())
                .cloned()
                .collect(),
            t: t.clone(),
        }
    }
}

#[derive(Default, Debug)]
struct State {
    supply: usize,
    subst: Subst,
}

impl State {
    fn new_type_var(&mut self, prefix: impl AsRef<str>) -> Type {
        let name = format!("{}{}", prefix.as_ref(), self.supply);
        self.supply += 1;
        Type::TVar(name)
    }

    fn var_bind(&mut self, u: impl AsRef<str>, t: &Type) -> Result<()> {
        let u = u.as_ref();
        if let Type::TVar(name) = t {
            if u == name {
                return Ok(());
            }
        }

        if t.free_vars().contains(u) {
            return Err(Error::DoesNotOccur);
        }

        self.subst.insert(u.to_owned(), t.clone());
        Ok(())
    }

    fn unify(&mut self, a: &Type, b: &Type) -> Result<()> {
        match (a, b) {
            (Type::TFun(l1, r1), Type::TFun(l2, r2)) => {
                self.unify(l1, l2)?;
                self.unify(&r1.apply_subst(&self.subst), &r2.apply_subst(&self.subst))?;
                Ok(())
            }
            (Type::TCustom(name1, ts1), Type::TCustom(name2, ts2)) if name1 == name2 && ts1.len() == ts2.len() => {
                let zipped = ts1.iter().zip(ts2.iter());
                for t in zipped {
                    self.unify(&t.0.apply_subst(&self.subst), &t.1.apply_subst(&self.subst))?;
                }
                Ok(())
        }
            (Type::TVar(u), t) | (t, Type::TVar(u)) => self.var_bind(u, t),
            (Type::TInt, Type::TInt) | (Type::TBool, Type::TBool) | (Type::TChar, Type::TChar) => Ok(()),
            _ => return Err(Error::CantUnify),
        }
    }

    fn instantiate(&mut self, scheme: &Scheme) -> Type {
        let s = scheme
            .vars
            .iter()
            .map(|s| (s.clone(), self.new_type_var("a")))
            .collect();
        scheme.t.apply_subst(&s)
    }

    fn infer_lit(&self, lit: &Lit) -> Type {
        match lit {
            Lit::LInt(_) => Type::TInt,
            Lit::LBool(_) => Type::TBool,
            Lit::LChar(_) => Type::TChar,
        }
    }

    fn infer(&mut self, env: &TypeEnv, expr: &Expr) -> Result<Type> {
        let result = match expr {
            Expr::EVar(name) => match env.0.get(name) {
                Some(sigma) => self.instantiate(sigma),
                None => return Err(Error::UnboundVar),
            },
            Expr::ELit(lit) => self.infer_lit(lit),
            Expr::ELam(name, exp) => {
                let tv = self.new_type_var("a");
                let mut env1 = env.clone();
                env1.0.insert(
                    name.to_owned(),
                    Scheme {
                        vars: HashSet::default(),
                        t: tv.clone(),
                    },
                );

                let t1 = self.infer(&env1, exp)?;
                let t = Type::TFun(Box::new(tv.apply_subst(&self.subst)), Box::new(t1));
                t.apply_subst(&self.subst)
            }
            Expr::EApp(fun, arg) => {
                let tv = self.new_type_var("a");
                let t1 = self.infer(env, fun)?;
                let t2 = self.infer(&env.apply_subst(&self.subst), arg)?;

                let t = Type::TFun(Box::new(t2), Box::new(tv.clone()));
                self.unify(&t1.apply_subst(&self.subst), &t)?;

                let t = tv.apply_subst(&self.subst);
                t.apply_subst(&self.subst)
            }
            Expr::ECall(fun, arg) => {
                // let expr = Expr::ELam(fun.clone(), Box::new(arg[0].clone()));
                // self.infer(env, &expr.clone())?
                let expr = Expr::EApp(Box::new(Expr::EVar(fun.clone())), Box::new(arg[0].clone()));
                self.infer(env, &expr.clone())?
            }
            Expr::ELetRec(name, val, body) => {
                let mut env1 = env.clone();
                let tv1 = self.new_type_var("a");
                let tv2 = self.new_type_var("a");
                let t = Type::TFun(Box::new(tv1.clone()), Box::new(tv2.clone()));
                let sch = Scheme {
                    vars: [name.clone()].iter().cloned().collect(),
                    t: t.clone(),
                };
                env1.0.insert(name.clone(), sch);

                let t_val = self.infer(&env1.apply_subst(&self.subst), val)?;
                self.unify(&t.apply_subst(&self.subst), &t_val.apply_subst(&self.subst))?;
                self.infer(&env1.apply_subst(&self.subst), body)?
            }
            Expr::ELet(name, val, body) => {
                let t1 = self.infer(env, val)?;
                let t = env.apply_subst(&self.subst).generalize(&t1);
                let mut env1 = env.clone();
                env1.0.insert(name.clone(), t);

                let t2 = self.infer(&env1.apply_subst(&self.subst), body)?;
                t2.apply_subst(&self.subst)
            }
            Expr::EBinop(binop) => match binop {
                BinOp::Add(lhs, rhs)
                | BinOp::Sub(lhs, rhs)
                | BinOp::Mul(lhs, rhs)
                | BinOp::Div(lhs, rhs) => {
                    let t1 = self.infer(env, &lhs)?;
                    let t2 = self.infer(env, &rhs)?;
                    let t = self.new_type_var("a");
                    self.unify(&t1, &Type::TInt)?;
                    self.unify(&t2, &Type::TInt)?;
                    self.unify(&t, &Type::TInt)?;
                    t.apply_subst(&self.subst)
                }

                BinOp::Eq(lhs, rhs)
                | BinOp::Ne(lhs, rhs)
                | BinOp::Lt(lhs, rhs)
                | BinOp::Le(lhs, rhs)
                | BinOp::Gt(lhs, rhs)
                | BinOp::Ge(lhs, rhs) => {
                    let t1 = self.infer(env, &lhs)?;
                    let t2 = self.infer(env, &rhs)?;
                    let t = self.new_type_var("a");
                    self.unify(&t1, &Type::TInt)?;
                    self.unify(&t2, &Type::TInt)?;
                    self.unify(&t, &Type::TBool)?;
                    t.apply_subst(&self.subst)
                }
            },
            Expr::EAssign(name, expr) => {
                let t = self.infer(env, expr)?;
                self.subst.insert(name.clone(), t.apply_subst(&self.subst).clone());
                t.apply_subst(&self.subst)
            }
            Expr::EIf(e1, e2, e3) => {
                let t1 = self.infer(env, e1)?;
                self.unify(&t1.apply_subst(&self.subst), &Type::TBool)?;
                let t2 = self.infer(env, e2)?;
                let t3 = self.infer(env, e3)?;
                self.unify(&t2.apply_subst(&self.subst), &t3.apply_subst(&self.subst))?;
                t2.apply_subst(&self.subst)
            }
            _ => return Err(Error::DoesNotOccur),
        };
        Ok(result)
    }
}

pub fn infer_type(expr: &Expr) -> Result<Type> {
    let mut state = State::default();
    let env = TypeEnv::default();
    let ty = state.infer(&env, expr)?;
    let res = ty.apply_subst(&state.subst);
    Ok(res)
}

pub fn test() {
    let id = Expr::ELam(String::from("x"), Box::new(Expr::EVar(String::from("x"))));
    let id_t = infer_type(&id);
    println!("id: {:?}", id_t);

    let id1 = Expr::EApp(Box::new(id), Box::new(Expr::ELit(Lit::LInt(1))));
    let id1_t = infer_type(&id1);
    println!("id(1): {:?}", id1_t);

    let addop = Expr::ELam(
        String::from("x"),
        Box::new(Expr::EBinop(BinOp::Add(
            Box::new(Expr::EVar(String::from("x"))),
            Box::new(Expr::ELit(Lit::LInt(1))),
        ))),
    );
    let addop_t = infer_type(&addop);
    println!("\\x -> x + 5: {:?}", addop_t);
    let bad = Expr::EApp(Box::new(id1), Box::new(Expr::ELit(Lit::LInt(2))));
    let bad_t = infer_type(&bad);
    println!("1(2): {:?}", bad_t);
    let unbound = Expr::EVar(String::from("osu"));
    let unbound_t = infer_type(&unbound);
    println!("osu: {:?}", unbound_t);
}

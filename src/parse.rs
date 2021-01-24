use crate::inference::*;

peg::parser!(pub grammar parser() for str {
    pub rule function() -> (String, String, Expr)
        = [' ' | '\t' | '\n']* "fn" _ name:identifier() _
        i:identifier() _
        "=" _ stmt:statement()
        {(name, i, stmt)}

    rule statements() -> Vec<Expr>
        = s:(statement()*) {s}

    rule statement() -> Expr
        = _ e:expression() _ {e}

    rule expression() -> Expr
        = if_else()
        / lambda()
        / let()
        / assignment()
        / binary_op()

    rule if_else() -> Expr
        = "if" _ e:expression() _ "then" _
        then_body:statement() _ "else" _
        else_body:statement()
        {Expr::EIf(Box::new(e), Box::new(then_body), Box::new(else_body))}

    rule lambda() -> Expr
        = "\\" _ i:identifier() _ "->" _ e:expression()
        {Expr::ELam(i, Box::new(e))}

    rule let() -> Expr
        = "let" _ i:identifier() _ "=" _ e1:expression() _ "in" _ e2:expression()
        {Expr::ELet(i, Box::new(e1), Box::new(e2))}

    rule binary_op() -> Expr = precedence!{
        a:@ _ "==" _ b:(@) {Expr::EBinop(BinOp::Eq(Box::new(a), Box::new(b)))}
        a:@ _ "!=" _ b:(@) {Expr::EBinop(BinOp::Ne(Box::new(a), Box::new(b)))}
        a:@ _ "<"  _ b:(@) {Expr::EBinop(BinOp::Lt(Box::new(a), Box::new(b)))}
        a:@ _ "<=" _ b:(@) {Expr::EBinop(BinOp::Le(Box::new(a), Box::new(b)))}
        a:@ _ ">"  _ b:(@) {Expr::EBinop(BinOp::Gt(Box::new(a), Box::new(b)))}
        a:@ _ ">=" _ b:(@) {Expr::EBinop(BinOp::Ge(Box::new(a), Box::new(b)))}

        a:@ _ "+" _ b:(@) {Expr::EBinop(BinOp::Add(Box::new(a), Box::new(b)))}
        a:@ _ "-" _ b:(@) {Expr::EBinop(BinOp::Sub(Box::new(a), Box::new(b)))}

        a:@ _ "*" _ b:(@) {Expr::EBinop(BinOp::Mul(Box::new(a), Box::new(b)))}
        a:@ _ "/" _ b:(@) {Expr::EBinop(BinOp::Div(Box::new(a), Box::new(b)))}

        i:identifier() _ "(" args:((_ e:expression() _ {e}) ** ",") ")" {Expr::ECall(i, args)}
        i:identifier() {Expr::EVar(i)}
        l:literal() {l}
    }

    rule assignment() -> Expr
        = i:identifier() _ "=" _ e:expression() {Expr::EAssign(i, Box::new(e))}
    rule identifier() -> String
        = quiet!{n:$(['a'..='z' | 'A'..='Z' | '_']['a'..='z' | 'A'..='Z' | '0'..='9' | '_']*) {n.to_owned()}}
        / expected!("identifier")
    rule literal() -> Expr
        = n:$(['0'..='9']+) {Expr::ELit(Lit::LInt(n.parse::<i64>().unwrap()))}
        / b:$("True" / "False") {Expr::ELit(Lit::LBool(b.parse::<bool>().unwrap()))}
        / c:$("\'" ([' ' ..= '~']) "\'") {Expr::ELit(Lit::LChar(c.chars().next().unwrap()))}
        / expected!("literal")

    rule _() = quiet!{[' ' | '\t' | '\n']*}
});

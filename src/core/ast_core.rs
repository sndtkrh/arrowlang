
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum BaseType {
    Int,
    Unit,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Base(BaseType),
    Prod(Box<Type>, Box<Type>),
    Fun(Box<Type>, Box<Type>),
    Arr(Box<Type>, Box<Type>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum VarWithType {
    VT(String, Type),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Var {
    V(String),
}


#[derive(Debug, Clone, PartialEq)]
pub enum Term {
    NumInt(i32),
    Unt,
    Var(Var),
    Pair(Box<Term>, Box<Term>),
    Fst(Box<Term>),
    Snd(Box<Term>),
    Lam(VarWithType, Box<Term>),
    App(Box<Term>, Box<Term>),
    CLam(VarWithType, Box<Command>),
    // +
    Plus(Box<Term>, Box<Term>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum VTR  {
    T(Box<Term>),
    V(Box<Value>),
    Resume,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Command {
    Return(VTR),
    // `Let` may contain a term environment and a command environment
    Let(VarWithType, Box<Command>, Box<Command>, Option<(Env, Env)>),
    CApp(Box<Term>, Box<Term>),
    DoOp(Operation, Box<Term>),
    // `Handle` may contain a term environment
    Handle(Box<Command>, Handler, Option<Env>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Operation {
    Op(String),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Handler {
    H(HandlerRet, Vec<HandlerOp>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum HandlerRet {
    HRet(VarWithType, Box<Command>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum HandlerOp {
    HOp(Operation, VarWithType, VarWithType, Box<Command>),
}

pub type EffectDecl = (Operation, Type, Type);
pub type TopLevelTerm = (Var, VarWithType, Type, Term);
pub type TopLevelCommand = (Var, VarWithType, VarWithType, Type, Command);

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    NumInt(i32),
    Unt,
    Pair(Box<Value>, Box<Value>),
    ClosureFunc(Env, Var, Term),
    ClosureArr(Env, Var, Command),
    ClosureContArr(Env, Command),
}

#[derive(Debug, Clone, PartialEq)]
pub enum EvalResult {
    Ok(Value),
    Wrong(String),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Continuation {
    Let(VarWithType, Box<Command>, (Env, Env)),
    Handle(Handler, Env),
}

pub type Env = Vec<(Var, Value)>;

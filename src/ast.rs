
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum BaseType {
    UInt,
    Int,
    Bool,
    Float,
    Vect,
    Mat,
    Unit,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Base(BaseType),
    Prod(Box<Type>, Box<Type>),
    Fun(Box<Type>, Box<Type>),
    Arr(Box<Type>, Box<Type>),
    List(Box<Type>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum VarWithType {
    VT(VarProd, Type),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Var {
    V(String),
}

#[derive(Debug, Clone, PartialEq)]
pub enum VarProd {
    Unused,
    V(String),
    P(Box<VarProd>, Box<VarProd>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum L<T> {
    Nil(Type),
    Cons(T, Box<L<T>>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Term {
    NumInt(i32),
    NumFloat(f32),
    Bool(bool),
    Unt,
    Vect(Vec<f32>),
    Mat(Vec<Vec<f32>>),
    Var(Var),
    Pair(Box<Term>, Box<Term>),
    Fst(Box<Term>),
    Snd(Box<Term>),
    Lam(VarWithType, Box<Term>),
    App(Box<Term>, Box<Term>),
    CLam(VarWithType, Box<Command>),
    If(Box<Term>, Box<Term>, Box<Term>),
    // Float
    Exp,
    // list
    Nil(Type),
    Cons(Box<Term>, Box<Term>),
    Head(Box<Term>),
    Tail(Box<Term>),
    // vector
    VectZero,
    VectSize,
    // matrix
    MatZero,
    MatSize,
    Transpose,
    // +
    Plus(Box<Term>, Box<Term>),
    // *
    Times(Box<Term>, Box<Term>),
    // +.
    PlusF(Box<Term>, Box<Term>),
    // *.
    TimesF(Box<Term>, Box<Term>),
    // /.
    DivF(Box<Term>, Box<Term>),
    // #>
    MatVectMul(Box<Term>, Box<Term>),
    // ==
    EqInt(Box<Term>, Box<Term>),
    // <.
    LTFloat(Box<Term>, Box<Term>),
    // >.
    GTFloat(Box<Term>, Box<Term>),
    // ><
    ProdVecVec(Box<Term>, Box<Term>),
    // $>
    ApplicationVectEntrywise(Box<Term>, Box<Term>),
    // <+>
    VectEntrywisePlus(Box<Term>, Box<Term>),
    // <->
    VectEntrywiseMinus(Box<Term>, Box<Term>),
    // <*>
    VectEntrywiseTimes(Box<Term>, Box<Term>),
    // .>
    ScalarVect(Box<Term>, Box<Term>),
    // #+#
    MatEntrywisePlus(Box<Term>, Box<Term>),
    // #-#
    MatEntrywiseMinus(Box<Term>, Box<Term>),
    // .#
    ScalarMat(Box<Term>, Box<Term>),
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
    NumFloat(f32),
    Bool(bool),
    Vect(Vec<f32>),
    Mat(Vec<Vec<f32>>),
    Unt,
    List(L<Box<Value>>),
    Pair(Box<Value>, Box<Value>),
    ClosureFunc(Env, VarProd, Term),
    ClosureArr(Env, VarProd, Command),
    ClosureContArr(Env, Command),
    // primitive functions
    Exp,
    VectZero,
    VectSize,
    MatZero,
    MatSize,
    Transpose,
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
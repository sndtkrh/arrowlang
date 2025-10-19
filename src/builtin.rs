use crate::ast::{Type, Operation};
use crate::ast::Operation::Op;
// use crate::ast::VarWithType::VT;
use crate::ast::Type::{Base, Prod};
use crate::ast::BaseType::{Int, Float, Vect, Mat, Unit};

// fn builtin_functions() -> Vec<VarWithType> {
//     let mut v = Vec::new();
//     // + : Int -> (Int -> Int)
//     v.push(VT("+".to_string(),  Fun(Box::new(Base(Int)), Box::new(Fun(Box::new(Base(Int)), Box::new(Base(Int)))))));
//     // * : Int -> (Int -> Int)
//     v.push(VT("*".to_string(),  Fun(Box::new(Base(Int)), Box::new(Fun(Box::new(Base(Int)), Box::new(Base(Int)))))));
//     // #> : Mat -> (Vect -> Vect)
//     v.push(VT("#>".to_string(), Fun(Box::new(Base(Mat)), Box::new(Fun(Box::new(Base(Vect)), Box::new(Base(Vect)))))));
//     // @> : (Float -> Float) -> (Vect -> Vect)
//     v.push(VT("@>".to_string(), Fun(Box::new(Fun(Box::new(Base(Float)), Box::new(Base(Float)))), Box::new(Fun(Box::new(Base(Vect)), Box::new(Base(Vect)))))));
//     v
// }

pub fn builtin_effect() -> Vec<(Operation, Type, Type)> {
    let mut v = Vec::new();
    v.push((Op("PrintInt".to_string()), Base(Int), Base(Unit)));
    v.push((Op("PrintFloat".to_string()), Base(Float), Base(Unit)));
    v.push((Op("PrintVec".to_string()), Base(Vect), Base(Unit)));
    v.push((Op("PrintMat".to_string()), Base(Mat), Base(Unit)));
    v.push((Op("SampleNormal".to_string()), Prod(Box::new(Base(Float)), Box::new(Base(Float))), Base(Float)));
    v.push((Op("MatInitNormal".to_string()),
        Prod(Box::new(Base(Int)), Box::new(Prod(Box::new(Base(Int)), Box::new(Prod(Box::new(Base(Float)), Box::new(Base(Float))))))),
        Base(Mat))
    );
    v.push((Op("VecInitNormal".to_string()),
        Prod(Box::new(Base(Int)), Box::new(Prod(Box::new(Base(Float)), Box::new(Base(Float))))),
        Base(Vect))
    );
    v
}

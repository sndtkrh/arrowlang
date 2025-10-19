use crate::ast::{
    VTR, Command, Term, Type, BaseType, Var, VarProd, VarWithType, Operation,
    Handler, HandlerRet, HandlerOp,
    EffectDecl, TopLevelCommand, TopLevelTerm
};

pub fn typecheck_toplevel(effects: &Vec<EffectDecl>, functions: &Vec<TopLevelTerm>, arrows: &Vec<TopLevelCommand>) -> Result<(), String> {
    let mut var_and_type = Vec::new();
    for (Var::V(func_name), VarWithType::VT(_arg_var_name, arg_typ), ret_typ, _func_body) in functions {
        var_and_type.push(VarWithType::VT(
            VarProd::V(func_name.to_string()),
            Type::Fun(Box::new(arg_typ.clone()), Box::new(ret_typ.clone()))
        ));
    }
    for (Var::V(arr_name), VarWithType::VT(_arg_var_name, arg_typ), VarWithType::VT(_arg_var_arr_name, arr_arg_typ), ret_typ, _arr_body) in arrows {
        var_and_type.push(VarWithType::VT(
            VarProd::V(arr_name.to_string()),
            Type::Fun(Box::new(arg_typ.clone()), Box::new(Type::Arr(Box::new(arr_arg_typ.clone()), Box::new(ret_typ.clone()))))
        ));
    }
    for (Var::V(func_name), x, ret_typ, func_body) in functions {
        match typecheck_term(&Term::Lam(x.clone(), Box::new(func_body.clone())), &mut var_and_type, &effects) {
            Ok(Type::Fun(_, ret_typ_)) => {
                if *ret_typ_ != *ret_typ {
                    return Err(format!("Type Error: function {:?}, {:?} != {:?}", func_name, ret_typ, ret_typ_));
                }
            }
            Ok(_) => {
                return Err(format!("{} is not a function type", func_name));
            }
            Err(e) => {
                return Err(format!("{}: {}", func_name, e));
            }
        }
    };
    for (Var::V(arr_name), x, z, ret_typ, arr_body) in arrows {
        match typecheck_term(&Term::Lam(x.clone(), Box::new(Term::CLam(z.clone(), Box::new(arr_body.clone())))), &mut var_and_type, &effects) {
            Ok(Type::Fun(_, arr)) => {
                match *arr {
                    Type::Arr(_, ret_typ_) => {
                        if *ret_typ_ != *ret_typ {
                            return Err(format!("Type Error: arrow {:?}, {:?} != {:?}", arr_name, ret_typ, ret_typ_));
                        }
                    }
                    _ => {
                        return Err(format!("{} is not an arrow type", arr_name));
                    }
                }
            }
            Ok(_) => {
                return Err(format!("{} is not an arrow type", arr_name));
            }
            Err(e) => {
                return Err(format!("{}: {}", arr_name, e));
            }
        }
    };
    return Ok(())
}

fn search_type(name: &String, var: &VarProd, typ: &Type) -> Result<Option<Type>, ()> {
    match (var, typ) {
        (VarProd::Unused, _) => Ok(None),
        (VarProd::V(varname), typ) => {
            if name == varname {
                Ok(Some(typ.clone()))
            } else {
                Ok(None)
            }
        }
        (VarProd::P(var1, var2), Type::Prod(typ1, typ2)) => {
            match search_type(name, var1, typ1) {
                Ok(Some(typ)) => Ok(Some(typ)),
                Ok(None) => search_type(name, var2, typ2),
                Err(()) => Err(()),
            }
        }
        (VarProd::P(_, _), _) => Err(()),
    }
}
fn search_type_of_var(name: &String, var_and_type: &Vec<VarWithType>) -> Result<Type, String> {
    for vt in var_and_type.iter().rev() {
        match vt {
            VarWithType::VT(var, typ) => {
                match search_type(name, var, typ) {
                    Ok(Some(typ)) => {
                        return Ok(typ);
                    }
                    Ok(None) => { }
                    Err(()) => {
                        return Err(format!("illigal product: {:?}", vt));
                    }
                }
            }
        }
    }
    Err(format!("variable not found: {}", name))
}

fn search_type_of_operation(opr: & Operation, effects: & Vec<EffectDecl>) -> Option<(Type, Type)> {
    for (o, typ1, typ2) in effects {
        if opr == o {
            return Some((typ1.clone(), typ2.clone()));
        }
    }
    None
}

pub fn typecheck_handler(
    handler: & Handler,
    var_and_type: &mut Vec<VarWithType>,
    effects: & Vec<EffectDecl>)
    -> Result<(Type , Type), String> {
    match handler {
        Handler::H(hret, hops) => {
            match hret {
                HandlerRet::HRet(vt @ VarWithType::VT(_, typ1), c) => {
                    let mut arrow_var_and_type = vec![vt.clone()];
                    match typecheck_command(c, var_and_type, &mut arrow_var_and_type, effects) {
                        Ok(typ2) => {
                            // Γ ; x : typ1 |- c : typ2
                            for op_clause in hops {
                                match op_clause {
                                    HandlerOp::HOp(opr, vt_k, vt_z, c_op) => {
                                        match search_type_of_operation(opr, effects) {
                                            // op : typ_gamma ~> typ_delta
                                            Some((typ_gamma, typ_delta)) => {
                                                match vt_k {
                                                    // k : typ_delta_ ~> typ2_
                                                    VarWithType::VT(_, Type::Arr(typ_delta_, typ2_)) => {
                                                        if **typ_delta_ != typ_delta {
                                                            return Err(format!("type mismatch (handler 0): {:?} != {:?}", **typ_delta_, typ_delta));
                                                        }
                                                        if **typ2_ != typ2 {
                                                            return Err(format!("type mismatch (handler 1): {:?} != {:?}", **typ2_, typ2));
                                                        }
                                                        match vt_z {
                                                            VarWithType::VT(_, typ_gamma_) => {
                                                                if *typ_gamma_ != typ_gamma {
                                                                    return Err(format!("type mismatch (handler 2): {:?} != {:?}", *typ_gamma_, typ_gamma));
                                                                }
                                                                let mut arrow_var_and_type = vec![vt_z.clone()];
                                                                var_and_type.push(vt_k.clone());
                                                                match typecheck_command(c_op, var_and_type, &mut arrow_var_and_type, effects) {
                                                                    Ok(typ2__) => {
                                                                        if typ2__ != typ2 {
                                                                            return Err(format!("type mismatch (handler 3): {:?} != {:?}", typ2_, typ2));
                                                                        }
                                                                        // Γ, k : typ_delta ~> typ2 ; z : typ_gamma |- c_op : typ2
                                                                    }
                                                                    Err(e) => return Err(e),
                                                                }
                                                            }
                                                        }
                                                    }
                                                    _ => return Err(format!("{:?} is not an arrow type", vt_k)),
                                                }
                                            }
                                            None => return Err(format!("operation {:?} not found", opr)),
                                        }
                                    }
                                }
                            }
                            Ok((typ1.clone(), typ2))
                        }
                        Err(e) => Err(e),
                    }
                }
            }
        }
    }
}

pub fn typecheck_command(
    c: &Command,
    // context Γ
    var_and_type: &mut Vec<VarWithType>,
    // context Δ
    arrow_var_and_type: &mut Vec<VarWithType>,
    // operation and its type
    effects: & Vec<EffectDecl>)
    -> Result<Type, String> {
    match c {
        Command::Return(VTR::Resume) => Err(format!("resume variable")),
        Command::Return(VTR::V(_)) => Err(format!("found a value")),
        Command::Return(VTR::T(t)) => {
            let l = var_and_type.len();
            // concatenate the contexts Γ and Δ
            var_and_type.append(arrow_var_and_type);
            match typecheck_term(t, var_and_type, effects) {
                Ok(typ) => {
                    // resplit the context Γ,Δ into Γ and Δ
                    arrow_var_and_type.append(&mut var_and_type.split_off(l));
                    Ok(typ)
                }
                Err(e) => Err(e),
            }
        }
        Command::Let(vt @ VarWithType::VT(_, typ1), c1, c2, _) => {
            match typecheck_command(c1, var_and_type, arrow_var_and_type, effects) {
                Ok(typ1_) => {
                    if *typ1 == typ1_ {
                        // add the variable to the context Δ
                        arrow_var_and_type.push(vt.clone());
                        match typecheck_command(c2, var_and_type, arrow_var_and_type, effects) {
                            Ok(typ2) => {
                                // remove the variable from the context Δ
                                arrow_var_and_type.pop();
                                Ok(typ2)
                            }
                            Err(e) => Err(e),
                        }
                    } else {
                        Err(format!("type mismatch (Let): {:?} != {:?}", typ1, typ1_))
                    }
                }
                Err(e) => Err(e),
            }
        }
        Command::CApp(t1, t2) => {
            // var_and_type |- t1 : typ1 ~> typ2
            // var_and_type , arrow_var_and_type |- t2 : typ1
            // ---------------------------------------------------
            // var_and_type ; arrow_var_and_type |- t1 @ t2 ! typ2
            //println!("Typecheck CApp: t1={:?}\nt2={:?}\nvar_and_type={:?}\narrow_var_and_type={:?}\n", t1, t2, var_and_type, arrow_var_and_type);
            match typecheck_term(t1, var_and_type, effects) {
                Ok(Type::Arr(typ1, typ2)) => {
                    // concatenate the contexts Γ and Δ
                    let l = var_and_type.len();
                    var_and_type.append(arrow_var_and_type);
                    match typecheck_term(t2, var_and_type, effects) {
                        Ok(typ1_) => {
                            if *typ1 == typ1_ {
                                // resplit the context Γ,Δ into Γ and Δ
                                arrow_var_and_type.append(&mut var_and_type.split_off(l));
                                Ok(*typ2)
                            } else {
                                Err(format!("type mismatch (CApp): {:?} != {:?}", typ1, typ1_))
                            }
                        }
                        Err(e) => Err(e),
                    }
                }
                Ok(typ) => Err(format!("type mismatch (CApp): {:?} is not an arrow type", typ)),
                Err(e) => Err(e),
            }
        }
        Command::DoOp(opr, t) => {
            let l = var_and_type.len();
            // concatenate the contexts Γ and Δ
            var_and_type.append(arrow_var_and_type);
            match typecheck_term(t, var_and_type, effects) {
                Ok(typ) => {
                    match search_type_of_operation(opr, effects) {
                        Some((typ_gamma, typ_delta)) => {
                            if typ == typ_gamma {
                                // resplit the context Γ,Δ into Γ and Δ
                                arrow_var_and_type.append(&mut var_and_type.split_off(l));
                                Ok(typ_delta)
                            } else {
                                Err(format!("type mismatch (DoOp): {:?} != {:?}", typ, typ_gamma))
                            }
                        }
                        None => {
                            Err(format!("unknown operation (DoOp): {:?}", opr))
                        }
                    }
                }
                Err(e) => Err(e),
            }
        }
        Command::Handle(c, handler, _) => {
            // c : typ
            match typecheck_command(c, var_and_type, arrow_var_and_type, effects) {
                Ok(typ) => {
                    match typecheck_handler(handler, var_and_type, effects) {
                        // handler : typ1 ==> typ2
                        Ok((typ1, typ2)) => {
                            if typ == typ1 {
                                Ok(typ2)
                            } else {
                                Err(format!("type mismatch (Handle): {:?} != {:?}", typ, typ1))
                            }
                        }
                        Err(e) => Err(e),
                    }
                }
                Err(e) => Err(e),
            }
        }
    }
}

pub fn typecheck_term(t: &Term, var_and_type: &mut Vec<VarWithType>, effects: & Vec<EffectDecl>) -> Result<Type, String> {
    match t {
        Term::NumInt(_) => Ok(Type::Base(BaseType::Int)),
        Term::NumFloat(_) => Ok(Type::Base(BaseType::Float)),
        Term::Vect(_) => Ok(Type::Base(BaseType::Vect)),
        Term::Mat(mat) => {
            if mat.len() != 0 {
                let n = mat[0].len();
                for row in mat {
                    if row.len() != n {
                        return Err(format!("matrix {:?} is not rectangular", mat));
                    }
                }
            }
            Ok(Type::Base(BaseType::Mat))
        }
        Term::Bool(_) => Ok(Type::Base(BaseType::Bool)),
        Term::Unt => Ok(Type::Base(BaseType::Unit)),
        Term::Exp => Ok(Type::Fun(Box::new(Type::Base(BaseType::Float)), Box::new(Type::Base(BaseType::Float)))),
        // list
        Term::Nil(typ) => Ok(Type::List(Box::new(typ.clone()))),
        Term::Cons(t_head, t_tail) => {
            match typecheck_term(t_head, var_and_type, effects) {
                Ok(typ_head) => {
                    match typecheck_term(t_tail, var_and_type, effects) {
                        Ok(typ_tail) => {
                            if typ_tail == Type::List(Box::new(typ_head.clone())) {
                                Ok(Type::List(Box::new(typ_head)))
                            } else {
                                Err(format!("type mismatch (Cons): {:?} != {:?}", typ_tail, Type::List(Box::new(typ_head))))
                            }
                        }
                        Err(e) => Err(e),
                    }
                }
                Err(e) => Err(e),
            }
        }
        Term::Head(t) => {
            match typecheck_term(t, var_and_type, effects) {
                Ok(Type::List(typ)) => Ok(*typ),
                Ok(typ) => Err(format!("type mismatch (Head): {:?} is not a list", typ)),
                Err(e) => Err(e),
            }
        }
        Term::Tail(t) => {
            match typecheck_term(t, var_and_type, effects) {
                Ok(Type::List(typ)) => Ok(Type::List(typ)),
                Ok(typ) => Err(format!("type mismatch (Tail): {:?} is not a list", typ)),
                Err(e) => Err(e),
            }
        }
        // vector
        Term::VectZero => Ok(Type::Fun(Box::new(Type::Base(BaseType::Int)), Box::new(Type::Base(BaseType::Vect)))),
        Term::VectSize => Ok(Type::Fun(Box::new(Type::Base(BaseType::Vect)), Box::new(Type::Base(BaseType::Int)))),
        // matrix
        Term::MatZero => Ok(Type::Fun(Box::new(Type::Prod(Box::new(Type::Base(BaseType::Int)), Box::new(Type::Base(BaseType::Int)))), Box::new(Type::Base(BaseType::Mat)))),
        Term::MatSize => Ok(Type::Fun(Box::new(Type::Base(BaseType::Mat)), Box::new(Type::Prod(Box::new(Type::Base(BaseType::Int)), Box::new(Type::Base(BaseType::Int)))))),
        Term::Transpose => Ok(Type::Fun(Box::new(Type::Base(BaseType::Mat)), Box::new(Type::Base(BaseType::Mat)))),
        //
        Term::Var(Var::V(vname)) => {
            //println!("Var: vname={:?}\nvar_and_type={:?}\n", vname, var_and_type);
            search_type_of_var(vname, var_and_type)
        }
        Term::Pair(t1, t2) => {
            match typecheck_term(t1, var_and_type, effects) {
                Ok(typ1) => {
                    match typecheck_term(t2, var_and_type, effects) {
                        Ok(typ2) => Ok(Type::Prod(Box::new(typ1), Box::new(typ2))),
                        Err(e) => Err(e),
                    }
                }
                Err(e) => Err(e),
            }
        }
        Term::Fst(t) => {
            match typecheck_term(t, var_and_type, effects) {
                Ok(Type::Prod(typ1, _)) => Ok(*typ1),
                Ok(typ) => Err(format!("type mismatch (Fst): {:?} is not a product type", typ)),
                Err(e) => Err(e),
            }
        }
        Term::Snd(t) => {
            match typecheck_term(t, var_and_type, effects) {
                Ok(Type::Prod(_, typ2)) => Ok(*typ2),
                Ok(typ) => Err(format!("type mismatch (Snd): {:?} is not a product type", typ)),
                Err(e) => Err(e),
            }
        }
        Term::Lam(vt @ VarWithType::VT(_, typ1 ), t) => {
            var_and_type.push(vt.clone());
            //println!("Lam: t={:?}\nvar_and_type={:?}\n", t, var_and_type);
            match typecheck_term(t, var_and_type, effects) {
                Ok(typ2) => {
                    var_and_type.pop();
                    Ok(Type::Fun(Box::new(typ1.clone()), Box::new(typ2.clone())))
                }
                Err(e) => Err(e),
            }
        }
        Term::App(t1, t2) => {
            match typecheck_term(t1, var_and_type, effects) {
                Ok(Type::Fun(typ1, typ2)) => {
                    match typecheck_term(t2, var_and_type, effects) {
                        Ok(typ3) => {
                            if *typ1 == typ3 {
                                Ok(*typ2)
                            } else {
                                Err(format!("type mismatch (App): {:?} != {:?}", typ1, typ3))
                            }
                        }
                        Err(e) => Err(e),
                    }
                }
                Ok(typ) => Err(format!("type mismatch (App): {:?} is not a function", typ)),
                Err(e) => Err(e),
            }
        }
        Term::CLam(vt @ VarWithType::VT(_x, typ1), c) => {
            //println!("Typecheck CLam: vt={:?}\nc={:?}\nvar_and_type={:?}\n", _x, c, var_and_type);
            let mut arrow_var_and_type = vec![vt.clone()];
            match typecheck_command(c, var_and_type, &mut arrow_var_and_type, effects) {
                Ok(typ2) => {
                    Ok(Type::Arr(Box::new(typ1.clone()), Box::new(typ2)))
                }
                Err(e) => Err(e),
            }
        }
        Term::If(t, t1, t2) => {
            match typecheck_term(t, var_and_type, effects) {
                Ok(Type::Base(BaseType::Bool)) => {
                    match typecheck_term(t1, var_and_type, effects) {
                        Ok(typ1) => {
                            match typecheck_term(t2, var_and_type, effects) {
                                Ok(typ2) => {
                                    if typ1 == typ2 {
                                        Ok(typ1)
                                    } else {
                                        Err(format!("type mismatch (If): {:?} != {:?}", typ1, typ2))
                                    }
                                }
                                Err(e) => Err(e),
                            }
                        }
                        Err(e) => Err(e),
                    }
                }
                Ok(typ) => Err(format!("type mismatch (If): {:?} is not Bool", typ)),
                Err(e) => Err(e),
            }
        }
        // binary operations
        Term::Plus(t1, t2) => {
            match typecheck_term(t1, var_and_type, effects) {
                Ok(Type::Base(BaseType::Int)) => {
                    match typecheck_term(t2, var_and_type, effects) {
                        Ok(Type::Base(BaseType::Int)) => {
                            Ok(Type::Base(BaseType::Int))
                        }
                        Ok(typ2) => Err(format!("type mismatch (+): {:?} is not an integer", typ2)),
                        Err(e) => Err(e),
                    }
                }
                Ok(typ1) => Err(format!("type mismatch (+): {:?} is not an integer", typ1)),
                Err(e) => Err(e),
            }
        }
        Term::Times(t1, t2) => {
            match typecheck_term(t1, var_and_type, effects) {
                Ok(Type::Base(BaseType::Int)) => {
                    match typecheck_term(t2, var_and_type, effects) {
                        Ok(Type::Base(BaseType::Int)) => {
                            Ok(Type::Base(BaseType::Int))
                        }
                        Ok(typ2) => Err(format!("type mismatch (*): {:?} is not Int", typ2)),
                        Err(e) => Err(e),
                    }
                }
                Ok(typ1) => Err(format!("type mismatch (*): {:?} is not Int", typ1)),
                Err(e) => Err(e),
            }
        }
        Term::PlusF(t1, t2) => {
            match typecheck_term(t1, var_and_type, effects) {
                Ok(Type::Base(BaseType::Float)) => {
                    match typecheck_term(t2, var_and_type, effects) {
                        Ok(Type::Base(BaseType::Float)) => {
                            Ok(Type::Base(BaseType::Float))
                        }
                        Ok(typ2) => Err(format!("type mismatch (+.): {:?} is not Float", typ2)),
                        Err(e) => Err(e),
                    }
                }
                Ok(typ1) => Err(format!("type mismatch (+.): {:?} is not Float", typ1)),
                Err(e) => Err(e),
            }
        }
        Term::TimesF(t1, t2) => {
            match typecheck_term(t1, var_and_type, effects) {
                Ok(Type::Base(BaseType::Float)) => {
                    match typecheck_term(t2, var_and_type, effects) {
                        Ok(Type::Base(BaseType::Float)) => {
                            Ok(Type::Base(BaseType::Float))
                        }
                        Ok(typ2) => Err(format!("type mismatch (*.): {:?} is not Float", typ2)),
                        Err(e) => Err(e),
                    }
                }
                Ok(typ1) => Err(format!("type mismatch (*.): {:?} is not Float", typ1)),
                Err(e) => Err(e),
            }
        }
        Term::DivF(t1, t2) => {
            match typecheck_term(t1, var_and_type, effects) {
                Ok(Type::Base(BaseType::Float)) => {
                    match typecheck_term(t2, var_and_type, effects) {
                        Ok(Type::Base(BaseType::Float)) => {
                            Ok(Type::Base(BaseType::Float))
                        }
                        Ok(typ2) => Err(format!("type mismatch (/.): {:?} is not Float", typ2)),
                        Err(e) => Err(e),
                    }
                }
                Ok(typ1) => Err(format!("type mismatch (/.): {:?} is not Float", typ1)),
                Err(e) => Err(e),
            }
        }
        Term::MatVectMul(t1, t2) => {
            //println!("MatVectMul: t1={:?}\nt2={:?}\nvar_and_type={:?}\n", t1, t2, var_and_type);
            match typecheck_term(t1, var_and_type, effects) {
                Ok(Type::Base(BaseType::Mat)) => {
                    match typecheck_term(t2, var_and_type, effects) {
                        Ok(Type::Base(BaseType::Vect)) => {
                            Ok(Type::Base(BaseType::Vect))
                        }
                        Ok(typ2) => Err(format!("type mismatch (#>): {:?} is not Vec", typ2)),
                        Err(e) => Err(e),
                    }
                }
                Ok(typ1) => Err(format!("type mismatch (#>): {:?} is not Mat", typ1)),
                Err(e) => Err(e),
            }
        }
        Term::EqInt(t1, t2) => {
            match typecheck_term(t1, var_and_type, effects) {
                Ok(Type::Base(BaseType::Int)) => {
                    match typecheck_term(t2, var_and_type, effects) {
                        Ok(Type::Base(BaseType::Int)) => {
                            Ok(Type::Base(BaseType::Bool))
                        }
                        Ok(typ2) => Err(format!("type mismatch (==): {:?} is not Int", typ2)),
                        Err(e) => Err(e),
                    }
                }
                Ok(typ1) => Err(format!("type mismatch (==): {:?} is not Int", typ1)),
                Err(e) => Err(e),
            }
        }
        Term::LTFloat(t1, t2) => {
            match typecheck_term(t1, var_and_type, effects) {
                Ok(Type::Base(BaseType::Float)) => {
                    match typecheck_term(t2, var_and_type, effects) {
                        Ok(Type::Base(BaseType::Float)) => {
                            Ok(Type::Base(BaseType::Bool))
                        }
                        Ok(typ2) => Err(format!("type mismatch (<.): {:?} is not Int", typ2)),
                        Err(e) => Err(e),
                    }
                }
                Ok(typ1) => Err(format!("type mismatch (<.): {:?} is not Int", typ1)),
                Err(e) => Err(e),
            }
        }
        Term::GTFloat(t1, t2) => {
            match typecheck_term(t1, var_and_type, effects) {
                Ok(Type::Base(BaseType::Float)) => {
                    match typecheck_term(t2, var_and_type, effects) {
                        Ok(Type::Base(BaseType::Float)) => {
                            Ok(Type::Base(BaseType::Bool))
                        }
                        Ok(typ2) => Err(format!("type mismatch (>.): {:?} is not Int", typ2)),
                        Err(e) => Err(e),
                    }
                }
                Ok(typ1) => Err(format!("type mismatch (>.): {:?} is not Int", typ1)),
                Err(e) => Err(e),
            }
        }
        Term::ProdVecVec(t1, t2) => {
            match typecheck_term(t1, var_and_type, effects) {
                Ok(Type::Base(BaseType::Vect)) => {
                    match typecheck_term(t2, var_and_type, effects) {
                        Ok(Type::Base(BaseType::Vect)) => {
                            Ok(Type::Base(BaseType::Mat))
                        }
                        Ok(typ2) => Err(format!("type mismatch (><): {:?} is not Vec", typ2)),
                        Err(e) => Err(e),
                    }
                }
                Ok(typ1) => Err(format!("type mismatch (><): {:?} is not Vec", typ1)),
                Err(e) => Err(e),
            }
        }
        Term::ApplicationVectEntrywise(t1, t2) => {
            match typecheck_term(t1, var_and_type, effects) {
                Ok(Type::Fun(box Type::Base(BaseType::Float), box Type::Base(BaseType::Float))) => {
                    match typecheck_term(t2, var_and_type, effects) {
                        Ok(Type::Base(BaseType::Vect)) => {
                            Ok(Type::Base(BaseType::Vect))
                        }
                        Ok(typ2) => Err(format!("type mismatch ($>): {:?} is not Vec", typ2)),
                        Err(e) => Err(e),
                    }
                }
                Ok(typ1) => Err(format!("type mismatch ($>): {:?} is not Float -> Float", typ1)),
                Err(e) => Err(e),
            }
        }
        Term::VectEntrywisePlus(t1, t2) => {
            match typecheck_term(t1, var_and_type, effects) {
                Ok(Type::Base(BaseType::Vect)) => {
                    match typecheck_term(t2, var_and_type, effects) {
                        Ok(Type::Base(BaseType::Vect)) => {
                            Ok(Type::Base(BaseType::Vect))
                        }
                        Ok(typ2) => Err(format!("type mismatch (<+>): {:?} is not Vec", typ2)),
                        Err(e) => Err(e),
                    }
                }
                Ok(typ1) => Err(format!("type mismatch (<+>): {:?} is not Vec", typ1)),
                Err(e) => Err(e),
            }
        }
        Term::VectEntrywiseMinus(t1, t2) => {
            match typecheck_term(t1, var_and_type, effects) {
                Ok(Type::Base(BaseType::Vect)) => {
                    match typecheck_term(t2, var_and_type, effects) {
                        Ok(Type::Base(BaseType::Vect)) => {
                            Ok(Type::Base(BaseType::Vect))
                        }
                        Ok(typ2) => Err(format!("type mismatch (<->): {:?} is not Vec", typ2)),
                        Err(e) => Err(e),
                    }
                }
                Ok(typ1) => Err(format!("type mismatch (<->): {:?} is not Vec", typ1)),
                Err(e) => Err(e),
            }
        }
        Term::VectEntrywiseTimes(t1, t2) => {
            match typecheck_term(t1, var_and_type, effects) {
                Ok(Type::Base(BaseType::Vect)) => {
                    match typecheck_term(t2, var_and_type, effects) {
                        Ok(Type::Base(BaseType::Vect)) => {
                            Ok(Type::Base(BaseType::Vect))
                        }
                        Ok(typ2) => Err(format!("type mismatch (<*>): {:?} is not Vec", typ2)),
                        Err(e) => Err(e),
                    }
                }
                Ok(typ1) => Err(format!("type mismatch (<*>): {:?} is not Vec", typ1)),
                Err(e) => Err(e),
            }
        }
        Term::ScalarVect(t1, t2) => {
            match typecheck_term(t1, var_and_type, effects) {
                Ok(Type::Base(BaseType::Float)) => {
                    match typecheck_term(t2, var_and_type, effects) {
                        Ok(Type::Base(BaseType::Vect)) => {
                            Ok(Type::Base(BaseType::Vect))
                        }
                        Ok(typ2) => Err(format!("type mismatch (.>): {:?} is not Vec", typ2)),
                        Err(e) => Err(e),
                    }
                }
                Ok(typ1) => Err(format!("type mismatch (.>): {:?} is not Float", typ1)),
                Err(e) => Err(e),
            }
        }
        Term::MatEntrywisePlus(t1, t2) => {
            match typecheck_term(t1, var_and_type, effects) {
                Ok(Type::Base(BaseType::Mat)) => {
                    match typecheck_term(t2, var_and_type, effects) {
                        Ok(Type::Base(BaseType::Mat)) => {
                            Ok(Type::Base(BaseType::Mat))
                        }
                        Ok(typ2) => Err(format!("type mismatch (#+#): {:?} is not Mat", typ2)),
                        Err(e) => Err(e),
                    }
                }
                Ok(typ1) => Err(format!("type mismatch (#+#): {:?} is not Mat", typ1)),
                Err(e) => Err(e),
            }
        }
        Term::MatEntrywiseMinus(t1, t2) => {
            match typecheck_term(t1, var_and_type, effects) {
                Ok(Type::Base(BaseType::Mat)) => {
                    match typecheck_term(t2, var_and_type, effects) {
                        Ok(Type::Base(BaseType::Mat)) => {
                            Ok(Type::Base(BaseType::Mat))
                        }
                        Ok(typ2) => Err(format!("type mismatch (#-#): {:?} is not Mat", typ2)),
                        Err(e) => Err(e),
                    }
                }
                Ok(typ1) => Err(format!("type mismatch (#-#): {:?} is not Mat", typ1)),
                Err(e) => Err(e),
            }
        }
        Term::ScalarMat(t1, t2) => {
            match typecheck_term(t1, var_and_type, effects) {
                Ok(Type::Base(BaseType::Float)) => {
                    match typecheck_term(t2, var_and_type, effects) {
                        Ok(Type::Base(BaseType::Mat)) => {
                            Ok(Type::Base(BaseType::Mat))
                        }
                        Ok(typ2) => Err(format!("type mismatch (.#): {:?} is not Mat", typ2)),
                        Err(e) => Err(e),
                    }
                }
                Ok(typ1) => Err(format!("type mismatch (.#): {:?} is not Float", typ1)),
                Err(e) => Err(e),
            }
        }
    }
}

#[test]
fn test_typecheck_toplevel() {
    use crate::parser::TopLevelParser;
    use crate::builtin;

    let (mut effects, functions, arrows) = TopLevelParser::new().parse("
        effect { Op : Int ~> Int }

        function f x : Int --> Int {
            x + 1
        }

        function g x : Int --> Int {
            g (g x)
        }

        arrow main u : Unit ; u : Unit ~~> Unit {
            let x : Int <~ Op 1 in
            PrintInt (f x)
        }
        "
    ).unwrap();
    effects.extend(builtin::builtin_effect());
    let res = typecheck_toplevel(&effects, &functions, &arrows);
    assert_eq!(res, Ok(()));
}

#[test]
fn test_typecheck_command() {
    use crate::parser::CommandParser;
    
    let t1 = Term::CLam(
        VarWithType::VT(VarProd::V("x".to_string()), Type::Base(BaseType::Int)),
        Box::new(Command::Return(VTR::T(Box::new(Term::Var(Var::V("x".to_string())))))));
    let t2 = Term::NumInt(42);
    let c1 = Command::CApp(Box::new(t1.clone()), Box::new(t2.clone()));
    let res = typecheck_command(&c1, &mut vec![], &mut vec![], &vec![]);
    assert_eq!(res, Ok(Type::Base(BaseType::Int)));

    let c = CommandParser::new().parse("
        let x , y , z : Int * Int * Int <~ return (1, (4 , 5)) in
        return x + y + z
        "
    );
    println!("{:?}", c);
    let res = typecheck_command(&c.unwrap(), &mut vec![], &mut vec![], &vec![]);
    assert_eq!(
        res,
        Ok(Type::Base(BaseType::Int))
    );
}

#[test]
fn test_typecheck_term() {
    use crate::parser::TermParser;

    // λ (x: Int). x
    let id_int = Term::Lam(
        VarWithType::VT(VarProd::V("x".to_string()), Type::Base(BaseType::Int)),
        Box::new(Term::Var(Var::V("x".to_string()))));
    let res = typecheck_term(&id_int, &mut vec![], &mut vec![]);
    assert_eq!(res, Ok(Type::Fun(Box::new(Type::Base(BaseType::Int)), Box::new(Type::Base(BaseType::Int)))));
    
    let int_42 = Term::NumInt(42);
    let res = typecheck_term(&int_42, &mut vec![], &mut vec![]);
    assert_eq!(res, Ok(Type::Base(BaseType::Int)));

    let app_id_42 = Term::App(Box::new(id_int.clone()), Box::new(int_42.clone()));
    let res = typecheck_term(&app_id_42, &mut vec![], &mut vec![]);
    assert_eq!(res, Ok(Type::Base(BaseType::Int)));

    let app_id_id = Term::App(Box::new(id_int.clone()), Box::new(id_int.clone()));
    let res = typecheck_term(&app_id_id, &mut vec![], &mut vec![]);
    assert_eq!(res, Err("type mismatch (App): Base(Int) != Fun(Base(Int), Base(Int))".to_string()));

    let t1 = Term::CLam(
        VarWithType::VT(VarProd::V("x".to_string()), Type::Base(BaseType::Int)),
        Box::new(Command::Return(VTR::T(Box::new(Term::Var(Var::V("x".to_string())))))));
    let res = typecheck_term(&t1, &mut vec![], &mut vec![]);
    assert_eq!(res, Ok(Type::Arr(Box::new(Type::Base(BaseType::Int)), Box::new(Type::Base(BaseType::Int)))));

    let t = Term::EqInt(
        Box::new(Term::NumInt(2)),
        Box::new(Term::NumInt(2))
    );
    let res = typecheck_term(&t, &mut vec![], &mut vec![]);
    assert_eq!(res, Ok(Type::Base(BaseType::Bool)));

    
    let ret = TermParser::new().parse("mat[[1.0, 2.0], [3.0, 4.0]]");
    let res = typecheck_term(&ret.unwrap(), &mut vec![], &mut vec![]);
    assert_eq!(res, Ok(Type::Base(BaseType::Mat)));
}

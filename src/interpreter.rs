use rand::Rng;
use rand_distr::{Normal, Distribution};

use crate::{ast::{
    VTR, L, Env, Value, EvalResult,
    Command, Term, Var, VarWithType, Operation,
    Handler, HandlerRet, HandlerOp,
    TopLevelTerm, TopLevelCommand, Continuation, VarProd
}};
use std::io::Write;

pub fn execute<W: Write, R: Rng>(functions: &Vec<TopLevelTerm>, arrows: &Vec<TopLevelCommand>, writer: &mut W, rng: &mut R) -> EvalResult {
    let mut env: Env = Vec::new();
    let mut env_com: Env = Vec::new();
    for (Var::V(arr_name), VarWithType::VT(x, _), VarWithType::VT(z, _), _, arr_body) in arrows {
        if *arr_name == "main".to_string() {
            if let Err(()) = bind_var_prod(&mut env, x, &Value::Unt) {
                return EvalResult::Wrong("main: failed argument binding".to_string())
            }
            if let Err(()) = bind_var_prod(&mut env, z, &Value::Unt) {
                return EvalResult::Wrong("main: failed command argument binding".to_string())
            }
            return interp_command(arr_body, &mut env, &mut env_com, None, (functions, arrows), &Vec::new(), writer, rng)
        }
    }
    EvalResult::Wrong("main not found".to_string())
}

pub fn replace_hole_command(cont: &Continuation, c: &Command) -> Command {
    match cont {
        Continuation::Let(x, c2, envs) =>
            Command::Let(x.clone(), Box::new(c.clone()), c2.clone(), Some(envs.clone())),
        Continuation::Handle(h, env) =>
            Command::Handle(Box::new(c.clone()), h.clone(), Some(env.clone())),
    }
}

pub fn bind_var_prod(env: &mut Env, vp: &VarProd, val: &Value) -> Result<(), ()> {
    match (vp, val) {
        (VarProd::Unused, _) => Ok(()),
        (VarProd::P(var1, var2), Value::Pair(val1, val2)) => {
            bind_var_prod(env, var1, val1)?;
            bind_var_prod(env, var2, val2)?;
            Ok(())
        }
        (VarProd::P(_, _), _) => Err(()),
        (VarProd::V(varname), _) => {
            env.push((Var::V(varname.clone()), val.clone()));
            Ok(())
        }
    }
}
pub fn interp_command<W: Write, R: Rng>(
    c: &Command,
    env: &Env,
    env_com: &Env,
    resume_val: Option<Value>,
    toplevels: (&Vec<TopLevelTerm>, &Vec<TopLevelCommand>),
    cont_stack: &Vec<&Continuation>,
    writer: &mut W,
    rng: &mut R
) -> EvalResult {
    match c {
        Command::Return(VTR::Resume) => {
            match resume_val {
                Some(val) => {
                    let mut cs = cont_stack.clone();
                    match cs.pop() {
                        Some(cont) => {
                            let c = replace_hole_command(cont, &Command::Return(VTR::V(Box::new(val))));
                            interp_command(&c, env, env_com, None, toplevels, &cs, writer, rng)
                        }
                        None => EvalResult::Ok(val),
                    }
                }
                None => EvalResult::Wrong("resume value is None".to_string()),
            }
        }
        Command::Return(VTR::V(v)) => {
            EvalResult::Ok(*v.clone())
        }
        Command::Return(VTR::T(t)) => {
            match concat_env_interp_term(t, env, env_com, toplevels) {
                EvalResult::Ok(val) => {
                    let mut cs = cont_stack.clone();
                    match cs.pop() {
                        Some(cont) => {
                            let c = replace_hole_command(cont, &Command::Return(VTR::V(Box::new(val))));
                            interp_command(&c, env, env_com, resume_val, toplevels, &cs, writer, rng)
                        }
                        None => EvalResult::Ok(val),
                    }
                }
                wrong @ EvalResult::Wrong(_) => wrong,
            }
        }
        Command::Let(var @ VarWithType::VT(vp, _), c1, c2, envs) => {
            let (env, mut env_com) = match envs {
                Some((e, ec)) => (e.clone(), ec.clone()),
                None => (env.clone(), env_com.clone()),
            };
            match *c1.clone() {
                Command::Return(VTR::V(val1))=> {
                    if let Err(()) = bind_var_prod(&mut env_com, vp, &val1) {
                        return EvalResult::Wrong(format!("cannot bind {:?} to {:?}", vp, val1))
                    }
                    interp_command(c2, &env, &env_com, resume_val, toplevels, cont_stack, writer, rng)
                }
                // if c1 is not Return, then we need to push the continuation to the stack
                _ => {
                    let cont = Continuation::Let(var.clone(), c2.clone(), (env.clone(), env_com.clone()));
                    let mut cs = cont_stack.clone();
                    cs.push(&cont);
                    interp_command(c1, &env, &env_com, resume_val, toplevels, &cs, writer, rng)
                }
            }
        }
        Command::CApp(t1, t2) => {
            match interp_term(t1, env, toplevels) {
                EvalResult::Ok(Value::ClosureArr(env1, vp, arr_body)) => {
                    match concat_env_interp_term(t2, env, env_com, toplevels) {
                        EvalResult::Ok(val2) => {
                            let mut env_com2 = Vec::new();
                            if let Err(()) = bind_var_prod(&mut env_com2, &vp, &val2) {
                                return EvalResult::Wrong(format!("cannot bind {:?} to {:?}", vp, val2))
                            }
                            interp_command(&arr_body, &env1, &env_com2, resume_val, toplevels, cont_stack, writer, rng)
                        }
                        wrong @ EvalResult::Wrong(_) => wrong,
                    }
                }
                EvalResult::Ok(Value::ClosureContArr(env1, cont_body)) => {
                    match concat_env_interp_term(t2, env, env_com, toplevels) {
                        EvalResult::Ok(val2) => {
                            interp_command(&cont_body, &env1, &Vec::new(), Some(val2), toplevels, cont_stack, writer, rng)
                        }
                        wrong @ EvalResult::Wrong(_) => wrong,
                    }
                }
                EvalResult::Ok(val1) => EvalResult::Wrong(format!("interp_command: CApp: val1={:?} is not an arrow closure", val1)),
                wrong @ EvalResult::Wrong(_) => wrong,
            }
        }
        Command::DoOp(op, t) => {
            let mut command = Command::Return(VTR::Resume);
            let mut cs = cont_stack.clone();
            match concat_env_interp_term(t, env, env_com, toplevels) {
                EvalResult::Ok(val) => {
                    while let Some(cont) = cs.pop() {
                        /*
                        * command = cont[ command ]
                        * where cont is
                        *   let x <~ [ ] in c2 or
                        *   handle [ ] with h
                        */
                        command = replace_hole_command(cont, &command);
                        if let Continuation::Handle(Handler::H(_, h_ops), env) = cont {
                            // Op k ; z => { c_op }
                            for HandlerOp::HOp(h_op, VarWithType::VT(k, _), VarWithType::VT(z, _), c_op) in h_ops {
                                if h_op == op {
                                    // handle with this handler
                                    // k
                                    let mut env_hand = env.clone();
                                    if let Err(()) = bind_var_prod(&mut env_hand, k, &Value::ClosureContArr(env.clone(), command.clone())) {
                                        return EvalResult::Wrong(format!("cannot bind {:?} to the continuation closure", k))
                                    }
                                    // z
                                    let mut env_com_hand = Vec::new();
                                    if let Err(()) = bind_var_prod(&mut env_com_hand, z, &val) {
                                        return EvalResult::Wrong(format!("cannot bind {:?} to {:?}", z, val))
                                    }
                                    return interp_command(c_op, &env_hand, &env_com_hand, resume_val, toplevels, &cs, writer, rng)
                                }
                            }
                        }
                    }
                    outermost_handler(op, val, &command, env, toplevels, writer, rng)
                }
                wrong @ EvalResult::Wrong(_) => wrong,
            }
        }
        Command::Handle(c1, h @ Handler::H(HandlerRet::HRet(VarWithType::VT(x, _), c_ret), _), _) => {
            match *c1.clone() {
                Command::Return(VTR::V(val1)) => {
                    let mut env_com_ret = Vec::new();
                    if let Err(()) = bind_var_prod(&mut env_com_ret, x, &*val1) {
                        return EvalResult::Wrong(format!("cannot bind {:?} to {:?}", x, val1))
                    }
                    interp_command(c_ret, &env, &env_com_ret, resume_val, toplevels, cont_stack, writer, rng)
                }
                _ => {
                    let cont = Continuation::Handle(h.clone(), env.clone());
                    let mut cs = cont_stack.clone();
                    cs.push(&cont);
                    interp_command(c1, env, env_com, resume_val, toplevels, &cs, writer, rng)
                }
            }
        }
    }
}

pub fn outermost_handler<W: Write, R: Rng>(
    op: &Operation,
    val: Value,
    command: &Command,
    env: &Env,
    toplevels: (&Vec<TopLevelTerm>, &Vec<TopLevelCommand>),
    writer: &mut W,
    rng: &mut R,
) -> EvalResult {
    if *op == Operation::Op("PrintInt".to_string()) {
        match val {
            Value::NumInt(n) => {
                let _ = writer.write(format!("{}\n", n).as_bytes());
                let _ = writer.flush();
                interp_command(&command, &env, &Vec::new(), Some(Value::Unt), toplevels, &Vec::new(), writer, rng)
            }
            _ => EvalResult::Wrong(format!("interp_command: DoOp: PrintInt: val={:?} is not an integer", val)),
        }
    } else if *op == Operation::Op("PrintFloat".to_string()) {
        match val {
            Value::NumFloat(f) => {
                let _ = writer.write(format!("{}\n", f).as_bytes());
                let _ = writer.flush();
                interp_command(&command, &env, &Vec::new(), Some(Value::Unt), toplevels, &Vec::new(), writer, rng)
            }
            _ => EvalResult::Wrong(format!("{:?} is not a float", val)),
        }
    } else if *op == Operation::Op("PrintVec".to_string()) {
        match val {
            Value::Vect(v) => {
                let _ = writer.write(format!("{:?}\n", v).as_bytes());
                let _ = writer.flush();
                interp_command(&command, &env, &Vec::new(), Some(Value::Unt), toplevels, &Vec::new(), writer, rng)
            }
            _ => EvalResult::Wrong(format!("{:?} is not a vector", val)),
        }
    } else if *op == Operation::Op("PrintMat".to_string()) {
        match val {
            Value::Mat(mat) => {
                let _ = writer.write(format!("{:?}\n", mat).as_bytes());
                let _ = writer.flush();
                interp_command(&command, &env, &Vec::new(), Some(Value::Unt), toplevels, &Vec::new(), writer, rng)
            }
            _ => EvalResult::Wrong(format!("{:?} is not a matrix", val)),
        }
    } else if *op == Operation::Op("SampleNormal".to_string()) {
        match val.clone() {
            Value::Pair(b_mean, b_std_dev) => {
                match (*b_mean, *b_std_dev) {
                    (Value::NumFloat(mean), Value::NumFloat(std_dev)) => {
                        let r = Normal::<f32>::new(mean, std_dev).unwrap().sample(rng);
                        interp_command(&command, &env, &Vec::new(), Some(Value::NumFloat(r)), toplevels, &Vec::new(), writer, rng)
                    }
                    _ => EvalResult::Wrong(format!("{:?} is not a pair of floats", val)),
                }
            }
            _ => EvalResult::Wrong(format!("{:?} is not a pair", val)),
        }
    } else if *op == Operation::Op("MatInitNormal".to_string()) {
        match val.clone() {
            Value::Pair(box m_, box Value::Pair(box n_, box Value::Pair(box mean_, box std_dev_))) => {
                match (m_, n_, mean_, std_dev_) {
                    (Value::NumInt(m), Value::NumInt(n), Value::NumFloat(mean), Value::NumFloat(std_dev)) => {
                        let distr = Normal::<f32>::new(mean, std_dev).unwrap();
                        let mut mat = vec![vec![0.0 ; n as usize]; m as usize];
                        for i in 0..m {
                            for j in 0..n {
                                mat[i as usize][j as usize] = distr.sample(rng);
                            }
                        }
                        interp_command(&command, &env, &Vec::new(), Some(Value::Mat(mat)), toplevels, &Vec::new(), writer, rng)
                    }
                    _ => EvalResult::Wrong(format!("{:?} is not a tuple of type Int * Int * Float * Float", val)),
                }
            }
            _ => EvalResult::Wrong(format!("{:?} is not a tuple", val)),
        }
    } else if *op == Operation::Op("VecInitNormal".to_string()) {
        match val.clone() {
            Value::Pair(box m_, box Value::Pair(box mean_, box std_dev_)) => {
                match (m_, mean_, std_dev_) {
                    (Value::NumInt(m), Value::NumFloat(mean), Value::NumFloat(std_dev)) => {
                        let distr = Normal::<f32>::new(mean, std_dev).unwrap();
                        let mut vec = vec![0.0 ; m as usize];
                        for i in 0..m {
                            vec[i as usize] = distr.sample(rng);
                        }
                        interp_command(&command, &env, &Vec::new(), Some(Value::Vect(vec)), toplevels, &Vec::new(), writer, rng)
                    }
                    _ => EvalResult::Wrong(format!("{:?} is not a tuple of type Int * Float * Float", val)),
                }
            }
            _ => EvalResult::Wrong(format!("{:?} is not a tuple", val)),
        }
    } else {
        EvalResult::Wrong(format!("interp_command: DoOp: Unhandled operation: {:?}", op))
    }
}

pub fn concat_env_interp_term(
    t: &Term,
    env: &Env,
    env_com: &Env,
    toplevels: (&Vec<TopLevelTerm>, &Vec<TopLevelCommand>)
) -> EvalResult {
    let mut concat_env = env.clone();
    concat_env.extend(env_com.clone());
    interp_term(t, &concat_env, toplevels)
}

pub fn interp_term(
    t: &Term,
    env: &Env,
    toplevels @ (functions, arrows): (&Vec<TopLevelTerm>, &Vec<TopLevelCommand>),
) -> EvalResult {
    match t {
        Term::NumInt(n) => EvalResult::Ok(Value::NumInt(*n)),
        Term::NumFloat(f) => EvalResult::Ok(Value::NumFloat(*f)),
        Term::Vect(vec) => EvalResult::Ok(Value::Vect(vec.clone())),
        Term::Mat(mat) => EvalResult::Ok(Value::Mat(mat.clone())),
        Term::Bool(b) => EvalResult::Ok(Value::Bool(*b)),
        Term::Unt => EvalResult::Ok(Value::Unt),
        Term::Exp => EvalResult::Ok(Value::Exp),
        // list
        Term::Nil(typ) => EvalResult::Ok(Value::List(L::Nil(typ.clone()))),
        Term::Cons(t_head, t_tail) => {
            match interp_term(t_head, env, toplevels) {
                EvalResult::Wrong(e) => EvalResult::Wrong(e),
                EvalResult::Ok(v_head) => {
                    match interp_term(t_tail, env, toplevels) {
                        EvalResult::Wrong(e) => EvalResult::Wrong(e),
                        EvalResult::Ok(Value::List(v_tail)) => {
                            EvalResult::Ok(Value::List(L::Cons(Box::new(v_head), Box::new(v_tail))))
                        }
                        EvalResult::Ok(w) => EvalResult::Wrong(format!("Type error: {:?} is not a list", w)),
                    }
                }
            }
        }
        Term::Head(t) => {
            match interp_term(t, env, toplevels) {
                EvalResult::Wrong(e) => EvalResult::Wrong(e),
                EvalResult::Ok(Value::List(L::Nil(_))) => {
                    EvalResult::Wrong(format!("Execution error: head of empty list"))
                }
                EvalResult::Ok(Value::List(L::Cons(v_head, _))) => {
                    EvalResult::Ok(*v_head)
                }
                EvalResult::Ok(w) => EvalResult::Wrong(format!("Type error: {:?} is not a list", w)),
            }
        }
        Term::Tail(t) => {
            match interp_term(t, env, toplevels) {
                EvalResult::Wrong(e) => EvalResult::Wrong(e),
                EvalResult::Ok(Value::List(L::Nil(_))) => {
                    EvalResult::Wrong(format!("Execution error: tail of empty list"))
                }
                EvalResult::Ok(Value::List(L::Cons(_, v_tail))) => {
                    EvalResult::Ok(Value::List(*v_tail))
                }
                EvalResult::Ok(w) => EvalResult::Wrong(format!("Type error: {:?} is not a list", w)),
            }
        }
        // vector
        Term::VectZero => EvalResult::Ok(Value::VectZero),
        Term::VectSize => EvalResult::Ok(Value::VectSize),
        // matrix
        Term::MatZero => EvalResult::Ok(Value::MatZero),
        Term::MatSize => EvalResult::Ok(Value::MatSize),
        Term::Transpose => EvalResult::Ok(Value::Transpose),
        //
        Term::Var(v) => {
            for (vt, val) in env.iter().rev() {
                if vt == v {
                    return EvalResult::Ok(val.clone())
                }
            }
            for (fvar, VarWithType::VT(x, _), _, func_body) in functions {
                if fvar == v {
                    return EvalResult::Ok(Value::ClosureFunc(Vec::new(), x.clone(), func_body.clone()))
                }
            }
            for (avar, VarWithType::VT(x, _), z, _, arr_body) in arrows {
                if avar == v {
                    return EvalResult::Ok(Value::ClosureFunc(Vec::new(), x.clone(), Term::CLam(z.clone(), Box::new(arr_body.clone()))))
                }
            }
            EvalResult::Wrong(format!("Unbound variable: {:?}, environment {:?}", v, env))
        }
        Term::Pair(t1, t2) => {
            match interp_term(t1, env, toplevels) {
                EvalResult::Wrong(e) => EvalResult::Wrong(e),
                EvalResult::Ok(v1) => {
                    match interp_term(t2, env, toplevels) {
                        EvalResult::Wrong(e) => EvalResult::Wrong(e),
                        EvalResult::Ok(v2) => EvalResult::Ok(Value::Pair(Box::new(v1), Box::new(v2))),
                    }
                }
            }
        }
        Term::Fst(t) => {
            match interp_term(t, env, toplevels) {
                EvalResult::Wrong(e) => EvalResult::Wrong(e),
                EvalResult::Ok(Value::Pair(v1, _)) => EvalResult::Ok(*v1),
                EvalResult::Ok(v) => EvalResult::Wrong(format!("Type error: {:?}", v)),
            }
        }
        Term::Snd(t) => {
            match interp_term(t, env, toplevels) {
                EvalResult::Wrong(e) => EvalResult::Wrong(e),
                EvalResult::Ok(Value::Pair(_, v2)) => EvalResult::Ok(*v2),
                EvalResult::Ok(v) => EvalResult::Wrong(format!("Type error: {:?}", v)),
            }
        }
        Term::Lam(VarWithType::VT(x , _typ), t) => {
            EvalResult::Ok(Value::ClosureFunc(env.clone(), x.clone(), *t.clone()))
        }
        Term::App(t1, t2) => {
            match interp_term(t1, env, toplevels) {
                EvalResult::Wrong(e) => EvalResult::Wrong(e),
                
                EvalResult::Ok(v) => {
                    match v {
                        Value::ClosureFunc(mut env1, vp, t) => {
                            match interp_term(t2, env, toplevels) {
                                EvalResult::Wrong(e) => EvalResult::Wrong(e),
                                EvalResult::Ok(v) => {
                                    if let Err(()) = bind_var_prod(&mut env1, &vp, &v) {
                                        return EvalResult::Wrong("failed binding product var".to_string())
                                    }
                                    interp_term(&t, &mut env1, toplevels)
                                }
                            }
                        }
                        // primitive functions
                        Value::Exp => {
                            match interp_term(t2, env, toplevels) {
                                EvalResult::Wrong(e) => EvalResult::Wrong(e),
                                EvalResult::Ok(Value::NumFloat(val)) => {
                                    EvalResult::Ok(Value::NumFloat(val.exp()))
                                }
                                EvalResult::Ok(v) => EvalResult::Wrong(format!("Type error: {:?}", v)),
                            }
                        }
                        Value::VectZero => {
                            match interp_term(t2, env, toplevels) {
                                EvalResult::Wrong(e) => EvalResult::Wrong(e),
                                EvalResult::Ok(Value::NumInt(n)) => {
                                    EvalResult::Ok(Value::Vect(vec![0.0; n.try_into().unwrap()]))
                                }
                                EvalResult::Ok(v) => EvalResult::Wrong(format!("Type error: {:?}", v)),
                            }
                        }
                        Value::VectSize => {
                            match interp_term(t2, env, toplevels) {
                                EvalResult::Wrong(e) => EvalResult::Wrong(e),
                                EvalResult::Ok(Value::Vect(v)) => {
                                    EvalResult::Ok(Value::NumInt(v.len().try_into().unwrap()))
                                }
                                EvalResult::Ok(v) => EvalResult::Wrong(format!("Type error: {:?}", v)),
                            }
                        }
                        Value::MatZero => {
                            match interp_term(t2, env, toplevels) {
                                EvalResult::Wrong(e) => EvalResult::Wrong(e),
                                EvalResult::Ok(Value::Pair(box Value::NumInt(m), box Value::NumInt(n))) => {
                                    EvalResult::Ok(Value::Mat(vec![vec![0.0; n.try_into().unwrap()]; m.try_into().unwrap()]))
                                }
                                EvalResult::Ok(v) => EvalResult::Wrong(format!("Type error: {:?}", v)),
                            }
                        }
                        Value::MatSize => {
                            match interp_term(t2, env, toplevels) {
                                EvalResult::Wrong(e) => EvalResult::Wrong(e),
                                EvalResult::Ok(Value::Mat(m)) => {
                                    EvalResult::Ok(Value::Pair(Box::new(Value::NumInt(m.len().try_into().unwrap())), Box::new(Value::NumInt(m[0].len().try_into().unwrap()))))
                                }
                                EvalResult::Ok(v) => EvalResult::Wrong(format!("Type error: {:?}", v)),
                            }
                        }
                        Value::Transpose => {
                            match interp_term(t2, env, toplevels) {
                                EvalResult::Wrong(e) => EvalResult::Wrong(e),
                                EvalResult::Ok(Value::Mat(mat)) => {
                                    let mut tmat = Vec::new();
                                    for j in 0..mat[0].len() {
                                        let mut row = Vec::new();
                                        for i in 0..mat.len() {
                                            row.push(mat[i][j]);
                                        }
                                        tmat.push(row);
                                    }
                                    EvalResult::Ok(Value::Mat(tmat))
                                }
                                EvalResult::Ok(v) => EvalResult::Wrong(format!("Type error: {:?}", v)),
                            }
                        }
                        // 
                        _ => EvalResult::Wrong(format!("Type error: {:?}", v))
                    }
                }
            }
        }
        Term::CLam(VarWithType::VT(vp, _typ), c) => {
            EvalResult::Ok(Value::ClosureArr(env.clone(), vp.clone(), *c.clone()))
        }
        Term::If(t, t1, t2) => {
            match interp_term(t, env, toplevels) {
                EvalResult::Wrong(e) => EvalResult::Wrong(e),
                EvalResult::Ok(Value::Bool(true)) => interp_term(t1, env, toplevels),
                EvalResult::Ok(Value::Bool(false)) => interp_term(t2, env, toplevels),
                EvalResult::Ok(v) => EvalResult::Wrong(format!("Type error: {:?}", v)),
            }
        }
        Term::Plus(t1, t2) => {
            match interp_term(t1, env, toplevels) {
                EvalResult::Wrong(e) => EvalResult::Wrong(e),
                EvalResult::Ok(Value::NumInt(n1)) => {
                    match interp_term(t2, env, toplevels) {
                        EvalResult::Wrong(e) => EvalResult::Wrong(e),
                        EvalResult::Ok(Value::NumInt(n2)) => EvalResult::Ok(Value::NumInt(n1 + n2)),
                        EvalResult::Ok(v) => EvalResult::Wrong(format!("Type error: {:?}", v)),
                    }
                }
                EvalResult::Ok(v) => EvalResult::Wrong(format!("Type error: {:?}", v)),
            }
        }
        Term::Times(t1, t2) => {
            match interp_term(t1, env, toplevels) {
                EvalResult::Wrong(e) => EvalResult::Wrong(e),
                EvalResult::Ok(Value::NumInt(n1)) => {
                    match interp_term(t2, env, toplevels) {
                        EvalResult::Wrong(e) => EvalResult::Wrong(e),
                        EvalResult::Ok(Value::NumInt(n2)) => EvalResult::Ok(Value::NumInt(n1 * n2)),
                        EvalResult::Ok(v) => EvalResult::Wrong(format!("Type error: {:?}", v)),
                    }
                }
                EvalResult::Ok(v) => EvalResult::Wrong(format!("Type error: {:?}", v)),
            }
        }
        Term::PlusF(t1, t2) => {
            match interp_term(t1, env, toplevels) {
                EvalResult::Wrong(e) => EvalResult::Wrong(e),
                EvalResult::Ok(Value::NumFloat(n1)) => {
                    match interp_term(t2, env, toplevels) {
                        EvalResult::Wrong(e) => EvalResult::Wrong(e),
                        EvalResult::Ok(Value::NumFloat(n2)) => EvalResult::Ok(Value::NumFloat(n1 + n2)),
                        EvalResult::Ok(v) => EvalResult::Wrong(format!("Type error: {:?}", v)),
                    }
                }
                EvalResult::Ok(v) => EvalResult::Wrong(format!("Type error: {:?}", v)),
            }
        }
        Term::TimesF(t1, t2) => {
            match interp_term(t1, env, toplevels) {
                EvalResult::Wrong(e) => EvalResult::Wrong(e),
                EvalResult::Ok(Value::NumFloat(n1)) => {
                    match interp_term(t2, env, toplevels) {
                        EvalResult::Wrong(e) => EvalResult::Wrong(e),
                        EvalResult::Ok(Value::NumFloat(n2)) => EvalResult::Ok(Value::NumFloat(n1 * n2)),
                        EvalResult::Ok(v) => EvalResult::Wrong(format!("Type error: {:?}", v)),
                    }
                }
                EvalResult::Ok(v) => EvalResult::Wrong(format!("Type error: {:?}", v)),
            }
        }
        Term::DivF(t1, t2) => {
            match interp_term(t1, env, toplevels) {
                EvalResult::Wrong(e) => EvalResult::Wrong(e),
                EvalResult::Ok(Value::NumFloat(n1)) => {
                    match interp_term(t2, env, toplevels) {
                        EvalResult::Wrong(e) => EvalResult::Wrong(e),
                        EvalResult::Ok(Value::NumFloat(n2)) => EvalResult::Ok(Value::NumFloat(n1 / n2)),
                        EvalResult::Ok(v) => EvalResult::Wrong(format!("Type error: {:?}", v)),
                    }
                }
                EvalResult::Ok(v) => EvalResult::Wrong(format!("Type error: {:?}", v)),
            }
        }
        Term::MatVectMul(t1, t2) => {
            match interp_term(t1, env, toplevels) {
                EvalResult::Wrong(e) => EvalResult::Wrong(e),
                EvalResult::Ok(Value::Mat(mat)) => {
                    match interp_term(t2, env, toplevels) {
                        EvalResult::Wrong(e) => EvalResult::Wrong(e),
                        EvalResult::Ok(Value::Vect(vec)) => {
                            if mat.len() == 0 && vec.len() == 0 {
                                EvalResult::Ok(Value::Vect(Vec::new()))
                            } else if mat[0].len() != vec.len() {
                                EvalResult::Wrong(format!("Matrix and vector dimensions do not match"))
                            } else {
                                let mut res = Vec::new();
                                for i in 0..mat.len() {
                                    let mut sum = 0.;
                                    for j in 0..mat[0].len() {
                                        sum += mat[i][j] * vec[j];
                                    }
                                    res.push(sum);
                                }
                                EvalResult::Ok(Value::Vect(res))
                            }
                        }
                        EvalResult::Ok(v) => EvalResult::Wrong(format!("Type error: {:?}", v)),
                    }
                }
                EvalResult::Ok(v) => EvalResult::Wrong(format!("Type error: {:?}, expected matrix", v)),
            }
        }
        Term::EqInt(t1, t2) => {
            match interp_term(t1, env, toplevels) {
                EvalResult::Wrong(e) => EvalResult::Wrong(e),
                EvalResult::Ok(Value::NumInt(n1)) => {
                    match interp_term(t2, env, toplevels) {
                        EvalResult::Wrong(e) => EvalResult::Wrong(e),
                        EvalResult::Ok(Value::NumInt(n2)) => EvalResult::Ok(Value::Bool(n1 == n2)),
                        EvalResult::Ok(v) => EvalResult::Wrong(format!("Type error: {:?}", v)),
                    }
                }
                EvalResult::Ok(v) => EvalResult::Wrong(format!("Type error: {:?}", v)),
            }
        }
        Term::LTFloat(t1, t2) => {
            match interp_term(t1, env, toplevels) {
                EvalResult::Wrong(e) => EvalResult::Wrong(e),
                EvalResult::Ok(Value::NumFloat(f1)) => {
                    match interp_term(t2, env, toplevels) {
                        EvalResult::Wrong(e) => EvalResult::Wrong(e),
                        EvalResult::Ok(Value::NumFloat(f2)) => EvalResult::Ok(Value::Bool(f1 < f2)),
                        EvalResult::Ok(v) => EvalResult::Wrong(format!("Type error: {:?}", v)),
                    }
                }
                EvalResult::Ok(v) => EvalResult::Wrong(format!("Type error: {:?}", v)),
            }
        }
        Term::GTFloat(t1, t2) => {
            match interp_term(t1, env, toplevels) {
                EvalResult::Wrong(e) => EvalResult::Wrong(e),
                EvalResult::Ok(Value::NumFloat(f1)) => {
                    match interp_term(t2, env, toplevels) {
                        EvalResult::Wrong(e) => EvalResult::Wrong(e),
                        EvalResult::Ok(Value::NumFloat(f2)) => EvalResult::Ok(Value::Bool(f1 > f2)),
                        EvalResult::Ok(v) => EvalResult::Wrong(format!("Type error: {:?}", v)),
                    }
                }
                EvalResult::Ok(v) => EvalResult::Wrong(format!("Type error: {:?}", v)),
            }
        }
        Term::ProdVecVec(t1, t2) => {
            match interp_term(t1, env, toplevels) {
                EvalResult::Wrong(e) => EvalResult::Wrong(e),
                EvalResult::Ok(Value::Vect(v1)) => {
                    match interp_term(t2, env, toplevels) {
                        EvalResult::Wrong(e) => EvalResult::Wrong(e),
                        EvalResult::Ok(Value::Vect(v2)) => {
                            let mut mat = vec![vec![0.; v2.len()]; v1.len()];
                            for i in 0..v1.len() {
                                for j in 0..v2.len() {
                                    mat[i][j] = v1[i] * v2[j];
                                }
                            }
                            EvalResult::Ok(Value::Mat(mat))
                        }
                        EvalResult::Ok(w) => EvalResult::Wrong(format!("Type error: {:?}", w)),
                    }
                }
                EvalResult::Ok(w) => EvalResult::Wrong(format!("Type error: {:?}", w)),
            }
        }
        Term::ApplicationVectEntrywise(t1, t2) => {
            match interp_term(t1, env, toplevels) {
                EvalResult::Wrong(e) => EvalResult::Wrong(e),
                EvalResult::Ok(Value::ClosureFunc(mut env1, var, func_body)) => {
                    match interp_term(t2, env, toplevels) {
                        EvalResult::Wrong(e) => EvalResult::Wrong(e),
                        EvalResult::Ok(Value::Vect(v2)) => {
                            let mut res = Vec::new();
                            let idx = env1.len();
                            if let VarProd::V(v) = var {
                                env1.push((Var::V(v), Value::NumFloat(0.)));
                            } else {
                                env1.push((Var::V("".to_string()), Value::NumFloat(0.))); // dummy variable
                            }
                            for i in 0..v2.len() {
                                env1[idx].1 = Value::NumFloat(v2[i]); // update the value of the variable in the environment
                                match interp_term(&func_body, &env1, toplevels) {
                                    EvalResult::Ok(Value::NumFloat(flt)) => {
                                        res.push(flt);
                                    }
                                    EvalResult::Ok(_) => return EvalResult::Wrong(format!("Type error: expected float")),
                                    wrong @ EvalResult::Wrong(_) => return wrong,
                                }
                            }
                            EvalResult::Ok(Value::Vect(res))
                        }
                        EvalResult::Ok(w) => EvalResult::Wrong(format!("Type error: {:?}", w)),
                    }
                }
                EvalResult::Ok(w) => EvalResult::Wrong(format!("Type error: {:?}", w)),
            }
        }
        Term::VectEntrywisePlus(t1, t2) => {
            match interp_term(t1, env, toplevels) {
                EvalResult::Wrong(e) => EvalResult::Wrong(e),
                EvalResult::Ok(Value::Vect(v1)) => {
                    match interp_term(t2, env, toplevels) {
                        EvalResult::Wrong(e) => EvalResult::Wrong(e),
                        EvalResult::Ok(Value::Vect(v2)) => {
                            if v1.len() != v2.len() {
                                return EvalResult::Wrong(format!("(<+>): Vectors have different lengths"));
                            }
                            let mut res = Vec::with_capacity(v1.len());
                            for i in 0..v1.len() {
                                res.push(v1[i] + v2[i]);
                            }
                            EvalResult::Ok(Value::Vect(res))
                        }
                        EvalResult::Ok(w) => EvalResult::Wrong(format!("Type error: {:?}", w)),
                    }
                }
                EvalResult::Ok(w) => EvalResult::Wrong(format!("Type error: {:?}", w)),
            }
        }
        Term::VectEntrywiseMinus(t1, t2) => {
            match interp_term(t1, env, toplevels) {
                EvalResult::Wrong(e) => EvalResult::Wrong(e),
                EvalResult::Ok(Value::Vect(v1)) => {
                    match interp_term(t2, env, toplevels) {
                        EvalResult::Wrong(e) => EvalResult::Wrong(e),
                        EvalResult::Ok(Value::Vect(v2)) => {
                            if v1.len() != v2.len() {
                                return EvalResult::Wrong(format!("(<->): Vectors have different lengths"));
                            }
                            let mut res = Vec::with_capacity(v1.len());
                            for i in 0..v1.len() {
                                res.push(v1[i] - v2[i]);
                            }
                            EvalResult::Ok(Value::Vect(res))
                        }
                        EvalResult::Ok(w) => EvalResult::Wrong(format!("Type error: {:?}", w)),
                    }
                }
                EvalResult::Ok(w) => EvalResult::Wrong(format!("Type error: {:?}", w)),
            }
        }
        Term::VectEntrywiseTimes(t1, t2) => {
            match interp_term(t1, env, toplevels) {
                EvalResult::Wrong(e) => EvalResult::Wrong(e),
                EvalResult::Ok(Value::Vect(v1)) => {
                    match interp_term(t2, env, toplevels) {
                        EvalResult::Wrong(e) => EvalResult::Wrong(e),
                        EvalResult::Ok(Value::Vect(v2)) => {
                            if v1.len() != v2.len() {
                                return EvalResult::Wrong(format!("(<*>): Vectors have different lengths"));
                            }
                            let mut res = Vec::with_capacity(v1.len());
                            for i in 0..v1.len() {
                                res.push(v1[i] * v2[i]);
                            }
                            EvalResult::Ok(Value::Vect(res))
                        }
                        EvalResult::Ok(w) => EvalResult::Wrong(format!("Type error: {:?}", w)),
                    }
                }
                EvalResult::Ok(w) => EvalResult::Wrong(format!("Type error: {:?}", w)),
            }
        }
        Term::ScalarVect(t1, t2) => {
            match interp_term(t1, env, toplevels) {
                EvalResult::Wrong(e) => EvalResult::Wrong(e),
                EvalResult::Ok(Value::NumFloat(a)) => {
                    match interp_term(t2, env, toplevels) {
                        EvalResult::Wrong(e) => EvalResult::Wrong(e),
                        EvalResult::Ok(Value::Vect(vect)) => {
                            let mut res = Vec::with_capacity(vect.len());
                            for i in 0..vect.len() {
                                res.push(a * vect[i]);
                            }
                            EvalResult::Ok(Value::Vect(res))
                        }
                        EvalResult::Ok(w) => EvalResult::Wrong(format!("Type error: {:?}", w)),
                    }
                }
                EvalResult::Ok(w) => EvalResult::Wrong(format!("Type error: {:?}", w)),
            }
        }
        Term::MatEntrywisePlus(t1, t2) => {
            match interp_term(t1, env, toplevels) {
                EvalResult::Wrong(e) => EvalResult::Wrong(e),
                EvalResult::Ok(Value::Mat(mat1)) => {
                    match interp_term(t2, env, toplevels) {
                        EvalResult::Wrong(e) => EvalResult::Wrong(e),
                        EvalResult::Ok(Value::Mat(mat2)) => {
                            if mat1.len() != mat2.len() {
                                return EvalResult::Wrong(format!("(#+#): Matrices have different shape"));
                            }
                            if mat1.len() > 0 && mat1[0].len() != mat2[0].len() {
                                return EvalResult::Wrong(format!("(#+#): Matrices have different shape"));
                            }
                            let mut res = Vec::with_capacity(mat1.len());
                            for i in 0..mat1.len() {
                                res.push(Vec::with_capacity(mat1[i].len()));
                                for j in 0..mat1[i].len() {
                                    res[i].push(mat1[i][j] + mat2[i][j]);
                                }
                            }
                            EvalResult::Ok(Value::Mat(res))
                        }
                        EvalResult::Ok(w) => EvalResult::Wrong(format!("Type error: {:?}", w)),
                    }
                }
                EvalResult::Ok(w) => EvalResult::Wrong(format!("Type error: {:?}", w)),
            }
        }
        Term::MatEntrywiseMinus(t1, t2) => {
            match interp_term(t1, env, toplevels) {
                EvalResult::Wrong(e) => EvalResult::Wrong(e),
                EvalResult::Ok(Value::Mat(mat1)) => {
                    match interp_term(t2, env, toplevels) {
                        EvalResult::Wrong(e) => EvalResult::Wrong(e),
                        EvalResult::Ok(Value::Mat(mat2)) => {
                            if mat1.len() != mat2.len() {
                                return EvalResult::Wrong(format!("(#-#): Matrices have different shape"));
                            }
                            if mat1.len() > 0 && mat1[0].len() != mat2[0].len() {
                                return EvalResult::Wrong(format!("(#-#): Matrices have different shape"));
                            }
                            let mut res = Vec::with_capacity(mat1.len());
                            for i in 0..mat1.len() {
                                res.push(Vec::with_capacity(mat1[i].len()));
                                for j in 0..mat1[i].len() {
                                    res[i].push(mat1[i][j] - mat2[i][j]);
                                }
                            }
                            EvalResult::Ok(Value::Mat(res))
                        }
                        EvalResult::Ok(w) => EvalResult::Wrong(format!("Type error: {:?}", w)),
                    }
                }
                EvalResult::Ok(w) => EvalResult::Wrong(format!("Type error: {:?}", w)),
            }
        }
        Term::ScalarMat(t1, t2) => {
            match interp_term(t1, env, toplevels) {
                EvalResult::Wrong(e) => EvalResult::Wrong(e),
                EvalResult::Ok(Value::NumFloat(a)) => {
                    match interp_term(t2, env, toplevels) {
                        EvalResult::Wrong(e) => EvalResult::Wrong(e),
                        EvalResult::Ok(Value::Mat(mat)) => {
                            let mut res = Vec::with_capacity(mat.len());
                            for i in 0..mat.len() {
                                res.push(Vec::with_capacity(mat[i].len()));
                                for j in 0..mat[i].len() {
                                    res[i].push(a * mat[i][j]);
                                }
                            }
                            EvalResult::Ok(Value::Mat(res))
                        }
                        EvalResult::Ok(w) => EvalResult::Wrong(format!("Type error: {:?}", w)),
                    }
                }
                EvalResult::Ok(w) => EvalResult::Wrong(format!("Type error: {:?}", w)),
            }
        }
    }
}

#[test]
fn test_interp_term() {
    use crate::parser::TermParser;
    use crate::ast::{Type, BaseType};
    let empty_env: Env = vec![];

    let t = TermParser::new().parse("1 + 1");
    assert_eq!(interp_term(&t.unwrap(), &mut empty_env.clone(), (&Vec::new(), &Vec::new())), EvalResult::Ok(Value::NumInt(2)));

    let t = TermParser::new().parse("1 + 1 + 2");
    assert_eq!(interp_term(&t.unwrap(), &mut empty_env.clone(), (&Vec::new(), &Vec::new())), EvalResult::Ok(Value::NumInt(4)));

    let t = TermParser::new().parse("2 + 3 * 4");
    assert_eq!(interp_term(&t.unwrap(), &mut empty_env.clone(), (&Vec::new(), &Vec::new())), EvalResult::Ok(Value::NumInt(14)));

    let t = TermParser::new().parse("2 * 3 + 5");
    assert_eq!(interp_term(&t.unwrap(), &mut empty_env.clone(), (&Vec::new(), &Vec::new())), EvalResult::Ok(Value::NumInt(11)));

    let t = TermParser::new().parse("(2 * 3) + 5");
    assert_eq!(interp_term(&t.unwrap(), &mut empty_env.clone(), (&Vec::new(), &Vec::new())), EvalResult::Ok(Value::NumInt(11)));

    let t = TermParser::new().parse("(fn x : Int --> { 3 * x } ) 2 ");
    assert_eq!(interp_term(&t.unwrap(), &mut empty_env.clone(), (&Vec::new(), &Vec::new())), EvalResult::Ok(Value::NumInt(6)));

    let t = TermParser::new().parse("
        (fn x : Int --> {
            fn y : Int --> {
                y * x
            }
        }) 2 3
        "
    );
    assert_eq!(interp_term(&t.unwrap(), &mut empty_env.clone(), (&Vec::new(), &Vec::new())), EvalResult::Ok(Value::NumInt(6)));

    let t = TermParser::new().parse("proj1 (1, 2)");
    assert_eq!(interp_term(&t.unwrap(), &mut empty_env.clone(), (&Vec::new(), &Vec::new())), EvalResult::Ok(Value::NumInt(1)));

    let t = TermParser::new().parse("proj2 (1, 2)");
    assert_eq!(interp_term(&t.unwrap(), &mut empty_env.clone(), (&Vec::new(), &Vec::new())), EvalResult::Ok(Value::NumInt(2)));

    let t = TermParser::new().parse("
        head (cons 1 (cons 2 (cons 3 nil_int)))
        "
        );
    assert_eq!(interp_term(&t.unwrap(), &mut empty_env.clone(), (&Vec::new(), &Vec::new())), EvalResult::Ok(Value::NumInt(1)));

    let t = TermParser::new().parse("
        tail (cons 1 (cons 2 (cons 3 nil_int)))
        "
        );
        assert_eq!(interp_term(&t.unwrap(), &mut empty_env.clone(), (&Vec::new(), &Vec::new())),
        EvalResult::Ok(
            Value::List(
                L::Cons(
                    Box::new(Value::NumInt(2)),
                    Box::new(
                        L::Cons(
                            Box::new(Value::NumInt(3)),
                            Box::new(L::Nil(Type::Base(BaseType::Int)))
                        )
                    )
                )
            )
        )
    );

    let t = TermParser::new().parse("
        (fn x : Float --> { if (x <. 0.0) then 0.0 else x }) $> [1.0, -2.0, 3.0]
        "
    );
    assert_eq!(interp_term(&t.unwrap(), &mut empty_env.clone(), (&Vec::new(), &Vec::new())),
        EvalResult::Ok(Value::Vect(vec![1.0, 0.0, 3.0]))
    );

    let t = TermParser::new().parse("
        [1.0, 3.0, 4.0] <-> [1.0, -2.0, 3.0]
        "
    );
    assert_eq!(interp_term(&t.unwrap(), &mut empty_env.clone(), (&Vec::new(), &Vec::new())),
        EvalResult::Ok(Value::Vect(vec![1.0 - 1.0, 3.0 - (-2.0), 4.0 - 3.0]))
    );

    let t = TermParser::new().parse("
        mat[[1.0, 3.0], [2.0, 1.0]] #+# mat[[1.0, -2.0], [3.0, -1.0]]
        "
    );
    assert_eq!(interp_term(&t.unwrap(), &mut empty_env.clone(), (&Vec::new(), &Vec::new())),
        EvalResult::Ok(Value::Mat(vec![vec![1.0 + 1.0, 3.0 + (-2.0)], vec![2.0 + 3.0, 1.0 + (-1.0)]]))
    );

    let t = TermParser::new().parse("
        transpose mat[[1.0, 3.0], [2.0, 1.0], [3.0, 4.0]]
        "
    );
    assert_eq!(interp_term(&t.unwrap(), &mut empty_env.clone(), (&Vec::new(), &Vec::new())),
        EvalResult::Ok(Value::Mat(vec![vec![1.0, 2.0, 3.0], vec![3.0, 1.0, 4.0]]))
    );
}

#[test]
fn test_interp_command() {
    use rand::SeedableRng;
    use rand::rngs::StdRng;
    use crate::parser::CommandParser;
    use crate::ast::EvalResult;
    use std::io;

    let buf = Vec::new();
    let mut writer = io::BufWriter::new(buf);
    let mut rng: StdRng = SeedableRng::from_seed([0; 32]);

    let c = CommandParser::new().parse("let x : Int <- (1 + 1) in return (x + x)");
    assert_eq!(
        interp_command(&c.unwrap(), &Vec::new(), &Vec::new(), None, (&Vec::new(), &Vec::new()), &Vec::new(), &mut writer, &mut rng),
        EvalResult::Ok(Value::NumInt(4))
    );

    let buf = Vec::new();
    let mut writer = io::BufWriter::new(buf);
    let c = CommandParser::new().parse("
        let u : Unit <~ PrintInt (1 + 1) in
        return 0
        "
    );
    assert_eq!(
        interp_command(&c.clone().unwrap(), &Vec::new(), &Vec::new(), None, (&Vec::new(), &Vec::new()), &Vec::new(), &mut writer, &mut rng),
        EvalResult::Ok(Value::NumInt(0))
    );
    assert_eq!(String::from_utf8(writer.into_inner().unwrap()).unwrap(), "2\n");

    let c = CommandParser::new().parse("
        let u : Unit <~ PrintInt (1 + 2) in
        let u : Unit <~ PrintInt (2 + 3) in
        return (8 * 7)"
    );
    let buf = Vec::new();
    let mut writer = io::BufWriter::new(buf);
    let mut rng: StdRng = SeedableRng::from_seed([0; 32]);
    assert_eq!(
        interp_command(&c.unwrap(), &Vec::new(), &Vec::new(), None, (&Vec::new(), &Vec::new()), &Vec::new(), &mut writer, &mut rng),
        EvalResult::Ok(Value::NumInt(56))
    );
    assert_eq!(String::from_utf8(writer.into_inner().unwrap()).unwrap(), "3\n5\n");

    let c = CommandParser::new().parse("
        handle (
            handle (return 2)
            with {
                return x : Int => { return (x + 1) }
            }
        ) with {
            return x : Int => { return (x + 5) }
        }
        "
    );
    let buf = Vec::new();
    let mut writer = io::BufWriter::new(buf);
    let mut rng: StdRng = SeedableRng::from_seed([0; 32]);
    assert_eq!(
        interp_command(&c.unwrap(), &Vec::new(), &Vec::new(), None, (&Vec::new(), &Vec::new()), &Vec::new(), &mut writer, &mut rng),
        EvalResult::Ok(Value::NumInt(8))
    );

    let c = CommandParser::new().parse("
        handle (
            let u : Unit <~ PrintInt 1 in
            return 2
        ) with {
            return x : Int => { return (x + 5) }
            PrintInt k : (Unit ~> Int) ; z : Int => {
                let u : Unit <~ PrintInt (z + 100) in
                return 1
            }
        }
        "
    );
    let buf = Vec::new();
    let mut writer = io::BufWriter::new(buf);
    let mut rng: StdRng = SeedableRng::from_seed([0; 32]);
    assert_eq!(
        interp_command(&c.unwrap(), &Vec::new(), &Vec::new(), None, (&Vec::new(), &Vec::new()), &Vec::new(), &mut writer, &mut rng),
        EvalResult::Ok(Value::NumInt(1)));
    assert_eq!(String::from_utf8(writer.into_inner().unwrap()).unwrap(), "101\n");

    let c = CommandParser::new().parse("
        handle (
            let u : Unit <~ PrintInt 1 in
            return 2
        ) with {
            return x : Int => { return (x + 5) }
            PrintInt k : (Unit ~> Int) ; z : Int => {
                let u : Unit <~ PrintInt (z + 100) in
                (k @ u)
            }
        }
        "
    );
    let buf = Vec::new();
    let mut writer = io::BufWriter::new(buf);
    let mut rng: StdRng = SeedableRng::from_seed([0; 32]);
    assert_eq!(
        interp_command(&c.unwrap(), &Vec::new(), &Vec::new(), None, (&Vec::new(), &Vec::new()), &Vec::new(), &mut writer, &mut rng),
        EvalResult::Ok(Value::NumInt(7))
    );
    assert_eq!(String::from_utf8(writer.into_inner().unwrap()).unwrap(), "101\n");
    //println!("env: {:?}", env);

    let c = CommandParser::new().parse("
        handle (
            let r : Int <~ Op 1 in
            return (r + 1000)
        ) with {
            return x : Int => {
                return (x + 50)
            }
            Op k : (Int ~> Int) ; z : Int => {
                k @ (z + 200)
            }
        }
        "
    );
    let buf = Vec::new();
    let mut writer = io::BufWriter::new(buf);
    let mut rng: StdRng = SeedableRng::from_seed([0; 32]);
    assert_eq!(
        interp_command(&c.unwrap(), &Vec::new(), &Vec::new(), None, (&Vec::new(), &Vec::new()), &Vec::new(), &mut writer, &mut rng),
        EvalResult::Ok(Value::NumInt(1251))
    );

    let c = CommandParser::new().parse("
        let x, y : Int * Int <~ return (2, 3) in
        return (x + y)
        "
    );
    let buf = Vec::new();
    let mut writer = io::BufWriter::new(buf);
    let mut rng: StdRng = SeedableRng::from_seed([0; 32]);
    assert_eq!(
        interp_command(&c.unwrap(), &Vec::new(), &Vec::new(), None, (&Vec::new(), &Vec::new()), &Vec::new(), &mut writer, &mut rng),
        EvalResult::Ok(Value::NumInt(5))
    );

    let c = CommandParser::new().parse("
        let r : Float <~ SampleNormal (1.0, 1.0) in
        let u : Unit <~ PrintFloat r in
        return r
        "
    );
    let buf = Vec::new();
    let mut writer = io::BufWriter::new(buf);
    let mut rng: StdRng = SeedableRng::from_seed([0; 32]);
    match interp_command(&c.unwrap(), &Vec::new(), &Vec::new(), None, (&Vec::new(), &Vec::new()), &Vec::new(), &mut writer, &mut rng) {
        EvalResult::Ok(Value::NumFloat(_)) => (),
        _ => panic!("not a float"),
    }
}

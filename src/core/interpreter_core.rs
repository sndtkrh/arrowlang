
use crate::core::ast_core::{
    Command, Term, Var, VarWithType, Operation,
    Handler, HandlerRet, HandlerOp,
    TopLevelTerm, TopLevelCommand,
    Value, EvalResult, Continuation, Env, VTR,
};


pub fn replace_hole_command(cont: &Continuation, c: &Command) -> Command {
    match cont {
        Continuation::Let(x, c2, envs) =>
            Command::Let(x.clone(), Box::new(c.clone()), c2.clone(), Some(envs.clone())),
        Continuation::Handle(h, env) =>
            Command::Handle(Box::new(c.clone()), h.clone(), Some(env.clone())),
    }
}

pub fn var_with_type_to_var(vt: &VarWithType) -> Var {
    match vt {
        VarWithType::VT(v, _) => Var::V(v.clone()),
    }
}

pub fn execute(functions: &Vec<TopLevelTerm>, arrows: &Vec<TopLevelCommand>) -> EvalResult {
    let mut env: Env = Vec::new();
    let mut env_com: Env = Vec::new();
    for (Var::V(arr_name), VarWithType::VT(x, _), VarWithType::VT(z, _), _, arr_body) in arrows {
        if *arr_name == "main".to_string() {
            env.push((Var::V(x.clone()), Value::Unt));
            env_com.push((Var::V(z.clone()), Value::Unt));
            return interp_command(arr_body, &mut env, &mut env_com, None, functions, arrows, &Vec::new(), 0)
        }
    }
    EvalResult::Wrong("main not found".to_string())
}

pub fn interp_command(
    c: &Command,
    env: &Env,
    env_com: &Env,
    resume_val: Option<Value>,
    functions: &Vec<TopLevelTerm>,
    arrows: &Vec<TopLevelCommand>,
    cont_stack: &Vec<&Continuation>,
    nest: usize
    ) -> EvalResult {
    println!("{} interp_command: c={:?},\nenv={:?},\nenv_com={:?}\nstack={:?}\n", "*".repeat(nest), c, env, env_com, cont_stack);
    match c {
        Command::Return(VTR::Resume) => {
            match resume_val {
                Some(val) => {
                    let mut cs = cont_stack.clone();
                    match cs.pop() {
                        Some(cont) => {
                            let c = replace_hole_command(cont, &Command::Return(VTR::V(Box::new(val))));
                            interp_command(&c, env, env_com, None, functions, arrows, &cs, nest + 1)
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
            match concat_env_interp_term(t, env, env_com, functions, arrows, nest + 1) {
                EvalResult::Ok(val) => {
                    let mut cs = cont_stack.clone();
                    match cs.pop() {
                        Some(cont) => {
                            let c = replace_hole_command(cont, &Command::Return(VTR::V(Box::new(val))));
                            interp_command(&c, env, env_com, resume_val, functions, arrows, &cs, nest + 1)
                        }
                        None => EvalResult::Ok(val),
                    }
                }
                wrong @ EvalResult::Wrong(_) => wrong,
            }
        }
        Command::Let(var, c1, c2, envs) => {
            let (env, mut env_com) = match envs {
                Some((e, ec)) => (e.clone(), ec.clone()),
                None => (env.clone(), env_com.clone()),
            };
            match *c1.clone() {
                Command::Return(VTR::V(val1))=> {
                    env_com.push((var_with_type_to_var(var), *val1));
                    interp_command(c2, &env, &env_com, resume_val, functions, arrows, cont_stack, nest + 1)
                }
                // if c1 is not Return, then we need to push the continuation to the stack
                _ => {
                    let cont = Continuation::Let(var.clone(), c2.clone(), (env.clone(), env_com.clone()));
                    let mut cs = cont_stack.clone();
                    cs.push(&cont);
                    interp_command(c1, &env, &env_com, resume_val, functions, arrows, &cs, nest + 1)
                }
            }
        }
        Command::CApp(t1, t2) => {
            match interp_term(t1, env, functions, arrows, nest + 1) {
                EvalResult::Ok(Value::ClosureArr(env1, var, arr_body)) => {
                    match concat_env_interp_term(t2, env, env_com, functions, arrows, nest + 1) {
                        EvalResult::Ok(val2) => {
                            interp_command(&arr_body, &env1, &vec![(var, val2)], resume_val, functions, arrows, cont_stack, nest + 1)
                        }
                        wrong @ EvalResult::Wrong(_) => wrong,
                    }
                }
                EvalResult::Ok(Value::ClosureContArr(env1, cont_body)) => {
                    match concat_env_interp_term(t2, env, env_com, functions, arrows, nest + 1) {
                        EvalResult::Ok(val2) => {
                            interp_command(&cont_body, &env1, &Vec::new(), Some(val2), functions, arrows, cont_stack, nest + 1)
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
            match concat_env_interp_term(t, env, env_com, functions, arrows, nest + 1) {
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
                            for HandlerOp::HOp(h_op, k, z, c_op) in h_ops {
                                if h_op == op {
                                    // handle with this handler
                                    // k
                                    let mut env_hand = env.clone();
                                    env_hand.push((var_with_type_to_var(k), Value::ClosureContArr(env.clone(), command.clone())));
                                    // z
                                    let env_com_hand = vec![(var_with_type_to_var(z), val.clone())];
                                    return interp_command(c_op, &env_hand, &env_com_hand, resume_val, functions, arrows, &cs, nest + 1)
                                }
                            }
                        }
                    }
                    // outermost handler
                    if *op == Operation::Op("PrintInt".to_string()) {
                        match val {
                            Value::NumInt(i) => {
                                println!("{}", i);
                                interp_command(&command, &env, &Vec::new(), Some(Value::Unt), functions, arrows, &Vec::new(), nest + 1)
                            }
                            _ => EvalResult::Wrong(format!("interp_command: DoOp: PrintInt: val={:?} is not an integer", val)),
                        }
                    } else {
                        EvalResult::Wrong(format!("interp_command: DoOp: Unhandled operation: {:?}", op))
                    }
                }
                wrong @ EvalResult::Wrong(_) => wrong,
            }
        }
        Command::Handle(c1, h @ Handler::H(HandlerRet::HRet(x, c_ret), _), _h_env) => {
            match *c1.clone() {
                Command::Return(VTR::V(val1)) => {
                    let env_com_ret = vec![(var_with_type_to_var(x), *val1)];
                    interp_command(c_ret, &env, &env_com_ret, resume_val, functions, arrows, cont_stack, nest + 1)
                }
                _ => {
                    let cont = Continuation::Handle(h.clone(), env.clone());
                    let mut cs = cont_stack.clone();
                    cs.push(&cont);
                    interp_command(c1, env, env_com, resume_val, functions, arrows, &cs, nest + 1)
                }
            }
        }
    }
}

pub fn concat_env_interp_term(
    t: &Term,
    env: &Env,
    env_com: &Env,
    functions: &Vec<TopLevelTerm>,
    arrows: &Vec<TopLevelCommand>,
    nest: usize
    ) -> EvalResult {
    let mut concat_env = env.clone();
    concat_env.extend(env_com.clone());
    interp_term(t, &concat_env, functions, arrows, nest)
}

pub fn interp_term(
    t: &Term,
    env: &Env,
    functions: &Vec<TopLevelTerm>,
    arrows: &Vec<TopLevelCommand>,
    nest: usize
    ) -> EvalResult {
    println!("{} interp_term: t={:?},\nenv={:?}\n", "*".repeat(nest), t, env);
    match t {
        Term::NumInt(n) => EvalResult::Ok(Value::NumInt(*n)),
        Term::Unt => EvalResult::Ok(Value::Unt),
        Term::Var(Var::V(var)) => {
            for (Var::V(y), val) in env.iter().rev() {
                if var == y {
                    return EvalResult::Ok(val.clone())
                }
            }
            for (Var::V(fvar), VarWithType::VT(x, _), _, func_body) in functions {
                if var == fvar {
                    return EvalResult::Ok(Value::ClosureFunc(Vec::new(), Var::V(x.to_string()), func_body.clone()))
                }
            }
            for (Var::V(avar), VarWithType::VT(x, _), z, _, arr_body) in arrows {
                if var == avar {
                    return EvalResult::Ok(Value::ClosureFunc(Vec::new(), Var::V(x.to_string()), Term::CLam(z.clone(), Box::new(arr_body.clone()))))
                }
            }
            EvalResult::Wrong(format!("interp_term: Unbound variable {:?}, env={:?}", var, env))
        }
        Term::Pair(t1, t2) => {
            match interp_term(t1, env, functions, arrows, nest) {
                EvalResult::Ok(val1) => {
                    match interp_term(t2, env, functions, arrows, nest) {
                        EvalResult::Ok(val2) => {
                            EvalResult::Ok(Value::Pair(Box::new(val1), Box::new(val2)))
                        }
                        wrong @ EvalResult::Wrong(_) => wrong,
                    }
                }
                wrong @ EvalResult::Wrong(_) => wrong,
            }
        }
        Term::Fst(s) => {
            match interp_term(s, env, functions, arrows, nest) {
                EvalResult::Ok(Value::Pair(val1, _val2)) =>
                    EvalResult::Ok(*val1),
                EvalResult::Ok(val) =>
                    EvalResult::Wrong(format!("interp_term: {:?} is not a pair", val)),
                wrong @ EvalResult::Wrong(_) => wrong,
            }
        }
        Term::Snd(s) => {
            match interp_term(s, env, functions, arrows, nest) {
                EvalResult::Ok(Value::Pair(_val1, val2)) =>
                    EvalResult::Ok(*val2),
                EvalResult::Ok(val) =>
                    EvalResult::Wrong(format!("interp_term: {:?} is not a pair", val)),
                wrong @ EvalResult::Wrong(_) => wrong,
            }
        }
        Term::Lam(VarWithType::VT(varname, _), s) => {
            EvalResult::Ok(Value::ClosureFunc(env.clone(), Var::V(varname.clone()), *s.clone()))
        }
        Term::App(t1, t2) => {
            match interp_term(t1, env, functions, arrows, nest + 1) {
                EvalResult::Ok(Value::ClosureFunc(mut env1, var, func_body)) => {
                    match interp_term(t2, env, functions, arrows, nest + 1) {
                        EvalResult::Ok(val2) => {
                            env1.push((var, val2));
                            interp_term(&func_body, &env1, functions, arrows, nest + 1)
                        }
                        wrong @ EvalResult::Wrong(_) => wrong,
                    }
                }
                EvalResult::Ok(val) => EvalResult::Wrong(format!("interp_term: {:?} is not a function closure", val)),
                wrong @ EvalResult::Wrong(_) => wrong,
            }
        }
        Term::CLam(VarWithType::VT(varname, _), c) => {
            EvalResult::Ok(Value::ClosureArr(env.clone(), Var::V(varname.clone()), *c.clone()))
        }
        Term::Plus(t1, t2) => {
            match interp_term(t1, env, functions, arrows, nest) {
                EvalResult::Ok(Value::NumInt(n1)) => {
                    match interp_term(t2, env, functions, arrows, nest) {
                        EvalResult::Ok(Value::NumInt(n2)) => {
                            EvalResult::Ok(Value::NumInt(n1 + n2))
                        }
                        EvalResult::Ok(val2) => EvalResult::Wrong(format!("interp_term: {:?} is not a number", val2)),
                        wrong @ EvalResult::Wrong(_) => wrong,
                    }
                }
                EvalResult::Ok(val1) => EvalResult::Wrong(format!("interp_term: {:?} is not a number", val1)),
                wrong @ EvalResult::Wrong(_) => wrong,
            }
        }
    }
}

#[test]
fn test() {
    use crate::core::typechecker_core::typecheck_command;
    use crate::parser_core::{TermParser, CommandParser};
    use crate::core::ast_core::{Type, BaseType};

    let t = TermParser::new().parse("1 + 2");
    assert_eq!(interp_term(&t.unwrap(), &Vec::new(), &Vec::new(), &Vec::new(), 0), EvalResult::Ok(Value::NumInt(3)));

    let c = CommandParser::new().parse("
        let x : Int <~ return 1 in
        let y : Int <~ (ar z : Int ~~> { return z + 300 }) @ 20 in
        return x + y
        "
    );
    assert_eq!(
        interp_command(&c.unwrap(), &Vec::new(), &Vec::new(), None, &Vec::new(), &Vec::new(), &Vec::new(), 0),
        EvalResult::Ok(Value::NumInt(321))
    );

    let c = CommandParser::new().parse("
        handle
            let x : Int <~ Op 1 in
            return x
        with {
            return s : Int => {
                return s + 4000
            }
            Op k : Int ~> Int ; z : Int => {
                k @ (z + 50000)
            }
        }
        "
    );
    assert_eq!(
        interp_command(&c.unwrap(), &Vec::new(), &Vec::new(), None, &Vec::new(), &Vec::new(), &Vec::new(), 0),
        EvalResult::Ok(Value::NumInt(54001))
    );

    let c = CommandParser::new().parse("
        handle
            let x : Int <~ return 1 in
            let y : Int <~ (ar z : Int ~~> {
                                let x : Int <~ Op z in
                                return x + 300
                            }) @ 20 in
            return x + y
        with {
            return s : Int => {
                return s + 4000
            }
            Op k : Int ~> Int ; z_ : Int => {
                k @ (z_ + 50000)
            }
        }
        "
    );
    assert_eq!(
        interp_command(&c.unwrap(), &Vec::new(), &Vec::new(), None, &Vec::new(), &Vec::new(), &Vec::new(), 0),
        EvalResult::Ok(Value::NumInt(54321))
    );

    let c = CommandParser::new().parse("
        handle
            let y : Int <~ (ar z : Int ~~> {
                                let x : Int <~ Op z in
                                let a : Int <~ Op z in
                                return x
                            }) @ 20 in
            return y
        with {
            return s : Int => {
                return s
            }
            Op k : Int ~> Int ; p : Int => {
                k @ (p + 100)
            }
        }
        "
    );
    // typecheck
    let tc_res =
        typecheck_command(&c.clone().unwrap(), &mut Vec::new(), &mut Vec::new(),
            &vec![(Operation::Op("Op".to_string()), Type::Base(BaseType::Int), Type::Base(BaseType::Int))]);
    assert!(tc_res.is_ok());
    // execute
    assert_eq!(interp_command(&c.unwrap(), &Vec::new(), &Vec::new(), None, &Vec::new(), &Vec::new(), &Vec::new(), 0), EvalResult::Ok(Value::NumInt(120)));

    let c = CommandParser::new().parse("
        handle
            let x : Int <~ return 1 in
            let a : Int <~ return 0 in
            let y : Int <~ (ar z : Int ~~> {
                                let x : Int <~ Op z in
                                let a : Int <~ Op z in
                                return x + 300
                            }) @ 20 in
            return x + y + a
        with {
            return s : Int => {
                return s + 4000
            }
            Op k : Int ~> Int ; z_ : Int => {
                k @ (z_ + 50000)
            }
        }
        "
    );
    // typecheck
    let tc_res =
        typecheck_command(&c.clone().unwrap(), &mut Vec::new(), &mut Vec::new(),
            &vec![(Operation::Op("Op".to_string()), Type::Base(BaseType::Int), Type::Base(BaseType::Int))]);
    assert!(tc_res.is_ok());
    // execute
    assert_eq!(
        interp_command(&c.unwrap(), &Vec::new(), &Vec::new(), None, &Vec::new(), &Vec::new(), &Vec::new(), 0),
        EvalResult::Ok(Value::NumInt(54321))
    );

    let c = CommandParser::new().parse("
        handle
            let x : Int <~ return 1 in
            let a : Int <~ return 0 in
            let u : Unit <~ PrintInt 10000 in
            let y : Int <~ (ar z : Int ~~> {
                                let x : Int <~ Op z in
                                let a : Int <~ Op (z + 1) in
                                let b : Int <~ Op (z + 2) in
                                return x + 300
                            }) @ 20 in
            return x + y + a
        with {
            return s : Int => {
                return s + 4000
            }
            Op k : Int ~> Int ; z : Int => {
                k @ (z + 50000)
            }
        }
        "
    );
    assert_eq!(
        interp_command(&c.unwrap(), &Vec::new(), &Vec::new(), None, &Vec::new(), &Vec::new(), &Vec::new(), 0),
        EvalResult::Ok(Value::NumInt(54321))
    );
}

#![feature(box_patterns)]
use std::{env, fs, io};
use lalrpop_util::ParseError;
use rand::prelude::{thread_rng};

use builtin::builtin_effect;
use ast::EvalResult;

pub mod core;

pub mod ast;
pub mod typechecker;
pub mod interpreter;
pub mod builtin;

#[macro_use] extern crate lalrpop_util;

lalrpop_mod!(pub parser);
lalrpop_mod!(pub parser_core);

pub enum Mode{
    Core,
    Full,
}

fn main() {
    let args = env::args().collect::<Vec<String>>();
    if args.len() <= 1 {
        println!("No input file");
    } else {
        let mut next_arg = 1;
        let mut mode = Mode::Full;
        if &args[next_arg][..2] == "--" {
            if &args[next_arg] == "--core" {
                mode = Mode::Core;
            } else {
                println!("Unknown option {}", &args[1]);
                return;
            }
            next_arg += 1;
        }
        if args.len() <= next_arg {
            println!("No input file");
            return;
        }
        let filename = &args[next_arg];
        let contents = fs::read_to_string(filename).expect("Something went wrong reading the file");
        match mode {
            Mode::Core => core_mode(&contents),
            Mode::Full => full_mode(&contents),
        }
    }
}

pub fn full_mode(code: &String) {
    match parser::TopLevelParser::new().parse(code) {
        Ok((mut effects, functions, arrows)) => {
            effects.extend(builtin_effect());
            match typechecker::typecheck_toplevel(&effects, &functions, &arrows) {
                Ok(_) => {
                    let mut rng = thread_rng();
                    let mut writer = io::BufWriter::new(io::stdout().lock());
                    if let EvalResult::Wrong(e) = interpreter::execute(&functions, &arrows,  &mut writer, &mut rng) {
                        println!("Interpreter error: {}", e);
                    }
                }
                Err(e) => {
                    println!("TypeCheck error: {}", e);
                }
            }
        }
        Err(e) => {
            print_parse_error(e, code);
        }
    }
}

pub fn core_mode(code: &String) {
    use crate::core::ast_core::{Operation, BaseType, Type};
    match parser_core::TopLevelParser::new().parse(code) {
        Ok((mut effects, functions, arrows)) => {
            println!("arrows: {:?}", arrows);
            effects.extend(vec![(Operation::Op("PrintInt".to_string()), Type::Base(BaseType::Int), Type::Base(BaseType::Unit))]);
            match core::typechecker_core::typecheck_toplevel(&effects, &functions, &arrows) {
                Ok(_) => {
                    if let core::ast_core::EvalResult::Wrong(e) = core::interpreter_core::execute(&functions, &arrows) {
                        println!("Interpreter error: {}", e);
                    }
                }
                Err(e) => {
                    println!("TypeCheck error: {}", e);
                }
            }
        }
        Err(e) => {
            println!("Error: {}", e);
        }
    }
}

pub fn print_parse_error<T> (err: ParseError<usize, T, &str>, code: &String) {
    let lines: Vec<&str> = code.lines().collect();
    let (e, location) = match err {
        ParseError::InvalidToken { location } => ("Invalid token", Some(location)),
        ParseError::UnrecognizedEof { location, expected: _ } => ("Unrecognized EOF", Some(location)),
        ParseError::UnrecognizedToken { token: (location, _, _), expected: _} => ("Unrecognized token", Some(location)),
        ParseError::ExtraToken { token: (location, _, _) } => ("Extra token", Some(location)),
        ParseError::User { error } => (error, None),
    };
    println!("Parse error: {}", e);
    if let Some(loc) = location {
        let mut n = 0;
        for (i, line) in lines.iter().enumerate() {
            if n + line.len() >= loc {
                println!("{}:{}", i + 1, loc - n);
                if i > 0 {
                    println!("{:3} |{}", i, lines[i - 1]);
                }
                println!("{:3} |{}", i + 1, line);
                println!("     {}", " ".repeat(loc - n) + "^");
                if i < lines.len() - 1 {
                    println!("{:3} |{}", i + 2, lines[i + 1]);
                }
                break;
            }
            n += line.len() + 1;
        }
    }
}

#[test]
fn test_arrowml_term() {
    use crate::parser::TermParser;
    use crate::ast::{VTR, Term, Type, Command, BaseType, VarWithType, Var, VarProd};

    let one = TermParser::new().parse("1");
    assert_eq!(one, Ok(Box::new(Term::NumInt(1))));
    assert_eq!(typechecker::typecheck_term(&one.unwrap(), &mut Vec::new(), &mut Vec::new()), Ok(Type::Base(BaseType::Int)));

    let one = TermParser::new().parse("(((1)))");
    assert_eq!(one, Ok(Box::new(Term::NumInt(1))));

    let one_plus_one = TermParser::new().parse("1 + 1");
    assert_eq!(one_plus_one,
        Ok(Box::new(Term::Plus(Box::new(Term::NumInt(1)), Box::new(Term::NumInt(1)))))
    );

    let t = TermParser::new().parse("( 2 * 2 ) + 5");
    assert!(t.is_ok());

    let pair = TermParser::new().parse("1, 2");
    assert_eq!(pair, Ok(Box::new(Term::Pair(Box::new(Term::NumInt(1)), Box::new(Term::NumInt(2))))));
    assert_eq!(typechecker::typecheck_term(&pair.unwrap(), &mut Vec::new(), &mut Vec::new()), Ok(Type::Prod(Box::new(Type::Base(BaseType::Int)), Box::new(Type::Base(BaseType::Int)))));
    
    let pair = TermParser::new().parse("(1, 2)");
    assert_eq!(pair, Ok(Box::new(Term::Pair(Box::new(Term::NumInt(1)), Box::new(Term::NumInt(2))))));
    assert_eq!(typechecker::typecheck_term(&pair.unwrap(), &mut Vec::new(), &mut Vec::new()), Ok(Type::Prod(Box::new(Type::Base(BaseType::Int)), Box::new(Type::Base(BaseType::Int)))));

    let clam = TermParser::new().parse("ar x: Int ~~> { return x }");
    assert_eq!(clam, Ok(Box::new(Term::CLam(VarWithType::VT(VarProd::V("x".to_string()), Type::Base(BaseType::Int)), Box::new(Command::Return(VTR::T(Box::new(Term::Var(Var::V("x".to_string()))))))))));
    assert_eq!(typechecker::typecheck_term(&clam.unwrap(), &mut Vec::new(), &mut Vec::new()),
        Ok(Type::Arr(Box::new(Type::Base(BaseType::Int)), Box::new(Type::Base(BaseType::Int)))));

    let lam = TermParser::new().parse("fn x : Int --> { x }");
    assert_eq!(lam, Ok(Box::new(Term::Lam(VarWithType::VT(VarProd::V("x".to_string()), Type::Base(BaseType::Int)), Box::new(Term::Var(Var::V("x".to_string())))))));
    assert_eq!(typechecker::typecheck_term(&lam.unwrap(), &mut Vec::new(), &mut Vec::new()),
        Ok(Type::Fun(Box::new(Type::Base(BaseType::Int)), Box::new(Type::Base(BaseType::Int)))));

    let ty_int_int = Type::Prod(Box::new(Type::Base(BaseType::Int)), Box::new(Type::Base(BaseType::Int)));
    let lam = TermParser::new().parse("fn x : (Int * Int) --> { x }");
    assert_eq!(lam, Ok(Box::new(Term::Lam(VarWithType::VT(VarProd::V("x".to_string()), ty_int_int.clone()), Box::new(Term::Var(Var::V("x".to_string())))))));
    assert_eq!(typechecker::typecheck_term(&lam.unwrap(), &mut Vec::new(), &mut Vec::new()),
        Ok(Type::Fun(
            Box::new(ty_int_int.clone()),
            Box::new(ty_int_int.clone()))));

    let app = TermParser::new().parse("fn z : Int --> { (fn x : Int --> { x }) z }");
    assert_eq!(app, Ok(Box::new(Term::Lam(VarWithType::VT(VarProd::V("z".to_string()), Type::Base(BaseType::Int)), Box::new(Term::App(Box::new(Term::Lam(VarWithType::VT(VarProd::V("x".to_string()), Type::Base(BaseType::Int)), Box::new(Term::Var(Var::V("x".to_string()))))), Box::new(Term::Var(Var::V("z".to_string())))))))));
    assert_eq!(typechecker::typecheck_term(&app.unwrap(), &mut Vec::new(), &mut Vec::new()),
        Ok(Type::Fun(Box::new(Type::Base(BaseType::Int)), Box::new(Type::Base(BaseType::Int)))));

    let iseq = TermParser::new().parse("
        if (3 == 2) then 1 else 2
        "
    );
    assert!(iseq.is_ok());
    assert_eq!(typechecker::typecheck_term(&iseq.unwrap(), &mut Vec::new(), &mut Vec::new()),
        Ok(Type::Base(BaseType::Int))
    );


    let nn = TermParser::new().parse(
        "ar w : Mat ~~> {handle
            let x : Vec <~ Input () in
            let z1 : Vec <~ Leyer1 x in
            let z2 : Vec <~ Leyer2 z1 in
            let z3 : Vec <~ Leyer3 z2 in
            return z3
        with {
            return y : Vec => {
                return y
            }
            Leyer1 k : (Vec ~> Vec) ; z : Vec => {
                k @ w #> z
            }
        }}
        "
    );
    assert!(nn.is_ok());
    // println!("{:?}", typechecker::typecheck_term(&nn.unwrap(), &mut Vec::new(), &mut Vec::new()));
}

#[test]
fn test_arrowml_command() {
    use crate::parser::CommandParser;
    use crate::ast::{VTR, Term, Type, Command, BaseType};

    let ret = CommandParser::new().parse("return 1");
    assert_eq!(ret, Ok(Box::new(Command::Return(VTR::T(Box::new(Term::NumInt(1)))))));

    let c = CommandParser::new().parse(
        "let x : Int <~ return (let x : Int = 1 in x + 2) in return x"
    );
    // println!("{:?}", c);
    assert!(c.is_ok());

    let c = CommandParser::new().parse(
        "let x, y : Int * Int <~ return (1, 2) in return x + y"
    );
    println!("{:?}", c);
    assert!(c.is_ok());

    let c = CommandParser::new().parse(
        "let x : Int <~ a @ v in return x"
    );
    assert!(c.is_ok());

    let hand = CommandParser::new().parse(
        "handle return 1 with {
            return x : Int =>{
                return 2
            }
        }"
    );
    assert_eq!(
        typechecker::typecheck_command(& hand.unwrap(), &mut Vec::new(), &mut Vec::new(), & Vec::new()),
        Ok(Type::Base(BaseType::Int))
    );

    let nn = CommandParser::new().parse(
        "handle
            let x : Vec <~ Input u in
            return x
        with {
            return y : Vec => {
                return y
            }
        }
        "
    );
    assert!(nn.is_ok());

    let c = CommandParser::new().parse(
        "let x : Int <~ handle return 1 with {
            return x : Int => {
                return 2
            }
        } in return x"
    );
    // println!("{:?}", c);
    assert!(c.is_ok());
    
    let c = CommandParser::new().parse(
        "let x : Int <~ let y : Int <~ return 1 in return 1 in return x"
    );
    // println!("{:?}", c);
    assert!(c.is_ok());

}

#[test]
fn test_arrowml_handler() {
    use crate::parser::HandlerParser;
    use crate::ast::{VTR, Term, Type, Command, BaseType, VarWithType, Var, Handler, HandlerRet, VarProd};

    let ret_only =
        HandlerParser::new().parse("return x : Int => { return x }");
    assert_eq!(ret_only, Ok(Handler::H(
        HandlerRet::HRet(
            VarWithType::VT(VarProd::V("x".to_string()), Type::Base(BaseType::Int)),
            Box::new(Command::Return(VTR::T(Box::new(Term::Var(Var::V("x".to_string()))))))),
        Vec::new())));
    assert_eq!(typechecker::typecheck_handler(&ret_only.unwrap(), &mut Vec::new(), & Vec::new()),
        Ok((Type::Base(BaseType::Int), Type::Base(BaseType::Int))));

    let h_op =
        HandlerParser::new().parse(
            "return x : UInt => { return (10 + 1) }  Op k : (Int ~> Int) ; z : UInt => { k @ 5 }"
        );
    assert!(h_op.is_ok());
}

#[test]
fn test_neural_network_example() {
    let eff = parser::EffectDeclsParser::new().parse(
        "Input : Unit ~> Vec
        | Layer1 : Vec ~> Vec
        | Layer2 : Vec ~> Vec
        | Layer3 : Vec ~> Vec
        "
    );
    println!("{:?}", eff);
}
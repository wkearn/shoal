use crate::error;
use crate::types::{self, Type, TypeScheme};
use std::collections::HashSet;

fn initialize_types() -> (types::TypeSubstitution,types::TypeEnv) {
    // Initialize the standard library
    let mut sub = types::TypeSubstitution::new();
    let mut env = types::TypeEnv::new();

    let Type::TypeVar(t1,ops) = sub.genvar_with_ops(Some("+".into())) else { unreachable!() };
    let mut hs1 = HashSet::new();
    hs1.insert(t1.clone());
    env.insert(
        "+".into(),
        TypeScheme::QuantifiedType(
            hs1,
            Type::BinaryFunction(
                Box::new(Type::TypeVar(t1.clone(), ops.clone())),
                Box::new(Type::TypeVar(t1.clone(), ops.clone())),
                Box::new(Type::TypeVar(t1.clone(), ops.clone())),
            ),
        ),
    );

    let Type::TypeVar(t2,ops) = sub.genvar_with_ops(Some("-".into())) else { unreachable!() };
    let mut hs2 = HashSet::new();
    hs2.insert(t2.clone());
    env.insert(
        "-".into(),
        TypeScheme::QuantifiedType(
            hs2,
            Type::BinaryFunction(
                Box::new(Type::TypeVar(t2.clone(), ops.clone())),
                Box::new(Type::TypeVar(t2.clone(), ops.clone())),
                Box::new(Type::TypeVar(t2.clone(), ops.clone())),
            ),
        ),
    );

    let Type::TypeVar(t3,ops) = sub.genvar_with_ops(Some("max".into())) else { unreachable!() };
    let mut hs3 = HashSet::new();
    hs3.insert(t3.clone());
    env.insert(
        "max".into(),
        TypeScheme::QuantifiedType(
            hs3,
            Type::BinaryFunction(
                Box::new(Type::TypeVar(t3.clone(), ops.clone())),
                Box::new(Type::TypeVar(t3.clone(), ops.clone())),
                Box::new(Type::TypeVar(t3.clone(), ops.clone())),
            ),
        ),
    );

    let Type::TypeVar(t4,ops) = sub.genvar_with_ops(Some("exp".into())) else { unreachable!() };
    let mut hs4 = HashSet::new();
    hs4.insert(t4.clone());
    env.insert(
        "exp".into(),
        TypeScheme::PlainType(Type::Function(
            Box::new(Type::TypeVar(t4.clone(), ops.clone())),
            Box::new(Type::TypeVar(t4.clone(), ops.clone())),
        )),
    );

    let ps1: Vec<Box<str>> = vec!["Integer".into(), "Float32".into(), "Float64".into()];
    sub.insert_overload("+".into(), ps1);

    let ps2: Vec<Box<str>> = vec!["Integer".into(), "Float32".into(), "Float64".into()];
    sub.insert_overload("-".into(), ps2);

    let ps3: Vec<Box<str>> = vec!["Integer".into(), "Float32".into(), "Float64".into()];
    sub.insert_overload("max".into(), ps3);

    let ps4: Vec<Box<str>> = vec!["Float32".into(), "Float64".into()];
    sub.insert_overload("exp".into(), ps4);
    (sub,env)
}


#[cfg(test)]
mod test {
    use super::*;
    use crate::parser::{parse,sexpr::SExpr};

    #[test]
    fn test1() {
	let expr = parse(
            &"(let ((f (lambda (x) x))) (f 1.0))"
                .parse::<SExpr>()
                .unwrap(),
        )
            .unwrap();
	
	let (mut sub,env) = initialize_types();

	let t = sub.reconstruct(&expr, &env).unwrap();

	assert_eq!(t, Type::Float64);
    }

    #[test]
    fn test2() {
	let expr = parse(
            &"(let ((f (lambda (x) (+ x 2.0)))) (f 1.0))"
                .parse::<SExpr>()
                .unwrap(),
        )
            .unwrap();
	
	let (mut sub,env) = initialize_types();

	let t = sub.reconstruct(&expr, &env).unwrap();

	assert_eq!(t, Type::Float64);

	//
	let expr = parse(
            &"(let ((f (lambda (x) (+ x 2)))) (f 1))"
                .parse::<SExpr>()
                .unwrap(),
        )
            .unwrap();
	
	let (mut sub,env) = initialize_types();

	let t = sub.reconstruct(&expr, &env).unwrap();

	assert_eq!(t, Type::Integer);

	//
	let expr = parse(
            &"(let ((f (lambda (x y) (+ x y)))) (let ((a (f 1 2))) (let ((b (f 1.0 2.0))) b)))"
                .parse::<SExpr>()
                .unwrap(),
        )
            .unwrap();
	
	let (mut sub,env) = initialize_types();

	let t = sub.reconstruct(&expr, &env).unwrap();

	assert_eq!(t, Type::Float64);

	//
	let expr = parse(
            &"(let ((f (lambda (x y) (+ x y)))) (let ((a (f 1 2))) (let ((b (f true false))) b)))"
                .parse::<SExpr>()
                .unwrap(),
        )
            .unwrap();
	
	let (mut sub,env) = initialize_types();

	// This should throw a TypeError because Boolean is an invalid overloading of +
	sub.reconstruct(&expr, &env).unwrap_err();
    }
}

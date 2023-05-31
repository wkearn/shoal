use crate::error;
use crate::types::{self, Type, TypeScheme};
use std::collections::HashSet;

fn overload_binary_operator(sub: &mut types::TypeSubstitution, env: &mut types::TypeEnv,tv: &str, op: &str, ts: Vec<Box<str>>) {
    let t: Box<str> = tv.into();
    let ops: HashSet<Box<str>> = Some(op.into()).into_iter().collect();
    let mut hs = HashSet::new();
    hs.insert(t.clone());
    env.insert(
        op.into(),
        TypeScheme::QuantifiedType(
            hs,
            Type::BinaryFunction(
                Box::new(Type::TypeVar(t.clone(), ops.clone())),
                Box::new(Type::TypeVar(t.clone(), ops.clone())),
                Box::new(Type::TypeVar(t.clone(), ops.clone())),
            ),
        ),
    );

    sub.insert_overload(op.into(), ts);
}

fn overload_unary_operator(sub: &mut types::TypeSubstitution, env: &mut types::TypeEnv,tv: &str, op: &str, ts: Vec<Box<str>>) {
    let t: Box<str> = tv.into();
    let ops: HashSet<Box<str>> = Some(op.into()).into_iter().collect();
    let mut hs = HashSet::new();
    hs.insert(t.clone());
    env.insert(
        op.into(),
        TypeScheme::QuantifiedType(
            hs,
            Type::Function(
                Box::new(Type::TypeVar(t.clone(), ops.clone())),
                Box::new(Type::TypeVar(t.clone(), ops.clone())),
            ),
        ),
    );

    sub.insert_overload(op.into(), ts);
}

pub fn initialize_types() -> (types::TypeSubstitution,types::TypeEnv) {
    // Initialize the standard library
    let mut sub = types::TypeSubstitution::new();
    let mut env = types::TypeEnv::new();

    overload_binary_operator(&mut sub,&mut env,"a","+",vec!["Integer".into(), "Float32".into(), "Float64".into()]);
    overload_binary_operator(&mut sub,&mut env,"b","-",vec!["Integer".into(), "Float32".into(), "Float64".into()]);
    overload_binary_operator(&mut sub,&mut env,"c","max",vec!["Integer".into(), "Float32".into(), "Float64".into()]);
    overload_unary_operator(&mut sub,&mut env,"d","exp",vec!["Float32".into(), "Float64".into()]);

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

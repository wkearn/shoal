use crate::types::{self, Type, TypeScheme};
use std::collections::HashSet;

fn define_comparison_operator(
    sub: &mut types::TypeSubstitution,
    env: &mut types::TypeEnv,
    op: &str,
    ts: Vec<Box<str>>,
) {
    let t: Box<str> = "?S0".into();
    let ops: HashSet<Box<str>> = Some(op.into()).into_iter().collect();
    let mut hs = Vec::new();
    hs.push(Type::TypeVar(t.clone(), ops.clone()));
    env.insert(
        op.into(),
        TypeScheme::QuantifiedType(
            hs,
            Type::BinaryFunction(
                Box::new(Type::TypeVar(t.clone(), ops.clone())),
                Box::new(Type::TypeVar(t.clone(), ops.clone())),
                Box::new(Type::Boolean),
            ),
        ),
    );

    sub.insert_overload(op.into(), ts);
}

fn define_binary_operator(
    sub: &mut types::TypeSubstitution,
    env: &mut types::TypeEnv,
    op: &str,
    ts: Vec<Box<str>>,
) {
    let t: Box<str> = "?S0".into();
    let ops: HashSet<Box<str>> = Some(op.into()).into_iter().collect();
    let mut hs = Vec::new();
    hs.push(Type::TypeVar(t.clone(), ops.clone()));
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

fn define_unary_operator(
    sub: &mut types::TypeSubstitution,
    env: &mut types::TypeEnv,
    op: &str,
    ts: Vec<Box<str>>,
) {
    let t: Box<str> = "?S0".into();
    let ops: HashSet<Box<str>> = Some(op.into()).into_iter().collect();
    let mut hs = Vec::new();
    hs.push(Type::TypeVar(t.clone(), ops.clone()));
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

pub fn initialize_types() -> (types::TypeSubstitution, types::TypeEnv) {
    // Initialize the standard library
    let mut sub = types::TypeSubstitution::new();
    let mut env = types::TypeEnv::new();

    define_binary_operator(
        &mut sub,
        &mut env,
        "+",
        vec!["Integer".into(), "Float32".into(), "Float64".into()],
    );
    define_binary_operator(
        &mut sub,
        &mut env,
        "-",
        vec!["Integer".into(), "Float32".into(), "Float64".into()],
    );
    define_binary_operator(
        &mut sub,
        &mut env,
        "*",
        vec!["Integer".into(), "Float32".into(), "Float64".into()],
    );
    define_binary_operator(
        &mut sub,
        &mut env,
        "/",
        vec!["Float32".into(), "Float64".into()],
    );
    define_binary_operator(
        &mut sub,
        &mut env,
        "div",
        vec!["Integer".into()]
    );
    define_binary_operator(
        &mut sub,
        &mut env,
        "mod",
        vec!["Integer".into()]
    );
    define_binary_operator(
        &mut sub,
        &mut env,
        "max",
        vec!["Integer".into(), "Float32".into(), "Float64".into()],
    );
    define_binary_operator(
        &mut sub,
        &mut env,
        "min",
        vec!["Integer".into(), "Float32".into(), "Float64".into()],
    );
    define_unary_operator(
        &mut sub,
        &mut env,
        "exp",
        vec!["Float32".into(), "Float64".into()],
    );
    define_unary_operator(
        &mut sub,
        &mut env,
        "sin",
        vec!["Float32".into(), "Float64".into()],
    );
    define_unary_operator(
        &mut sub,
        &mut env,
        "cos",
        vec!["Float32".into(), "Float64".into()],
    );
    define_unary_operator(
        &mut sub,
        &mut env,
        "tan",
        vec!["Float32".into(), "Float64".into()],
    );
    define_unary_operator(
        &mut sub,
        &mut env,
        "log",
        vec!["Float32".into(), "Float64".into()],
    );
    define_comparison_operator(
        &mut sub,
        &mut env,
        ">",
        vec!["Integer".into(),"Float32".into(),"Float64".into()]
    );
    define_comparison_operator(
        &mut sub,
        &mut env,
        ">=",
        vec!["Integer".into(),"Float32".into(),"Float64".into()]
    );
    define_comparison_operator(
        &mut sub,
        &mut env,
        "<",
        vec!["Integer".into(),"Float32".into(),"Float64".into()]
    );
    define_comparison_operator(
        &mut sub,
        &mut env,
        "<=",
        vec!["Integer".into(),"Float32".into(),"Float64".into()]
    );
    define_comparison_operator(
        &mut sub,
        &mut env,
        "==",
        vec!["Boolean".into(),"Integer".into(),"Float32".into(),"Float64".into()]
    );
    define_comparison_operator(
        &mut sub,
        &mut env,
        "!=",
        vec!["Boolean".into(),"Integer".into(),"Float32".into(),"Float64".into()]
    );
    
    
    (sub, env)
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::parser::{parse, sexpr::SExpr};

    #[test]
    fn test1() {
        let expr = parse(
            &"(let ((f (lambda (x) x))) (f 1.0))"
                .parse::<SExpr>()
                .unwrap(),
        )
        .unwrap();

        let (mut sub, env) = initialize_types();

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

        let (mut sub, env) = initialize_types();

        let t = sub.reconstruct(&expr, &env).unwrap();

        assert_eq!(t, Type::Float64);

        //
        let expr = parse(
            &"(let ((f (lambda (x) (+ x 2)))) (f 1))"
                .parse::<SExpr>()
                .unwrap(),
        )
        .unwrap();

        let (mut sub, env) = initialize_types();

        let t = sub.reconstruct(&expr, &env).unwrap();

        assert_eq!(t, Type::Integer);

        //
        let expr = parse(
            &"(let ((f (lambda (x y) (+ x y)))) (let ((a (f 1 2))) (let ((b (f 1.0 2.0))) b)))"
                .parse::<SExpr>()
                .unwrap(),
        )
        .unwrap();

        let (mut sub, env) = initialize_types();

        let t = sub.reconstruct(&expr, &env).unwrap();

        assert_eq!(t, Type::Float64);

        //
        let expr = parse(
            &"(let ((f (lambda (x y) (+ x y)))) (let ((a (f 1 2))) (let ((b (f true false))) b)))"
                .parse::<SExpr>()
                .unwrap(),
        )
        .unwrap();

        let (mut sub, env) = initialize_types();

        // This should throw a TypeError because Boolean is an invalid overloading of +
        let crate::error::Error::TypeError(e) = sub
	    .reconstruct(&expr, &env)
	    .unwrap_err()
	else { panic!("Encountered unexpected error type") };
    }

    #[test]
    fn comparison_test() {	
        let expr = parse(
            &"
(let ((p1 (lambda (u v) (< u v))))
  (let ((p2 (lambda (u v) (<= u v))))
    (let ((p3 (lambda (u v) (> u v))))
      (let ((p4 (lambda (u v) (>= u v))))
	(let ((p5 (lambda (u v) (== u v))))
	  (let ((p6 (lambda (u v) (!= u v))))
	    (if (p1 1.0 2.0)
		(if (p1 1 2)
		    (p2 1.0 2.0)
		    (p2 1.0 2.0))
		(if (p2 1 2)
		    (p3 1.0 2.0)
		    (if (p3 1 2)
			(if (p4 1.0 2.0)
			    (p4 1 2)
			    (if (p5 1.0 2.0)
				(p5 1 2)
				(if (p5 true false)
				    (p6 1.0 2.0)
				    (if (p6 1 2)
					(p6 true false)
					true))))
			true)))))))))"
                .parse::<SExpr>()
                .unwrap(),
        )
        .unwrap();

        let (mut sub, env) = initialize_types();

        let t = sub.reconstruct(&expr, &env).unwrap();

        assert_eq!(t, Type::Boolean);
    }
}

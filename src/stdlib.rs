use crate::interpreter::{
    primitives::{PrimitiveBinaryOp, PrimitiveUnaryOp},
    Env, PrimitiveTable, Value,
};
use crate::types::{self, Type, TypeScheme};

pub mod comparisons;
pub mod numeric;

fn define_comparison_operator(
    sub: &mut types::TypeSubstitution,
    type_env: &mut types::TypeEnv,
    env: &mut Env,
    prims: &mut PrimitiveTable,
    prim_op: impl PrimitiveBinaryOp + 'static,
    op: &str,
    ts: Vec<Box<str>>,
) {
    let t = 0;
    let ops: Vec<Box<str>> = Some(op.into()).into_iter().collect();
    let mut hs = Vec::new();
    hs.push(Type::TypeVar(t, ops.clone()));
    type_env.insert(
        op.into(),
        TypeScheme::QuantifiedType(
            hs,
            Type::BinaryFunction(
                Box::new(Type::TypeVar(t, ops.clone())),
                Box::new(Type::TypeVar(t, ops.clone())),
                Box::new(Type::Boolean),
            ),
        ),
    );

    sub.insert_overload(op.into(), ts);

    env.insert(op.into(), Value::PrimitiveFunction(op.into()));
    prims.insert(op.into(), prim_op);
}

fn define_binary_operator(
    sub: &mut types::TypeSubstitution,
    type_env: &mut types::TypeEnv,
    env: &mut Env,
    prims: &mut PrimitiveTable,
    prim_op: impl PrimitiveBinaryOp + 'static,
    op: &str,
    ts: Vec<Box<str>>,
) {
    let t = 0;
    let ops: Vec<Box<str>> = Some(op.into()).into_iter().collect();
    let mut hs = Vec::new();
    hs.push(Type::TypeVar(t, ops.clone()));
    type_env.insert(
        op.into(),
        TypeScheme::QuantifiedType(
            hs,
            Type::BinaryFunction(
                Box::new(Type::TypeVar(t, ops.clone())),
                Box::new(Type::TypeVar(t, ops.clone())),
                Box::new(Type::TypeVar(t, ops.clone())),
            ),
        ),
    );

    sub.insert_overload(op.into(), ts);

    env.insert(op.into(), Value::PrimitiveFunction(op.into()));
    prims.insert(op.into(), prim_op);
}

fn define_unary_operator(
    sub: &mut types::TypeSubstitution,
    type_env: &mut types::TypeEnv,
    env: &mut Env,
    prims: &mut PrimitiveTable,
    prim_op: impl PrimitiveUnaryOp + 'static,
    op: &str,
    ts: Vec<Box<str>>,
) {
    let t = 0;
    let ops: Vec<Box<str>> = Some(op.into()).into_iter().collect();
    let mut hs = Vec::new();
    hs.push(Type::TypeVar(t, ops.clone()));
    type_env.insert(
        op.into(),
        TypeScheme::QuantifiedType(
            hs,
            Type::Function(
                Box::new(Type::TypeVar(t, ops.clone())),
                Box::new(Type::TypeVar(t, ops.clone())),
            ),
        ),
    );

    sub.insert_overload(op.into(), ts);

    env.insert(op.into(), Value::PrimitiveFunction(op.into()));
    prims.insert(op.into(), prim_op);
}

pub fn initialize() -> (types::TypeSubstitution, types::TypeEnv, Env, PrimitiveTable) {
    // Initialize the standard library
    let mut sub = types::TypeSubstitution::new();
    let mut type_env = types::TypeEnv::new();
    let mut env = Env::new();
    let mut prims = PrimitiveTable::new();

    define_binary_operator(
        &mut sub,
        &mut type_env,
        &mut env,
        &mut prims,
        numeric::Add,
        "+",
        vec!["Integer".into(), "Float32".into(), "Float64".into()],
    );
    define_binary_operator(
        &mut sub,
        &mut type_env,
        &mut env,
        &mut prims,
        numeric::Sub,
        "-",
        vec!["Integer".into(), "Float32".into(), "Float64".into()],
    );
    define_binary_operator(
        &mut sub,
        &mut type_env,
        &mut env,
        &mut prims,
        numeric::Mul,
        "*",
        vec!["Integer".into(), "Float32".into(), "Float64".into()],
    );
    define_binary_operator(
        &mut sub,
        &mut type_env,
        &mut env,
        &mut prims,
        numeric::Div,
        "/",
        vec!["Float32".into(), "Float64".into()],
    );
    define_binary_operator(
        &mut sub,
        &mut type_env,
        &mut env,
        &mut prims,
        numeric::IDiv,
        "div",
        vec!["Integer".into()],
    );
    define_binary_operator(
        &mut sub,
        &mut type_env,
        &mut env,
        &mut prims,
        numeric::Mod,
        "mod",
        vec!["Integer".into()],
    );
    define_binary_operator(
        &mut sub,
        &mut type_env,
        &mut env,
        &mut prims,
        numeric::Max,
        "max",
        vec!["Integer".into(), "Float32".into(), "Float64".into()],
    );
    define_binary_operator(
        &mut sub,
        &mut type_env,
        &mut env,
        &mut prims,
        numeric::Min,
        "min",
        vec!["Integer".into(), "Float32".into(), "Float64".into()],
    );
    define_unary_operator(
        &mut sub,
        &mut type_env,
        &mut env,
        &mut prims,
        numeric::Exp,
        "exp",
        vec!["Float32".into(), "Float64".into()],
    );
    define_unary_operator(
        &mut sub,
        &mut type_env,
        &mut env,
        &mut prims,
        numeric::Sin,
        "sin",
        vec!["Float32".into(), "Float64".into()],
    );
    define_unary_operator(
        &mut sub,
        &mut type_env,
        &mut env,
        &mut prims,
        numeric::Cos,
        "cos",
        vec!["Float32".into(), "Float64".into()],
    );
    define_unary_operator(
        &mut sub,
        &mut type_env,
        &mut env,
        &mut prims,
        numeric::Tan,
        "tan",
        vec!["Float32".into(), "Float64".into()],
    );
    define_unary_operator(
        &mut sub,
        &mut type_env,
        &mut env,
        &mut prims,
        numeric::Log,
        "log",
        vec!["Float32".into(), "Float64".into()],
    );
    define_comparison_operator(
        &mut sub,
        &mut type_env,
        &mut env,
        &mut prims,
        comparisons::GreaterThan,
        ">",
        vec!["Integer".into(), "Float32".into(), "Float64".into()],
    );
    define_comparison_operator(
        &mut sub,
        &mut type_env,
        &mut env,
        &mut prims,
        comparisons::GreaterThanOrEqual,
        ">=",
        vec!["Integer".into(), "Float32".into(), "Float64".into()],
    );
    define_comparison_operator(
        &mut sub,
        &mut type_env,
        &mut env,
        &mut prims,
        comparisons::LessThan,
        "<",
        vec!["Integer".into(), "Float32".into(), "Float64".into()],
    );
    define_comparison_operator(
        &mut sub,
        &mut type_env,
        &mut env,
        &mut prims,
        comparisons::LessThanOrEqual,
        "<=",
        vec!["Integer".into(), "Float32".into(), "Float64".into()],
    );
    define_comparison_operator(
        &mut sub,
        &mut type_env,
        &mut env,
        &mut prims,
        comparisons::Equal,
        "==",
        vec![
            "Boolean".into(),
            "Integer".into(),
            "Float32".into(),
            "Float64".into(),
        ],
    );
    define_comparison_operator(
        &mut sub,
        &mut type_env,
        &mut env,
        &mut prims,
        comparisons::NotEqual,
        "!=",
        vec![
            "Boolean".into(),
            "Integer".into(),
            "Float32".into(),
            "Float64".into(),
        ],
    );

    (sub, type_env, env, prims)
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::parser::{sexpr::parser::SExpr, Expr};

    #[test]
    fn test1() {
        let expr = Expr::parse(
            &"(let ((f (lambda (x) x))) (f 1.0))"
                .parse::<SExpr>()
                .unwrap(),
        )
        .unwrap();

        let (mut sub, env, _, _) = initialize();

        let t = sub.reconstruct(&expr, &env).unwrap();

        assert_eq!(t.tag(), &Type::Float64);
    }

    #[test]
    fn test2() {
        let expr = Expr::parse(
            &"(let ((f (lambda (x) (+ x 2.0)))) (f 1.0))"
                .parse::<SExpr>()
                .unwrap(),
        )
        .unwrap();

        let (mut sub, env, _, _) = initialize();

        let t = sub.reconstruct(&expr, &env).unwrap();

        assert_eq!(t.tag(), &Type::Float64);

        //
        let expr = Expr::parse(
            &"(let ((f (lambda (x) (+ x 2)))) (f 1))"
                .parse::<SExpr>()
                .unwrap(),
        )
        .unwrap();

        let (mut sub, env, _, _) = initialize();

        let t = sub.reconstruct(&expr, &env).unwrap();

        assert_eq!(t.tag(), &Type::Integer);

        //
        let expr = Expr::parse(
            &"(let ((f (lambda (x y) (+ x y)))) (let ((a (f 1 2))) (let ((b (f 1.0 2.0))) b)))"
                .parse::<SExpr>()
                .unwrap(),
        )
        .unwrap();

        let (mut sub, env, _, _) = initialize();

        let t = sub.reconstruct(&expr, &env).unwrap();

        assert_eq!(t.tag(), &Type::Float64);

        //
        let expr = Expr::parse(
            &"(let ((f (lambda (x y) (+ x y)))) (let ((a (f 1 2))) (let ((b (f true false))) b)))"
                .parse::<SExpr>()
                .unwrap(),
        )
        .unwrap();

        let (mut sub, env, _, _) = initialize();

        // This should throw a TypeError because Boolean is an invalid overloading of +
        let crate::error::Error::TypeError(_) = sub
	    .reconstruct(&expr, &env)
	    .unwrap_err()
	else { panic!("Encountered unexpected error type") };
    }

    #[test]
    fn comparison_test() {
        let expr = Expr::parse(
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

        let (mut sub, env, _, _) = initialize();

        let t = sub.reconstruct(&expr, &env).unwrap();

        assert_eq!(t.tag(), &Type::Boolean);
    }
}

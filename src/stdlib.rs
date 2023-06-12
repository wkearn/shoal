use crate::interpreter::{
    primitives::{PrimitiveBinaryOp, PrimitiveUnaryOp},
    Env, PrimitiveTable, Value,
};
use crate::parser::Expr;
use crate::types::{self, Type, TypeScheme};

pub mod comparisons;
pub mod numeric;

fn define_comparison_operator(
    sub: &mut types::TypeSubstitution,
    type_env: &mut types::TypeEnv,
    overloading_env: &mut types::OverloadingEnv,
    env: &mut Env,
    prims: &mut PrimitiveTable,
    prim_op: impl PrimitiveBinaryOp + 'static,
    op: &str,
    ts: Vec<Box<str>>,
    imps: Vec<Expr<Type>>,
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

    overloading_env.insert(op.into(), imps);

    env.insert(op.into(), Value::PrimitiveFunction(op.into()));
    prims.insert(op.into(), prim_op);
}

fn define_binary_operator(
    sub: &mut types::TypeSubstitution,
    type_env: &mut types::TypeEnv,
    overloading_env: &mut types::OverloadingEnv,
    env: &mut Env,
    prims: &mut PrimitiveTable,
    prim_op: impl PrimitiveBinaryOp + 'static,
    op: &str,
    ts: Vec<Box<str>>,
    imps: Vec<Expr<Type>>,
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

    overloading_env.insert(op.into(), imps);

    env.insert(op.into(), Value::PrimitiveFunction(op.into()));
    prims.insert(op.into(), prim_op);
}

fn define_unary_operator(
    sub: &mut types::TypeSubstitution,
    type_env: &mut types::TypeEnv,
    overloading_env: &mut types::OverloadingEnv,
    env: &mut Env,
    prims: &mut PrimitiveTable,
    prim_op: impl PrimitiveUnaryOp + 'static,
    op: &str,
    ts: Vec<Box<str>>,
    imps: Vec<Expr<Type>>,
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

    overloading_env.insert(op.into(), imps);

    env.insert(op.into(), Value::PrimitiveFunction(op.into()));
    prims.insert(op.into(), prim_op);
}

pub fn initialize() -> (
    types::TypeSubstitution,
    types::TypeEnv,
    types::OverloadingEnv,
    Env,
    PrimitiveTable,
) {
    // Initialize the standard library
    let mut sub = types::TypeSubstitution::new();
    let mut type_env = types::TypeEnv::new();
    let mut overloading_env = types::OverloadingEnv::new(std::collections::HashMap::new());
    let mut env = Env::new();
    let mut prims = PrimitiveTable::new();

    define_binary_operator(
        &mut sub,
        &mut type_env,
        &mut overloading_env,
        &mut env,
        &mut prims,
        numeric::Add,
        "+",
        vec!["Integer".into(), "Float32".into(), "Float64".into()],
        vec![
            Expr::Identifier(
                Type::BinaryFunction(
                    Box::new(Type::Integer),
                    Box::new(Type::Integer),
                    Box::new(Type::Integer),
                ),
                "iplus".into(),
            ),
            Expr::Identifier(
                Type::BinaryFunction(
                    Box::new(Type::Float32),
                    Box::new(Type::Float32),
                    Box::new(Type::Float32),
                ),
                "fplus".into(),
            ),
            Expr::Identifier(
                Type::BinaryFunction(
                    Box::new(Type::Float64),
                    Box::new(Type::Float64),
                    Box::new(Type::Float64),
                ),
                "dplus".into(),
            ),
        ],
    );
    define_binary_operator(
        &mut sub,
        &mut type_env,
        &mut overloading_env,
        &mut env,
        &mut prims,
        numeric::Sub,
        "-",
        vec!["Integer".into(), "Float32".into(), "Float64".into()],
        vec![
            Expr::Identifier(
                Type::BinaryFunction(
                    Box::new(Type::Integer),
                    Box::new(Type::Integer),
                    Box::new(Type::Integer),
                ),
                "iminus".into(),
            ),
            Expr::Identifier(
                Type::BinaryFunction(
                    Box::new(Type::Float32),
                    Box::new(Type::Float32),
                    Box::new(Type::Float32),
                ),
                "fminus".into(),
            ),
            Expr::Identifier(
                Type::BinaryFunction(
                    Box::new(Type::Float64),
                    Box::new(Type::Float64),
                    Box::new(Type::Float64),
                ),
                "dminus".into(),
            ),
        ],
    );
    define_binary_operator(
        &mut sub,
        &mut type_env,
        &mut overloading_env,
        &mut env,
        &mut prims,
        numeric::Mul,
        "*",
        vec!["Integer".into(), "Float32".into(), "Float64".into()],
        vec![
            Expr::Identifier(
                Type::BinaryFunction(
                    Box::new(Type::Integer),
                    Box::new(Type::Integer),
                    Box::new(Type::Integer),
                ),
                "imul".into(),
            ),
            Expr::Identifier(
                Type::BinaryFunction(
                    Box::new(Type::Float32),
                    Box::new(Type::Float32),
                    Box::new(Type::Float32),
                ),
                "fmul".into(),
            ),
            Expr::Identifier(
                Type::BinaryFunction(
                    Box::new(Type::Float64),
                    Box::new(Type::Float64),
                    Box::new(Type::Float64),
                ),
                "dmul".into(),
            ),
        ],
    );
    define_binary_operator(
        &mut sub,
        &mut type_env,
        &mut overloading_env,
        &mut env,
        &mut prims,
        numeric::Div,
        "/",
        vec!["Float32".into(), "Float64".into()],
        vec![
            Expr::Identifier(
                Type::BinaryFunction(
                    Box::new(Type::Float32),
                    Box::new(Type::Float32),
                    Box::new(Type::Float32),
                ),
                "fdiv".into(),
            ),
            Expr::Identifier(
                Type::BinaryFunction(
                    Box::new(Type::Float64),
                    Box::new(Type::Float64),
                    Box::new(Type::Float64),
                ),
                "ddiv".into(),
            ),
        ],
    );
    define_binary_operator(
        &mut sub,
        &mut type_env,
        &mut overloading_env,
        &mut env,
        &mut prims,
        numeric::IDiv,
        "div",
        vec!["Integer".into()],
        vec![Expr::Identifier(
            Type::BinaryFunction(
                Box::new(Type::Integer),
                Box::new(Type::Integer),
                Box::new(Type::Integer),
            ),
            "idiv".into(),
        )],
    );
    define_binary_operator(
        &mut sub,
        &mut type_env,
        &mut overloading_env,
        &mut env,
        &mut prims,
        numeric::Mod,
        "mod",
        vec!["Integer".into()],
        vec![Expr::Identifier(
            Type::BinaryFunction(
                Box::new(Type::Integer),
                Box::new(Type::Integer),
                Box::new(Type::Integer),
            ),
            "idiv".into(),
        )],
    );
    define_binary_operator(
        &mut sub,
        &mut type_env,
        &mut overloading_env,
        &mut env,
        &mut prims,
        numeric::Max,
        "max",
        vec!["Integer".into(), "Float32".into(), "Float64".into()],
        vec![
            Expr::Identifier(
                Type::BinaryFunction(
                    Box::new(Type::Integer),
                    Box::new(Type::Integer),
                    Box::new(Type::Integer),
                ),
                "imax".into(),
            ),
            Expr::Identifier(
                Type::BinaryFunction(
                    Box::new(Type::Float32),
                    Box::new(Type::Float32),
                    Box::new(Type::Float32),
                ),
                "fmax".into(),
            ),
            Expr::Identifier(
                Type::BinaryFunction(
                    Box::new(Type::Float64),
                    Box::new(Type::Float64),
                    Box::new(Type::Float64),
                ),
                "dmax".into(),
            ),
        ],
    );
    define_binary_operator(
        &mut sub,
        &mut type_env,
        &mut overloading_env,
        &mut env,
        &mut prims,
        numeric::Min,
        "min",
        vec!["Integer".into(), "Float32".into(), "Float64".into()],
        vec![
            Expr::Identifier(
                Type::BinaryFunction(
                    Box::new(Type::Integer),
                    Box::new(Type::Integer),
                    Box::new(Type::Integer),
                ),
                "imin".into(),
            ),
            Expr::Identifier(
                Type::BinaryFunction(
                    Box::new(Type::Float32),
                    Box::new(Type::Float32),
                    Box::new(Type::Float32),
                ),
                "fmin".into(),
            ),
            Expr::Identifier(
                Type::BinaryFunction(
                    Box::new(Type::Float64),
                    Box::new(Type::Float64),
                    Box::new(Type::Float64),
                ),
                "dmin".into(),
            ),
        ],
    );
    define_unary_operator(
        &mut sub,
        &mut type_env,
        &mut overloading_env,
        &mut env,
        &mut prims,
        numeric::Exp,
        "exp",
        vec!["Float32".into(), "Float64".into()],
        vec![
            Expr::Identifier(
                Type::Function(Box::new(Type::Float32), Box::new(Type::Float32)),
                "fexp".into(),
            ),
            Expr::Identifier(
                Type::Function(Box::new(Type::Float64), Box::new(Type::Float64)),
                "dexp".into(),
            ),
        ],
    );
    define_unary_operator(
        &mut sub,
        &mut type_env,
        &mut overloading_env,
        &mut env,
        &mut prims,
        numeric::Sin,
        "sin",
        vec!["Float32".into(), "Float64".into()],
        vec![
            Expr::Identifier(
                Type::Function(Box::new(Type::Float32), Box::new(Type::Float32)),
                "fsin".into(),
            ),
            Expr::Identifier(
                Type::Function(Box::new(Type::Float64), Box::new(Type::Float64)),
                "dsin".into(),
            ),
        ],
    );
    define_unary_operator(
        &mut sub,
        &mut type_env,
        &mut overloading_env,
        &mut env,
        &mut prims,
        numeric::Cos,
        "cos",
        vec!["Float32".into(), "Float64".into()],
        vec![
            Expr::Identifier(
                Type::Function(Box::new(Type::Float32), Box::new(Type::Float32)),
                "fcos".into(),
            ),
            Expr::Identifier(
                Type::Function(Box::new(Type::Float64), Box::new(Type::Float64)),
                "dcos".into(),
            ),
        ],
    );
    define_unary_operator(
        &mut sub,
        &mut type_env,
        &mut overloading_env,
        &mut env,
        &mut prims,
        numeric::Tan,
        "tan",
        vec!["Float32".into(), "Float64".into()],
        vec![
            Expr::Identifier(
                Type::Function(Box::new(Type::Float32), Box::new(Type::Float32)),
                "ftan".into(),
            ),
            Expr::Identifier(
                Type::Function(Box::new(Type::Float64), Box::new(Type::Float64)),
                "dtan".into(),
            ),
        ],
    );
    define_unary_operator(
        &mut sub,
        &mut type_env,
        &mut overloading_env,
        &mut env,
        &mut prims,
        numeric::Log,
        "log",
        vec!["Float32".into(), "Float64".into()],
        vec![
            Expr::Identifier(
                Type::Function(Box::new(Type::Float32), Box::new(Type::Float32)),
                "flog".into(),
            ),
            Expr::Identifier(
                Type::Function(Box::new(Type::Float64), Box::new(Type::Float64)),
                "dlog".into(),
            ),
        ],
    );
    define_comparison_operator(
        &mut sub,
        &mut type_env,
        &mut overloading_env,
        &mut env,
        &mut prims,
        comparisons::GreaterThan,
        ">",
        vec!["Integer".into(), "Float32".into(), "Float64".into()],
        vec![
            Expr::Identifier(
                Type::BinaryFunction(
                    Box::new(Type::Integer),
                    Box::new(Type::Integer),
                    Box::new(Type::Boolean),
                ),
                "i>".into(),
            ),
            Expr::Identifier(
                Type::BinaryFunction(
                    Box::new(Type::Float32),
                    Box::new(Type::Float32),
                    Box::new(Type::Boolean),
                ),
                "f>".into(),
            ),
            Expr::Identifier(
                Type::BinaryFunction(
                    Box::new(Type::Float64),
                    Box::new(Type::Float64),
                    Box::new(Type::Boolean),
                ),
                "d>".into(),
            ),
        ],
    );
    define_comparison_operator(
        &mut sub,
        &mut type_env,
        &mut overloading_env,
        &mut env,
        &mut prims,
        comparisons::GreaterThanOrEqual,
        ">=",
        vec!["Integer".into(), "Float32".into(), "Float64".into()],
        vec![
            Expr::Identifier(
                Type::BinaryFunction(
                    Box::new(Type::Integer),
                    Box::new(Type::Integer),
                    Box::new(Type::Boolean),
                ),
                "i>=".into(),
            ),
            Expr::Identifier(
                Type::BinaryFunction(
                    Box::new(Type::Float32),
                    Box::new(Type::Float32),
                    Box::new(Type::Boolean),
                ),
                "f>=".into(),
            ),
            Expr::Identifier(
                Type::BinaryFunction(
                    Box::new(Type::Float64),
                    Box::new(Type::Float64),
                    Box::new(Type::Boolean),
                ),
                "d>=".into(),
            ),
        ],
    );
    define_comparison_operator(
        &mut sub,
        &mut type_env,
        &mut overloading_env,
        &mut env,
        &mut prims,
        comparisons::LessThan,
        "<",
        vec!["Integer".into(), "Float32".into(), "Float64".into()],
        vec![
            Expr::Identifier(
                Type::BinaryFunction(
                    Box::new(Type::Integer),
                    Box::new(Type::Integer),
                    Box::new(Type::Boolean),
                ),
                "i<".into(),
            ),
            Expr::Identifier(
                Type::BinaryFunction(
                    Box::new(Type::Float32),
                    Box::new(Type::Float32),
                    Box::new(Type::Boolean),
                ),
                "f<".into(),
            ),
            Expr::Identifier(
                Type::BinaryFunction(
                    Box::new(Type::Float64),
                    Box::new(Type::Float64),
                    Box::new(Type::Boolean),
                ),
                "d<".into(),
            ),
        ],
    );
    define_comparison_operator(
        &mut sub,
        &mut type_env,
        &mut overloading_env,
        &mut env,
        &mut prims,
        comparisons::LessThanOrEqual,
        "<=",
        vec!["Integer".into(), "Float32".into(), "Float64".into()],
        vec![
            Expr::Identifier(
                Type::BinaryFunction(
                    Box::new(Type::Integer),
                    Box::new(Type::Integer),
                    Box::new(Type::Boolean),
                ),
                "i<=".into(),
            ),
            Expr::Identifier(
                Type::BinaryFunction(
                    Box::new(Type::Float32),
                    Box::new(Type::Float32),
                    Box::new(Type::Boolean),
                ),
                "f<=".into(),
            ),
            Expr::Identifier(
                Type::BinaryFunction(
                    Box::new(Type::Float64),
                    Box::new(Type::Float64),
                    Box::new(Type::Boolean),
                ),
                "d<=".into(),
            ),
        ],
    );
    define_comparison_operator(
        &mut sub,
        &mut type_env,
        &mut overloading_env,
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
        vec![
            Expr::Identifier(
                Type::BinaryFunction(
                    Box::new(Type::Boolean),
                    Box::new(Type::Boolean),
                    Box::new(Type::Boolean),
                ),
                "b==".into(),
            ),
            Expr::Identifier(
                Type::BinaryFunction(
                    Box::new(Type::Integer),
                    Box::new(Type::Integer),
                    Box::new(Type::Boolean),
                ),
                "i==".into(),
            ),
            Expr::Identifier(
                Type::BinaryFunction(
                    Box::new(Type::Float32),
                    Box::new(Type::Float32),
                    Box::new(Type::Boolean),
                ),
                "f==".into(),
            ),
            Expr::Identifier(
                Type::BinaryFunction(
                    Box::new(Type::Float64),
                    Box::new(Type::Float64),
                    Box::new(Type::Boolean),
                ),
                "d==".into(),
            ),
        ],
    );
    define_comparison_operator(
        &mut sub,
        &mut type_env,
        &mut overloading_env,
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
        vec![
            Expr::Identifier(
                Type::BinaryFunction(
                    Box::new(Type::Boolean),
                    Box::new(Type::Boolean),
                    Box::new(Type::Boolean),
                ),
                "b==".into(),
            ),
            Expr::Identifier(
                Type::BinaryFunction(
                    Box::new(Type::Integer),
                    Box::new(Type::Integer),
                    Box::new(Type::Boolean),
                ),
                "i==".into(),
            ),
            Expr::Identifier(
                Type::BinaryFunction(
                    Box::new(Type::Float32),
                    Box::new(Type::Float32),
                    Box::new(Type::Boolean),
                ),
                "f==".into(),
            ),
            Expr::Identifier(
                Type::BinaryFunction(
                    Box::new(Type::Float64),
                    Box::new(Type::Float64),
                    Box::new(Type::Boolean),
                ),
                "d==".into(),
            ),
        ],
    );

    (sub, type_env, overloading_env, env, prims)
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::parser::{sexpr::parser::SExpr, Expr};
    use std::rc::Rc;

    #[test]
    fn test1() {
        let expr = Expr::parse(
            &"(let ((f (lambda (x) x))) (f 1.0))"
                .parse::<SExpr>()
                .unwrap(),
        )
        .unwrap();

        let (mut sub, env, _, _, _) = initialize();

        let t = sub.reconstruct(&expr, Rc::new(env)).unwrap();

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

        let (mut sub, env, _, _, _) = initialize();

        let t = sub.reconstruct(&expr, Rc::new(env)).unwrap();

        assert_eq!(t.tag(), &Type::Float64);

        //
        let expr = Expr::parse(
            &"(let ((f (lambda (x) (+ x 2)))) (f 1))"
                .parse::<SExpr>()
                .unwrap(),
        )
        .unwrap();

        let (mut sub, env, _, _, _) = initialize();

        let t = sub.reconstruct(&expr, Rc::new(env)).unwrap();

        assert_eq!(t.tag(), &Type::Integer);

        //
        let expr = Expr::parse(
            &"(let ((f (lambda (x y) (+ x y)))) (let ((a (f 1 2))) (let ((b (f 1.0 2.0))) b)))"
                .parse::<SExpr>()
                .unwrap(),
        )
        .unwrap();

        let (mut sub, env, _, _, _) = initialize();

        let t = sub.reconstruct(&expr, Rc::new(env)).unwrap();

        assert_eq!(t.tag(), &Type::Float64);

        //
        let expr = Expr::parse(
            &"(let ((f (lambda (x y) (+ x y)))) (let ((a (f 1 2))) (let ((b (f true false))) b)))"
                .parse::<SExpr>()
                .unwrap(),
        )
        .unwrap();

        let (mut sub, env, _, _, _) = initialize();

        // This should throw a TypeError because Boolean is an invalid overloading of +
        let crate::error::Error::TypeError(_) = sub
	    .reconstruct(&expr, Rc::new(env))
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

        let (mut sub, env, overloading_env, _, _) = initialize();

        let t = sub.reconstruct(&expr, Rc::new(env)).unwrap();

        assert_eq!(t.tag(), &Type::Boolean);
    }
}

pub mod alphatize;
pub mod anormalizer;

use crate::error::Error;
use crate::parser::{Expr, Program, Statement};
use crate::types::Type;

use std::collections::HashMap;
use std::rc::Rc;

fn let_desugaring<T>(prog: Program<T>) -> Result<Expr<T>, Error> {
    todo!()
}

pub fn compile<T>(prog: &Program<T>) -> Result<Program<T>, Error> {
    // Type inference and annotation
    let (mut sub, type_env, mut overloading_env, _, _) = crate::stdlib::initialize();
    let mut type_env = Rc::new(type_env);

    let mut vs: Vec<Statement<Type>> = Vec::new();

    for statement in prog.statements() {
        match statement {
            Statement::Expression(expr) => {
                let t = sub.reconstruct(&expr, type_env.clone())?;
                let t = sub.substitute(t);
                vs.push(Statement::Expression(t));
            }
            Statement::Definition(_, var, def) => {
                let t = sub.reconstruct(&def, type_env.clone())?;
                let t = sub.substitute(t);
                Rc::get_mut(&mut type_env)
                    .expect("type env has hanging references")
                    .insert(
                        var.clone(),
                        crate::types::TypeScheme::PlainType(t.tag().clone()),
                    );
                vs.push(Statement::Definition(t.tag().clone(), var.clone(), t));
            }
        }
    }
    let t = sub.reconstruct(prog.expression(), type_env.clone())?;
    let t = sub.substitute(t);
    vs.push(Statement::Expression(t));
    let typed_prog: Program<Type> = Program::new(vs)?;

    // Let desugaring
    let let_prog = let_desugaring(typed_prog)?;

    let resolved_prog = sub.resolve_overloading(&let_prog, &overloading_env)?;

    println!("Resolved prog {}", resolved_prog);

    // Alpha renaming
    let mut a1 = alphatize::Alphatizer::new();
    let renamed_prog = a1.alphatize(&resolved_prog, &HashMap::new());

    println!("Renamed prog {}", renamed_prog);

    // A-normalization
    let a2 = anormalizer::ANormalizer::new();
    let normalized_prog = a2.normalize_term(&renamed_prog);

    println!("{:?}", normalized_prog);

    Err(Error::CompileError(
        "Compiler pass not yet implemented".into(),
    ))
}

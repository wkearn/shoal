pub mod alphatize;
pub mod anormalizer;

use crate::error::Error;
use crate::parser::{Expr, Program, Statement};
use crate::types::{Type, TypeScheme};

use std::rc::Rc;

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
    let typed_prog: Program<Type> = Program::new(vs);

    let mut vs = Vec::new();
    // Overloading resolution
    for statement in typed_prog.statements() {
	match statement {
	    Statement::Expression(expr) => {
		let t = sub.resolve_overloading(expr,&overloading_env)?;
		vs.push(Statement::Expression(t));
	    }
	    Statement::Definition(_, var, def) => {
		if def.tag().is_overloaded() {
		    let new_def = sub.resolve_overloading(def,&overloading_env)?;
		    overloading_env.insert(var.clone(),vec![new_def.clone()]);
		    vs.push(Statement::Definition(new_def.tag().clone(),var.clone(),new_def));
		} else {
		    let new_def = sub.resolve_overloading(def,&overloading_env)?;
		    vs.push(Statement::Definition(new_def.tag().clone(),var.clone(),new_def));
		}
		
	    }
	}
    }
    let resolved_prog = Program::new(vs);

    println!("{:?}",resolved_prog);

    // Alpha renaming

    // A-normalization

    Err(Error::CompileError(
        "Compiler pass not yet implemented".into(),
    ))
}

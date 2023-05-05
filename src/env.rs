// Lexical scoping and closures

use crate::parser::Expr;

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

struct Env(Option<Rc<Scope>>);

// A scope owns a set of bindings and holds a reference counted
// pointer to its parent environment.
// The hash map needs to store Rc pointers, because the expressions
// might get shared around.
// The hash map also needs to be in a RefCell, because we may want to
// update the bindings from a child scope.
struct Scope {
    bindings: RefCell<HashMap<String, Rc<Expr>>>,
    parent: Env,
}

impl Scope {
    fn get(&self, k: &str) -> Option<Rc<Expr>> {
        let bs = self.bindings.borrow();
        match bs.get(k) {
            Some(expr) => Some(expr.clone()),
            None => None,
        }
    }
}

impl Env {
    fn get(&self, k: &str) -> Option<Rc<Expr>> {
        match &self.0 {
            Some(env) => env.get(k),
            None => None,
        }
    }
}

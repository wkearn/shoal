use std::rc::{Rc};
use std::cell::{RefCell,RefMut};
use std::collections::HashMap;

use crate::ast::Expr;

pub struct Env(Rc<Scope>);

impl Env {
    pub fn new(scope: Rc<Scope>) -> Self {
        Self(scope)
    }

    pub fn get(&self, k: &str) -> Option<Rc<Expr>> {
        self.0.get(k)
    }

    pub fn insert(&self, k: String, v: Rc<Expr>) {
        self.0.insert(k, v)
    }

    pub fn clone(&self) -> Self {
	Self(self.0.clone())
    }

    pub fn borrow_bindings(&self) -> RefMut<'_,HashMap<String,Rc<Expr>>> {
	self.0.bindings.borrow_mut()
    }
}

// A scope owns a set of bindings and holds a reference counted
// pointer to its parent environment.
// The hash map needs to store Rc pointers, because the expressions
// might get shared around.
// The hash map also needs to be in a RefCell, because we may want to
// update the bindings from a child scope.
pub struct Scope {
    bindings: RefCell<HashMap<String, Rc<Expr>>>,
    parent: Option<Env>,
}

impl Scope {
    pub fn new(bindings: RefCell<HashMap<String, Rc<Expr>>>, parent: Option<Env>) -> Self {
        Self { bindings, parent }
    }

    pub fn get(&self, k: &str) -> Option<Rc<Expr>> {
        match self.bindings.borrow().get(k) {
            Some(expr) => Some(expr.clone()),
            None => match &self.parent {
                Some(parent) => parent.get(k),
                None => None,
            },
        }
    }

    pub fn insert(&self, k: String, v: Rc<Expr>) {
        self.bindings.borrow_mut().insert(k, v);
    }
}

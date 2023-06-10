//! Union-find data structures for efficient unification

use crate::error::Error;
use crate::parser::Expr;

use std::cell::Cell;
use std::collections::HashMap;

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct TypeRef(usize);

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Type {
    Boolean,
    Integer,
    Float32,
    Float64,
    Variable(u8),
    Array(TypeRef),
    Pair(TypeRef, TypeRef),
    Function(TypeRef, TypeRef),
    BinaryFunction(TypeRef, TypeRef, TypeRef),
}

#[derive(Debug, Clone)]
pub enum TypeScheme {
    PlainType(TypeRef),
    QuantifiedType(Vec<TypeRef>, TypeRef),
}

#[derive(Debug, Default)]
pub struct TypeEnv(HashMap<Box<str>, TypeScheme>);

impl TypeEnv {
    pub fn new() -> Self {
        Self::default()
    }
}

pub struct UnionFind {
    fresh_vars: u8,
    data: Vec<Cell<TypeRef>>,
    ranks: Vec<u8>,
    table: HashMap<Type, TypeRef>,
    types: Vec<Type>,
}

impl UnionFind {
    pub fn new() -> Self {
        Self {
            fresh_vars: 0,
            data: Vec::new(),
            ranks: Vec::new(),
            table: HashMap::new(),
            types: Vec::new(),
        }
    }

    fn genvar(&mut self) -> TypeRef {
        self.fresh_vars += 1;
        self.insert(Type::Variable(self.fresh_vars))
    }

    pub fn pretty_print(&self, r: TypeRef) -> String {
        let root = self.get(self.find(r)); // A type
        match root {
            Type::Boolean => format!("Boolean"),
            Type::Integer => format!("Integer"),
            Type::Float32 => format!("Float32"),
	    Type::Float64 => format!("Float64"),
            Type::Variable(n) => format!("?X{}", n),
            Type::Array(arr) => format!("[{}]", self.pretty_print(*arr)),
            Type::Pair(p0, p1) => {
                format!("({},{})", self.pretty_print(*p0), self.pretty_print(*p1))
            }
            Type::Function(arg, body) => {
                format!(
                    "{} -> {}",
                    self.pretty_print(*arg),
                    self.pretty_print(*body)
                )
            }
            Type::BinaryFunction(arg0, arg1, body) => {
                format!(
                    "{} x {} -> {}",
                    self.pretty_print(*arg0),
                    self.pretty_print(*arg1),
                    self.pretty_print(*body)
                )
            }
        }
    }

    pub fn get(&self, r: TypeRef) -> &Type {
        &self.types[r.0]
    }

    pub fn get_root(&self, t: &Type) -> Option<TypeRef> {
        let r = self.table.get(&t)?;
        Some(self.find(*r))
    }

    pub fn insert(&mut self, t: Type) -> TypeRef {
        match self.table.get(&t) {
            Some(r) => *r,
            None => {
                let idx = self.data.len();

                assert_eq!(idx, self.ranks.len());
                assert_eq!(idx, self.types.len());
                assert_eq!(idx, self.table.len());

                self.data.push(Cell::new(TypeRef(idx)));
                self.ranks.push(0);
                self.table.insert(t.clone(), TypeRef(idx));
                self.types.push(t);

                TypeRef(idx)
            }
        }
    }

    pub fn find(&self, t: TypeRef) -> TypeRef {
        let mut element = t;
        let mut parent = self.parent(t);
        while parent != element {
            let grandparent = self.parent(parent);
            self.set_parent(element, grandparent);
            element = parent;
            parent = grandparent;
        }
        element
    }

    pub fn union(&mut self, t1: TypeRef, t2: TypeRef) {
        let x = self.find(t1);
        let y = self.find(t2);

        if x == y {
            // t1 and t2 are already in the same set
        } else {
            if let Type::Variable(_) = self.get(x) {
                self.set_parent(x, y);
            } else {
                let rankx = self.rank(x);
                let ranky = self.rank(y);

                if rankx < ranky {
                    self.set_parent(x, y);
                } else if rankx > ranky {
                    self.set_parent(y, x);
                } else {
                    self.increment_rank(x);
                    self.set_parent(y, x);
                }
            }
        }
    }

    fn set_parent(&self, t: TypeRef, new_parent: TypeRef) {
        self.data[t.0].set(new_parent);
    }

    fn parent(&self, t: TypeRef) -> TypeRef {
        self.data[t.0].get()
    }

    fn rank(&self, t: TypeRef) -> u8 {
        self.ranks[t.0]
    }

    fn increment_rank(&mut self, t: TypeRef) {
        self.ranks[t.0] = self.ranks[t.0].saturating_add(1);
    }

    pub fn unify_typerefs(&mut self, r1: TypeRef, r2: TypeRef) -> Result<(), Error> {
        let mut pairs = Vec::new();
        pairs.push((r1, r2));

        while let Some((x, y)) = pairs.pop() {
            let u = self.find(x);
            let v = self.find(y);

            if u == v {
            } else {
                match (self.get(u), self.get(v)) {
                    (Type::Boolean, Type::Boolean) => {}
                    (Type::Integer, Type::Integer) => {}
                    (Type::Float32, Type::Float32) => {}
		    (Type::Float64, Type::Float64) => {}
                    (Type::Array(arr0), Type::Array(arr1)) => {
                        pairs.push((*arr0, *arr1));
                        self.union(u, v);
                    }
                    (Type::Pair(p0, p1), Type::Pair(q0, q1)) => {
                        pairs.push((*p0, *q0));
                        pairs.push((*p1, *q1));
                        self.union(u, v);
                    }
                    (Type::Function(arg0, body0), Type::Function(arg1, body1)) => {
                        pairs.push((*arg0, *arg1));
                        pairs.push((*body0, *body1));
                        self.union(u, v);
                    }
                    (
                        Type::BinaryFunction(arg00, arg01, body0),
                        Type::BinaryFunction(arg10, arg11, body1),
                    ) => {
                        pairs.push((*arg00, *arg10));
                        pairs.push((*arg01, *arg11));
                        pairs.push((*body0, *body1));
                        self.union(u, v);
                    }
                    (Type::Variable(_), _) => {
                        // Doing it in this order makes it more likely that
                        // the concrete type becomes the parent
                        self.union(v, u)
                    }
                    (_, Type::Variable(_)) => pairs.push((v, u)),
                    (a, b) => return Err(Error::TypeError(format!("{:?} != {:?}", a, b))),
                }
            }
        }
        Ok(())
    }

    pub fn unify(&mut self, t1: Type, t2: Type) -> Result<(), Error> {
        let r1 = self.insert(t1);
        let r2 = self.insert(t2);

        self.unify_typerefs(r1, r2)
    }

    pub fn reconstruct<T>(
        &mut self,
        expr: &Expr<T>,
        env: &TypeEnv,
    ) -> Result<Expr<TypeRef>, Error> {
        match expr {
            Expr::BooleanLiteral(_, v) => {
                let r = self.insert(Type::Boolean);
                Ok(Expr::BooleanLiteral(r, *v))
            }
            Expr::IntegerLiteral(_, v) => {
                let r = self.insert(Type::Integer);
                Ok(Expr::IntegerLiteral(r, *v))
            }
            Expr::FloatLiteral(_, v) => {
                let r = self.insert(Type::Float64);
                Ok(Expr::FloatLiteral(r, *v))
            }
            Expr::Identifier(_, s) => {
                let x = env
                    .0
                    .get(s)
                    .ok_or(Error::UndefinedVariableError(format!("{s}")))?;
                match x {
                    TypeScheme::PlainType(t) => Ok(Expr::Identifier(t.clone(), s.clone())),
                    TypeScheme::QuantifiedType(vs, t) => {
                        // How do we do this in the union-find?
                        // We have to generate a new variable for
                        // each variable in vs. Then substitute
                        // those variables for the corresponding
                        // variables in t

                        let mut local_substitution: HashMap<TypeRef, TypeRef> = HashMap::new();
                        for v in vs {
                            // v is a &TypeRef, so just assume
                            // these are all Variables? They
                            // should be, since we can only
                            // create quantified types with
                            // Variables
                            let new_ref = self.genvar();
                            local_substitution.insert(*v, new_ref);
                        }

                        let tt = self.substitute(&local_substitution, *t);

                        Ok(Expr::Identifier(tt, s.clone()))
                    }
                }
            }
            Expr::Lambda(_, arg, body) => {
                let (arg_type, body_expr) = {
                    let mut local_env = TypeEnv::new();
                    local_env
                        .0
                        .extend(env.0.iter().map(|(k, v)| (k.clone(), v.clone())));

                    let arg_type = self.genvar();
                    local_env
                        .0
                        .insert(arg.clone(), TypeScheme::PlainType(arg_type));

                    let body_expr = self.reconstruct(body, &local_env)?;

                    let Some(TypeScheme::PlainType(arg_type)) = local_env.0.remove(arg) else {unreachable!()};
                    (arg_type, body_expr)
                };
                let new_arg = self.find(arg_type);
                let new_body = self.find(*body_expr.tag());

                let tt = Type::Function(new_arg, new_body);
                let tr = self.insert(tt);
                Ok(Expr::Lambda(tr, arg.clone(), Box::new(body_expr)))
            }
            Expr::BinLambda(_, arg0, arg1, body) => {
                let (arg0_type, arg1_type, body_expr) = {
                    let mut local_env = TypeEnv::new();
                    local_env
                        .0
                        .extend(env.0.iter().map(|(k, v)| (k.clone(), v.clone())));

                    let arg0_type = self.genvar();
                    let arg1_type = self.genvar();
                    local_env
                        .0
                        .insert(arg0.clone(), TypeScheme::PlainType(arg0_type));
                    local_env
                        .0
                        .insert(arg1.clone(), TypeScheme::PlainType(arg1_type));

                    let body_expr = self.reconstruct(body, &local_env)?;

                    let Some(TypeScheme::PlainType(arg0_type)) = local_env.0.remove(arg0) else {unreachable!()};
                    let Some(TypeScheme::PlainType(arg1_type)) = local_env.0.remove(arg1) else {unreachable!()};
                    (arg0_type, arg1_type, body_expr)
                };
                let new_arg0 = self.find(arg0_type);
                let new_arg1 = self.find(arg1_type);
                let new_body = self.find(*body_expr.tag());

                let tt = Type::BinaryFunction(new_arg0, new_arg1, new_body);
                let tr = self.insert(tt);
                Ok(Expr::BinLambda(
                    tr,
                    arg0.clone(),
                    arg1.clone(),
                    Box::new(body_expr),
                ))
            }
            Expr::Let(_, arg, def, body) => {
                // Reconstruct the principal type of def
                let def_expr = self.reconstruct(def, env)?;
                let t1 = self.find(*def_expr.tag());

                // Generalize over the free variables in t1
                let t1 = self.generalize(t1, env);

                // Extend environment with arg -> t1
                let body_expr = {
                    let mut local_env = TypeEnv::new();
                    local_env
                        .0
                        .extend(env.0.iter().map(|(k, v)| (k.clone(), v.clone())));
                    local_env.0.insert(arg.clone(), t1);

                    self.reconstruct(body, &local_env)?
                };

                let tt = self.find(*body_expr.tag());
                Ok(Expr::Let(
                    tt,
                    arg.clone(),
                    Box::new(def_expr),
                    Box::new(body_expr),
                ))
            }
            Expr::App(_, fun, arg) => {
                // (f:(a -> b) arg: a):b
                let ft = self.reconstruct(fun, env)?;
                let at = self.reconstruct(arg, env)?;

                let rt = self.genvar();

                let tt = Type::Function(*at.tag(), rt);
                let tr = self.insert(tt);

                // That clone is a little annoying.
                self.unify_typerefs(*ft.tag(), tr)?;

                let rt = self.find(rt);

                Ok(Expr::App(rt, Box::new(ft), Box::new(at)))
            }
            Expr::BinApp(_, fun, arg0, arg1) => {
                // (f:(a -> b) arg: a):b
                let ft = self.reconstruct(fun, env)?;
                let at0 = self.reconstruct(arg0, env)?;
                let at1 = self.reconstruct(arg1, env)?;

                let rt = self.genvar();

                let tt = Type::BinaryFunction(*at0.tag(), *at1.tag(), rt);
                let tr = self.insert(tt);

                self.unify_typerefs(*ft.tag(), tr)?;

                let rt = self.find(rt);

                Ok(Expr::BinApp(rt, Box::new(ft), Box::new(at0), Box::new(at1)))
            }
            Expr::If(_, pred, conseq, alt) => {
                // Predicate must be a Boolean
                let pt = self.reconstruct(pred, env)?;
                let br = self.insert(Type::Boolean);
                self.unify_typerefs(*pt.tag(), br)?;

                // Consequent and alternative must have the same type
                let ct = self.reconstruct(conseq, env)?;
                let at = self.reconstruct(alt, env)?;
                self.unify_typerefs(*ct.tag(), *at.tag())?;

                // Does it matter whether we return ct or at?
                let tt = self.find(*at.tag());
                Ok(Expr::If(tt, Box::new(pt), Box::new(ct), Box::new(at)))
            }
            Expr::Map(_, fun, arg) => {
                // map: ∀a b . (a -> b) -> [a] -> [b]
                let ft = self.reconstruct(fun, env)?;
                let at = self.reconstruct(arg, env)?;

                // at == [et]
                let et = self.genvar();
                let aref = self.insert(Type::Array(et));
                self.unify_typerefs(*at.tag(), aref)?;

                // ft == el_type -> rt
                let rt = self.genvar();
                let tt = Type::Function(et, rt.clone());
                let tr = self.insert(tt);
                self.unify_typerefs(*ft.tag(), tr)?;

                let map_type = Type::Array(self.find(rt));
                let map_ref = self.insert(map_type);
                Ok(Expr::Map(map_ref, Box::new(ft), Box::new(at)))
            }
            Expr::Reduce(_, fun, init, arg) => {
                // reduce: ∀ a b . (b x a -> b) -> b -> [a] -> b

                let ft = self.reconstruct(fun, env)?;
                let it = self.reconstruct(init, env)?;
                let at = self.reconstruct(arg, env)?;

                // at == [et]
                let et = self.genvar();
                let array_ref = self.insert(Type::Array(et));
                self.unify_typerefs(*at.tag(), array_ref)?;

                let rt = self.genvar();
                let tt = Type::BinaryFunction(rt, et, rt);
                let tr = self.insert(tt);

                // ft == rt x et -> rt
                self.unify_typerefs(*ft.tag(), tr)?;
                // it == rt
                self.unify_typerefs(*it.tag(), rt)?;

                let rt = self.find(rt);

                Ok(Expr::Reduce(rt, Box::new(ft), Box::new(it), Box::new(at)))
            }
            Expr::Scan(_, fun, init, arg) => {
                // scan: ∀ a b . (b x a -> b) -> b -> [a] -> b

                let ft = self.reconstruct(fun, env)?;
                let it = self.reconstruct(init, env)?;
                let at = self.reconstruct(arg, env)?;

                let et = self.genvar();
                let aref = self.insert(Type::Array(et));

                self.unify_typerefs(*at.tag(), aref)?;

                let rt = self.genvar();
                let tt = Type::BinaryFunction(rt, et, rt);
                let tr = self.insert(tt);

                // ft == rt x et -> rt
                self.unify_typerefs(*ft.tag(), tr)?;
                // it == rt
                self.unify_typerefs(*it.tag(), rt)?;

                let scan_ref = self.insert(Type::Array(self.find(rt)));
                Ok(Expr::Scan(
                    scan_ref,
                    Box::new(ft),
                    Box::new(it),
                    Box::new(at),
                ))
            }
            Expr::Iota(_, n) => {
                let nt = self.reconstruct(n, env)?;
                let iref = self.insert(Type::Integer);
                self.unify_typerefs(*nt.tag(), iref)?;

                let iota_type = self.insert(Type::Array(iref));
                Ok(Expr::Iota(iota_type, Box::new(nt)))
            }
            Expr::Pair(_, e1, e2) => {
                let t1 = self.reconstruct(e1, env)?;
                let t2 = self.reconstruct(e2, env)?;

                let tt = Type::Pair(*t1.tag(), *t2.tag());
                let tr = self.insert(tt);

                Ok(Expr::Pair(tr, Box::new(t1), Box::new(t2)))
            }
            Expr::Fst(_, p) => {
                let pt = self.reconstruct(p, env)?;

                let rt1 = self.genvar();
                let rt2 = self.genvar();
                let tr = self.insert(Type::Pair(rt1, rt2));

                self.unify_typerefs(*pt.tag(), tr)?;
                Ok(Expr::Fst(self.find(rt1), Box::new(pt)))
            }
            Expr::Snd(_, p) => {
                let pt = self.reconstruct(p, env)?;

                let rt1 = self.genvar();
                let rt2 = self.genvar();
                let tr = self.insert(Type::Pair(rt1, rt2));

                self.unify_typerefs(*pt.tag(), tr)?;
                Ok(Expr::Snd(self.find(rt2), Box::new(pt)))
            }
        }
    }

    fn free_vars(&self, t: TypeRef) -> HashMap<TypeRef, ()> {
        match self.get(t) {
            Type::Boolean => HashMap::new(),
            Type::Integer => HashMap::new(),
            Type::Float32 => HashMap::new(),
	    Type::Float64 => HashMap::new(),
            Type::Variable(n) => {
                let mut fvs = HashMap::new();
                fvs.insert(t, ());
                fvs
            }
            Type::Array(body) => self.free_vars(*body),
            Type::Pair(t1, t2) => {
                let mut u = self.free_vars(*t1);
                let v = self.free_vars(*t2);
                u.extend(v);
                u
            }
            Type::Function(arg, body) => {
                let mut u = self.free_vars(*arg);
                let v = self.free_vars(*body);
                u.extend(v);
                u
            }
            Type::BinaryFunction(arg0, arg1, body) => {
                let mut u = self.free_vars(*arg0);
                let v = self.free_vars(*arg1);
                let w = self.free_vars(*body);
                u.extend(v);
                u.extend(w);
                u
            }
        }
    }

    fn free_vars_scheme(&self, t: &TypeScheme) -> HashMap<TypeRef, ()> {
        match t {
            TypeScheme::PlainType(t) => self.free_vars(*t),
            TypeScheme::QuantifiedType(fvs, t) => {
                let mut tvs = self.free_vars(*t);
                let qts: HashMap<TypeRef, ()> = fvs.iter().cloned().map(|t| (t, ())).collect();
                for k in qts.keys() {
                    tvs.remove(k);
                }
                tvs
            }
        }
    }

    fn free_env_vars(&self, env: &TypeEnv) -> HashMap<TypeRef, ()> {
        let mut fvs = HashMap::new();
        for t in env.0.values() {
            fvs.extend(self.free_vars_scheme(t).into_iter())
        }
        fvs
    }

    fn generalize(&self, t: TypeRef, env: &TypeEnv) -> TypeScheme {
        let fvs = self.free_vars(t);
        let mut qts = Vec::new();
        let evs = self.free_env_vars(env);

        for (k,v) in fvs {
            if !evs.contains_key(&k) {
            qts.push(k)
            }
        }
        TypeScheme::QuantifiedType(qts, t)
    }

    fn substitute(&mut self, sub: &HashMap<TypeRef, TypeRef>, t: TypeRef) -> TypeRef {
        // recursively apply the substitution to the type, inserting the new type and returning a reference to that type

        // Check if the supplied TypeRef is in the substitution
        // If so, then we return the substituted TypeRef
        // Otherwise, we follow the type ref and recursively replace types based on the substitution
        match sub.get(&t) {
            Some(t) => *t,
            None => {
                let new_type = match self.get(t) {
                    Type::Boolean | Type::Integer | Type::Float32 | Type::Float64 | Type::Variable(_) => {
                        // If the type ref resolves to a constant or a variable, but it is not in the substitution,
                        // we just return the old typeref
                        None
                    }
                    Type::Array(arr) => {
                        // Substitute the array's child type and return an array with the new typeref
                        let new_arr = self.substitute(sub, *arr);
                        Some(Type::Array(new_arr))
                    }
                    Type::Pair(p0, p1) => {
                        let p0 = *p0;
                        let p1 = *p1;
                        let q0 = self.substitute(sub, p0);
                        let q1 = self.substitute(sub, p1);
                        Some(Type::Pair(q0, q1))
                    }
                    Type::Function(arg, body) => {
                        let arg = *arg;
                        let body = *body;
                        let new_arg = self.substitute(sub, arg);
                        let new_body = self.substitute(sub, body);
                        Some(Type::Function(new_arg, new_body))
                    }
                    Type::BinaryFunction(arg0, arg1, body) => {
                        let arg0 = *arg0;
                        let arg1 = *arg1;
                        let body = *body;
                        let new_arg0 = self.substitute(sub, arg0);
                        let new_arg1 = self.substitute(sub, arg1);
                        let new_body = self.substitute(sub, body);
                        Some(Type::BinaryFunction(new_arg0, new_arg1, new_body))
                    }
                };

                match new_type {
                    Some(nt) => self.insert(nt),
                    None => t,
                }
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::{Type, TypeEnv, UnionFind};
    use crate::parser::{sexpr::parser::SExpr, Expr};
    use crate::error::Error;

    #[test]
    fn unification_test() {
        let mut u = UnionFind::new();

        let _tr0 = u.insert(Type::Boolean);
        let tr1 = u.insert(Type::Integer);
        let tr2 = u.insert(Type::Float64);
        let tr3 = u.insert(Type::Array(tr2));

        let tr5 = u.insert(Type::Variable(1));
        let tr6 = u.insert(Type::Variable(2));

        let t7 = Type::Pair(tr1, tr3);
        let tr7 = u.insert(t7.clone());
        let t8 = Type::Pair(tr5, tr6);
        let tr8 = u.insert(t8.clone());

        u.unify_typerefs(tr7, tr8).unwrap();
        assert_eq!(u.find(tr7), u.find(tr8));
    }

    #[test]
    fn test1() {
        let expr = Expr::parse(
            &"(let ((f (lambda (x) x))) (f 1.0))"
                .parse::<SExpr>()
                .unwrap(),
        )
        .unwrap();

        let mut sub = UnionFind::new();
        let env = TypeEnv::new();
        let t = sub.reconstruct(&expr, &env).unwrap();

        assert_eq!(sub.get(sub.find(*t.tag())), &Type::Float64);

        //
        let expr =
            Expr::parse(&"(let ((f (lambda (x) x))) (f 1))".parse::<SExpr>().unwrap()).unwrap();

        let mut sub = UnionFind::new();
        let env = TypeEnv::new();
        let t = sub.reconstruct(&expr, &env).unwrap();

        assert_eq!(sub.get(sub.find(*t.tag())), &Type::Integer);

        //
        let expr = Expr::parse(
            &"(let ((f (lambda (x) x))) (f true))"
                .parse::<SExpr>()
                .unwrap(),
        )
        .unwrap();

        let mut sub = UnionFind::new();
        let env = TypeEnv::new();
        let t = sub.reconstruct(&expr, &env).unwrap();

        assert_eq!(sub.get(sub.find(*t.tag())), &Type::Boolean);
    }

    #[test]
    fn test2() {
        let expr = Expr::parse(&"(if true 1.0 2.0)".parse::<SExpr>().unwrap()).unwrap();

        let mut sub = UnionFind::new();
        let env = TypeEnv::new();
        let t = sub.reconstruct(&expr, &env).unwrap();

        assert_eq!(sub.get(sub.find(*t.tag())), &Type::Float64);

        //
        let expr = Expr::parse(&"(if true 1 2)".parse::<SExpr>().unwrap()).unwrap();

        let mut sub = UnionFind::new();
        let env = TypeEnv::new();
        let t = sub.reconstruct(&expr, &env).unwrap();

        assert_eq!(sub.get(sub.find(*t.tag())), &Type::Integer);

        //
        let expr = Expr::parse(&"(if true false true)".parse::<SExpr>().unwrap()).unwrap();

        let mut sub = UnionFind::new();
        let env = TypeEnv::new();
        let t = sub.reconstruct(&expr, &env).unwrap();

        assert_eq!(sub.get(sub.find(*t.tag())), &Type::Boolean);

        //
        let expr = Expr::parse(&"(if true 1.0 1)".parse::<SExpr>().unwrap()).unwrap();

        let mut sub = UnionFind::new();
        let env = TypeEnv::new();
        match sub.reconstruct(&expr, &env).unwrap_err() {
            Error::TypeError(_) => {}
            _ => panic!("Expected test to throw TypeError"),
        }

        //
        let expr = Expr::parse(&"(if 2.0 1 2)".parse::<SExpr>().unwrap()).unwrap();

        let mut sub = UnionFind::new();
        let env = TypeEnv::new();
        match sub.reconstruct(&expr, &env).unwrap_err() {
            Error::TypeError(_) => {}
            _ => panic!("Expected test to throw TypeError"),
        }
    }

    #[test]
    fn test3() {
        let expr = Expr::parse(
            &"(reduce (lambda (u v) v) 0 (iota 10))"
                .parse::<SExpr>()
                .unwrap(),
        )
        .unwrap();

        let mut sub = UnionFind::new();
        let env = TypeEnv::new();
        let t = sub.reconstruct(&expr, &env).unwrap();

        assert_eq!(sub.get(sub.find(*t.tag())), &Type::Integer);

        let expr = Expr::parse(
            &"(scan (lambda (u v) v) 0 (iota 10))"
                .parse::<SExpr>()
                .unwrap(),
        )
        .unwrap();

        let mut sub = UnionFind::new();
        let env = TypeEnv::new();
        let t = sub.reconstruct(&expr, &env).unwrap();

	let iref = sub.insert(Type::Integer);
        assert_eq!(sub.get(sub.find(*t.tag())), &Type::Array(iref))
    }

    #[test]
    fn test4() {
        let expr = Expr::parse(
            &"(map (lambda (x) x) (iota 10))"
                .parse::<SExpr>()
                .unwrap(),
        )
        .unwrap();

        let mut sub = UnionFind::new();
        let env = TypeEnv::new();
        let t = sub.reconstruct(&expr, &env).unwrap();

	let bref = sub.insert(Type::Integer);
	let aref = sub.insert(Type::Array(bref));
	println!("{:?} {:?}",sub.pretty_print(sub.find(*t.tag())),sub.pretty_print(sub.find(aref)));
        assert_eq!(sub.get(sub.find(*t.tag())), &Type::Array(bref))
    }

    /*
    #[test]
    fn test5() {
        // Direct expression
        let expr = Expr::parse(&"(reduce + 0 (iota 10))".parse::<SExpr>().unwrap()).unwrap();

        let (mut sub, env, _, _) = crate::stdlib::initialize();

        let t = sub.reconstruct(&expr, &env).unwrap();
        assert_eq!(t.tag(), &Type::Integer);

        // Let expression
        let expr = Expr::parse(
            &"(let ((xs (iota 10))) (reduce + 0 xs))"
                .parse::<SExpr>()
                .unwrap(),
        )
        .unwrap();

        let (mut sub, env, _, _) = crate::stdlib::initialize();

        let t = sub.reconstruct(&expr, &env).unwrap();
        assert_eq!(t.tag(), &Type::Integer);

        // Lambda application
        let expr = Expr::parse(
            &"((lambda (xs) (reduce + 0 xs)) (iota 10))"
                .parse::<SExpr>()
                .unwrap(),
        )
        .unwrap();

        let (mut sub, env, _, _) = crate::stdlib::initialize();

        let t = sub.reconstruct(&expr, &env).unwrap();
        assert_eq!(t.tag(), &Type::Integer);
    }

    #[test]
    fn test6() {
        // Lambda application
        let expr = Expr::parse(
            &"((lambda (xs) (map (lambda (u) (+ u 1)) xs)) (iota 10))"
                .parse::<SExpr>()
                .unwrap(),
        )
        .unwrap();

        let (mut sub, env, _, _) = crate::stdlib::initialize();

        let t = sub.reconstruct(&expr, &env).unwrap();
        assert_eq!(t.tag(), &Type::Array(Box::new(Type::Integer)));
    }

    #[test]
    fn test7() {
        let expr = Expr::parse(&"(lambda (xs) (reduce + 0 xs))".parse::<SExpr>().unwrap()).unwrap();

        let (mut sub, env, _, _) = crate::stdlib::initialize();

        let t = sub.reconstruct(&expr, &env).unwrap();
        assert_eq!(
            t.tag(),
            &Type::Function(
                Box::new(Type::Array(Box::new(Type::Integer))),
                Box::new(Type::Integer)
            )
        );
    }

    #[test]
    fn pairs() {
        let expr = Expr::parse(
            &"(snd (fst (pair (pair 1.0 1) true)))"
                .parse::<SExpr>()
                .unwrap(),
        )
        .unwrap();
        let (mut sub, env, _, _) = crate::stdlib::initialize();
        let t = sub.reconstruct(&expr, &env).unwrap();

        assert_eq!(t.tag(), &Type::Integer);
    }

    #[test]
    fn overflow_test1() {
        let expr = Expr::parse(
            &"((lambda (u v) (- (+ u v) v)) 1.0 2.0)"
                .parse::<SExpr>()
                .unwrap(),
        )
        .unwrap();

        let (mut sub, env, _, _) = crate::stdlib::initialize();
        let t = sub.reconstruct(&expr, &env).unwrap();

        assert_eq!(t.tag(), &Type::Float64);
}
    */
}

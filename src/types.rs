//! Type inference and lowering to the let-normal core.
//!
//! Function signatures are written out; everything inside a body is
//! inferred by unification. Type parameters are rigid inside the function
//! that declares them and instantiated afresh at each call.

use crate::core::{Atom, Core, CoreFn, Module, Prim};
use crate::error::{Error, Pos, Result};
use crate::syntax::{ArmPat, BinOp, Expr, ExprKind, FnDef, Pat, Program, Type};
use std::collections::HashMap;

#[derive(Clone, Debug, PartialEq, Eq)]
enum Ty {
    Int,
    Bool,
    Unit,
    List(Box<Ty>),
    Pair(Box<Ty>, Box<Ty>),
    Param(String),
    Meta(usize),
}

struct Infer<'p> {
    prog: &'p Program,
    subst: Vec<Option<Ty>>,
    types: Vec<Option<Ty>>,
}

fn from_type(t: &Type, params: &HashMap<String, Ty>) -> Ty {
    match t {
        Type::Int => Ty::Int,
        Type::Bool => Ty::Bool,
        Type::Unit => Ty::Unit,
        Type::List(a) => Ty::List(Box::new(from_type(a, params))),
        Type::Pair(a, b) => Ty::Pair(Box::new(from_type(a, params)), Box::new(from_type(b, params))),
        Type::Param(p) => params.get(p).cloned().unwrap_or_else(|| Ty::Param(p.clone())),
    }
}

fn params_of(t: &Type, out: &mut Vec<String>) {
    match t {
        Type::List(a) => params_of(a, out),
        Type::Pair(a, b) => {
            params_of(a, out);
            params_of(b, out);
        }
        Type::Param(p) if !out.contains(p) => out.push(p.clone()),
        _ => {}
    }
}

pub fn show_type(t: &Type) -> String {
    match t {
        Type::Int => "Int".into(),
        Type::Bool => "Bool".into(),
        Type::Unit => "Unit".into(),
        Type::List(a) => format!("List<{}>", show_type(a)),
        Type::Pair(a, b) => format!("({}, {})", show_type(a), show_type(b)),
        Type::Param(p) => p.clone(),
    }
}

impl<'p> Infer<'p> {
    fn fresh(&mut self) -> Ty {
        self.subst.push(None);
        Ty::Meta(self.subst.len() - 1)
    }

    fn resolve(&self, t: &Ty) -> Ty {
        match t {
            Ty::Meta(m) => match &self.subst[*m] {
                Some(u) => self.resolve(u),
                None => t.clone(),
            },
            Ty::List(a) => Ty::List(Box::new(self.resolve(a))),
            Ty::Pair(a, b) => Ty::Pair(Box::new(self.resolve(a)), Box::new(self.resolve(b))),
            _ => t.clone(),
        }
    }

    fn show(&self, t: &Ty) -> String {
        match self.resolve(t) {
            Ty::Int => "Int".into(),
            Ty::Bool => "Bool".into(),
            Ty::Unit => "Unit".into(),
            Ty::List(a) => format!("List<{}>", self.show(&a)),
            Ty::Pair(a, b) => format!("({}, {})", self.show(&a), self.show(&b)),
            Ty::Param(p) => p,
            Ty::Meta(_) => "_".into(),
        }
    }

    fn occurs(&self, m: usize, t: &Ty) -> bool {
        match self.resolve(t) {
            Ty::Meta(n) => n == m,
            Ty::List(a) => self.occurs(m, &a),
            Ty::Pair(a, b) => self.occurs(m, &a) || self.occurs(m, &b),
            _ => false,
        }
    }

    fn unify(&mut self, pos: Pos, want: &Ty, got: &Ty) -> Result<()> {
        let (a, b) = (self.resolve(want), self.resolve(got));
        match (&a, &b) {
            (Ty::Meta(m), Ty::Meta(n)) if m == n => Ok(()),
            (Ty::Meta(m), t) | (t, Ty::Meta(m)) => {
                if self.occurs(*m, t) {
                    return Err(Error::at(pos, "this value would have an infinite type"));
                }
                self.subst[*m] = Some(t.clone());
                Ok(())
            }
            (Ty::List(x), Ty::List(y)) => self.unify(pos, x, y),
            (Ty::Pair(x1, x2), Ty::Pair(y1, y2)) => {
                self.unify(pos, x1, y1)?;
                self.unify(pos, x2, y2)
            }
            _ if a == b => Ok(()),
            _ => Err(Error::at(pos, format!("expected {}, found {}", self.show(&a), self.show(&b)))),
        }
    }

    fn bind_pat(&mut self, pos: Pos, p: &Pat, t: &Ty, env: &mut HashMap<String, Ty>) -> Result<()> {
        match p {
            Pat::Var(x) => {
                env.insert(x.clone(), t.clone());
            }
            Pat::Wild => {}
            Pat::Pair(a, b) => {
                let (ta, tb) = (self.fresh(), self.fresh());
                self.unify(pos, &Ty::Pair(Box::new(ta.clone()), Box::new(tb.clone())), t)?;
                self.bind_pat(pos, a, &ta, env)?;
                self.bind_pat(pos, b, &tb, env)?;
            }
        }
        Ok(())
    }

    fn infer(&mut self, e: &Expr, env: &HashMap<String, Ty>) -> Result<Ty> {
        let t = match &e.kind {
            ExprKind::Var(x) => {
                env.get(x).cloned().ok_or_else(|| Error::at(e.pos, format!("unknown variable `{x}`")))?
            }
            ExprKind::Int(_) => Ty::Int,
            ExprKind::Bool(_) => Ty::Bool,
            ExprKind::Unit | ExprKind::Tick(_) => Ty::Unit,
            ExprKind::Nil => {
                let a = self.fresh();
                Ty::List(Box::new(a))
            }
            ExprKind::List(items) => {
                let a = self.fresh();
                for it in items {
                    let t = self.infer(it, env)?;
                    self.unify(it.pos, &a, &t)?;
                }
                Ty::List(Box::new(a))
            }
            ExprKind::Cons(h, t) => {
                let th = self.infer(h, env)?;
                let tt = self.infer(t, env)?;
                let l = Ty::List(Box::new(th));
                self.unify(t.pos, &l, &tt)?;
                l
            }
            ExprKind::Pair(a, b) => {
                let ta = self.infer(a, env)?;
                let tb = self.infer(b, env)?;
                Ty::Pair(Box::new(ta), Box::new(tb))
            }
            ExprKind::Bin(op, a, b) => {
                let ta = self.infer(a, env)?;
                let tb = self.infer(b, env)?;
                match op {
                    BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod => {
                        self.unify(a.pos, &Ty::Int, &ta)?;
                        self.unify(b.pos, &Ty::Int, &tb)?;
                        Ty::Int
                    }
                    BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                        self.unify(a.pos, &Ty::Int, &ta)?;
                        self.unify(b.pos, &Ty::Int, &tb)?;
                        Ty::Bool
                    }
                    BinOp::Eq | BinOp::Ne => {
                        self.unify(b.pos, &ta, &tb)?;
                        match self.resolve(&ta) {
                            Ty::Int | Ty::Bool | Ty::Unit => {}
                            Ty::Meta(_) => self.unify(a.pos, &Ty::Int, &ta)?,
                            t => {
                                return Err(Error::at(
                                    e.pos,
                                    format!(
                                        "`{}` compares Int, Bool or Unit, not {}; write the comparison as a function",
                                        op.symbol(),
                                        self.show(&t)
                                    ),
                                ));
                            }
                        }
                        Ty::Bool
                    }
                    BinOp::And | BinOp::Or => {
                        self.unify(a.pos, &Ty::Bool, &ta)?;
                        self.unify(b.pos, &Ty::Bool, &tb)?;
                        Ty::Bool
                    }
                }
            }
            ExprKind::Neg(a) => {
                let t = self.infer(a, env)?;
                self.unify(a.pos, &Ty::Int, &t)?;
                Ty::Int
            }
            ExprKind::Not(a) => {
                let t = self.infer(a, env)?;
                self.unify(a.pos, &Ty::Bool, &t)?;
                Ty::Bool
            }
            ExprKind::If(c, t, f) => {
                let tc = self.infer(c, env)?;
                self.unify(c.pos, &Ty::Bool, &tc)?;
                let tt = self.infer(t, env)?;
                let tf = self.infer(f, env)?;
                self.unify(f.pos, &tt, &tf)?;
                tt
            }
            ExprKind::Match(scrut, arms) => {
                let ts = self.infer(scrut, env)?;
                check_arms(e.pos, arms)?;
                let result = self.fresh();
                let list = arms.iter().any(|a| matches!(a.pat, ArmPat::Nil | ArmPat::Cons(..)));
                let elem = self.fresh();
                if list {
                    self.unify(scrut.pos, &Ty::List(Box::new(elem.clone())), &ts)?;
                }
                for arm in arms {
                    let mut env2 = env.clone();
                    match &arm.pat {
                        ArmPat::Nil => {}
                        ArmPat::Cons(h, t) => {
                            if let Some(h) = h {
                                env2.insert(h.clone(), elem.clone());
                            }
                            if let Some(t) = t {
                                env2.insert(t.clone(), Ty::List(Box::new(elem.clone())));
                            }
                        }
                        ArmPat::Other(p) => self.bind_pat(arm.pos, p, &ts, &mut env2)?,
                    }
                    let tb = self.infer(&arm.body, &env2)?;
                    self.unify(arm.body.pos, &result, &tb)?;
                }
                result
            }
            ExprKind::Let(p, e1, e2) => {
                let t1 = self.infer(e1, env)?;
                let mut env2 = env.clone();
                self.bind_pat(e.pos, p, &t1, &mut env2)?;
                self.infer(e2, &env2)?
            }
            ExprKind::Call(f, args) => {
                let def = self.prog.get(f).ok_or_else(|| Error::at(e.pos, format!("unknown function `{f}`")))?;
                if def.params.len() != args.len() {
                    return Err(Error::at(
                        e.pos,
                        format!("`{f}` takes {} argument(s), but {} were given", def.params.len(), args.len()),
                    ));
                }
                let mut names = Vec::new();
                for (_, t) in &def.params {
                    params_of(t, &mut names);
                }
                params_of(&def.ret, &mut names);
                let inst: HashMap<String, Ty> = names.into_iter().map(|n| (n, self.fresh())).collect();
                for (a, (_, pt)) in args.iter().zip(&def.params) {
                    let ta = self.infer(a, env)?;
                    self.unify(a.pos, &from_type(pt, &inst), &ta)?;
                }
                from_type(&def.ret, &inst)
            }
            ExprKind::Fail(_) => self.fresh(),
        };
        self.types[e.id] = Some(t.clone());
        Ok(t)
    }

    fn concrete(&self, id: usize) -> Type {
        fn go(t: &Ty) -> Type {
            match t {
                Ty::Int => Type::Int,
                Ty::Bool => Type::Bool,
                Ty::Unit | Ty::Meta(_) => Type::Unit,
                Ty::List(a) => Type::List(Box::new(go(a))),
                Ty::Pair(a, b) => Type::Pair(Box::new(go(a)), Box::new(go(b))),
                Ty::Param(p) => Type::Param(p.clone()),
            }
        }
        go(&self.resolve(self.types[id].as_ref().expect("expression was typed")))
    }
}

fn check_arms(pos: Pos, arms: &[crate::syntax::Arm]) -> Result<()> {
    if arms.is_empty() {
        return Err(Error::at(pos, "a match needs at least one arm"));
    }
    let list = arms.iter().any(|a| matches!(a.pat, ArmPat::Nil | ArmPat::Cons(..)));
    let (mut nil, mut cons) = (false, false);
    for (i, arm) in arms.iter().enumerate() {
        if nil && cons || (i > 0 && !list) {
            return Err(Error::at(arm.pos, "this arm can never match"));
        }
        match &arm.pat {
            ArmPat::Nil if nil => return Err(Error::at(arm.pos, "this arm can never match")),
            ArmPat::Cons(..) if cons => return Err(Error::at(arm.pos, "this arm can never match")),
            ArmPat::Nil => nil = true,
            ArmPat::Cons(..) => cons = true,
            ArmPat::Other(Pat::Pair(..)) if list => {
                return Err(Error::at(arm.pos, "a list is matched with `[]` and `x :: xs`"));
            }
            ArmPat::Other(_) => {
                nil = true;
                cons = true;
            }
        }
    }
    if !nil {
        return Err(Error::at(pos, "this match does not handle `[]`"));
    }
    if !cons {
        return Err(Error::at(pos, "this match does not handle `x :: xs`"));
    }
    Ok(())
}

// ---------------------------------------------------------------- lowering

struct Lower<'a> {
    inf: &'a Infer<'a>,
    index: &'a HashMap<String, usize>,
    temps: usize,
}

type Binds = Vec<(String, Type, Core)>;

fn wrap(binds: Binds, body: Core) -> Core {
    binds.into_iter().rev().fold(body, |acc, (x, ty, e)| let_in(Some(x), ty, e, acc))
}

/// `let x = e in body`, with the lets inside `e` floated out:
/// `let x = (let y = a in b) in c` becomes `let y = a in let x = b in c`
/// when that cannot capture a variable of `c`. Flat chains of lets keep
/// the analysis from typing the same subterm many times over.
pub fn let_in(x: Option<String>, ty: Type, e: Core, body: Core) -> Core {
    match e {
        Core::Let { x: y, ty: ty_y, e1, e2 } if y.as_ref().is_none_or(|y| !body.free_vars().contains(y)) => {
            Core::Let { x: y, ty: ty_y, e1, e2: Box::new(let_in(x, ty, *e2, body)) }
        }
        e => Core::Let { x, ty, e1: Box::new(e), e2: Box::new(body) },
    }
}

impl Lower<'_> {
    fn temp(&mut self) -> String {
        self.temps += 1;
        format!("%{}", self.temps)
    }

    fn atom(&mut self, e: &Expr, binds: &mut Binds) -> Atom {
        match &e.kind {
            ExprKind::Var(x) => Atom::Var(x.clone()),
            ExprKind::Int(n) => Atom::Int(*n),
            ExprKind::Bool(b) => Atom::Bool(*b),
            ExprKind::Unit => Atom::Unit,
            ExprKind::Nil => Atom::Nil,
            _ => {
                let c = self.expr(e);
                let t = self.temp();
                binds.push((t.clone(), self.inf.concrete(e.id), c));
                Atom::Var(t)
            }
        }
    }

    fn var(&mut self, e: &Expr, binds: &mut Binds) -> String {
        match self.atom(e, binds) {
            Atom::Var(x) => x,
            a => {
                let t = self.temp();
                binds.push((t.clone(), self.inf.concrete(e.id), Core::Atom(a)));
                t
            }
        }
    }

    /// Binds a pattern to the variable `x`, around `body`.
    fn pat(&mut self, p: &Pat, x: String, ty: &Type, body: Core) -> Core {
        match p {
            Pat::Wild => body,
            Pat::Var(y) => Core::Let {
                x: Some(y.clone()),
                ty: ty.clone(),
                e1: Box::new(Core::Atom(Atom::Var(x))),
                e2: Box::new(body),
            },
            Pat::Pair(a, b) => {
                let Type::Pair(ta, tb) = ty else { unreachable!("pair pattern on a non-pair") };
                let name = |l: &mut Self, p: &Pat| match p {
                    Pat::Var(y) => Some(y.clone()),
                    Pat::Wild => None,
                    Pat::Pair(..) => Some(l.temp()),
                };
                let xa = name(self, a);
                let xb = name(self, b);
                let mut inner = body;
                if let (Pat::Pair(..), Some(v)) = (&**b, &xb) {
                    inner = self.pat(b, v.clone(), tb, inner);
                }
                if let (Pat::Pair(..), Some(v)) = (&**a, &xa) {
                    inner = self.pat(a, v.clone(), ta, inner);
                }
                Core::Split { x, a: xa, b: xb, body: Box::new(inner) }
            }
        }
    }

    fn expr(&mut self, e: &Expr) -> Core {
        let mut binds = Binds::new();
        let core = match &e.kind {
            ExprKind::Var(_) | ExprKind::Int(_) | ExprKind::Bool(_) | ExprKind::Unit | ExprKind::Nil => {
                Core::Atom(self.atom(e, &mut binds))
            }
            ExprKind::List(items) => {
                let atoms: Vec<Atom> = items.iter().map(|it| self.atom(it, &mut binds)).collect();
                let ty = self.inf.concrete(e.id);
                let mut tail = Atom::Nil;
                for a in atoms[1..].iter().rev() {
                    let t = self.temp();
                    binds.push((t.clone(), ty.clone(), Core::Cons(a.clone(), tail)));
                    tail = Atom::Var(t);
                }
                Core::Cons(atoms[0].clone(), tail)
            }
            ExprKind::Cons(h, t) => {
                let a = self.atom(h, &mut binds);
                let b = self.atom(t, &mut binds);
                Core::Cons(a, b)
            }
            ExprKind::Pair(x, y) => {
                let a = self.atom(x, &mut binds);
                let b = self.atom(y, &mut binds);
                Core::Pair(a, b)
            }
            ExprKind::Bin(BinOp::And, a, b) => {
                let c = self.atom(a, &mut binds);
                Core::If(c, Box::new(self.expr(b)), Box::new(Core::Atom(Atom::Bool(false))))
            }
            ExprKind::Bin(BinOp::Or, a, b) => {
                let c = self.atom(a, &mut binds);
                Core::If(c, Box::new(Core::Atom(Atom::Bool(true))), Box::new(self.expr(b)))
            }
            ExprKind::Bin(op, a, b) => {
                let x = self.atom(a, &mut binds);
                let y = self.atom(b, &mut binds);
                Core::Prim(Prim::Bin(*op), vec![x, y])
            }
            ExprKind::Neg(a) => Core::Prim(Prim::Neg, vec![self.atom(a, &mut binds)]),
            ExprKind::Not(a) => Core::Prim(Prim::Not, vec![self.atom(a, &mut binds)]),
            ExprKind::If(c, t, f) => {
                let c = self.atom(c, &mut binds);
                Core::If(c, Box::new(self.expr(t)), Box::new(self.expr(f)))
            }
            ExprKind::Match(scrut, arms) => {
                let x = self.var(scrut, &mut binds);
                let ty = self.inf.concrete(scrut.id);
                let list = arms.iter().any(|a| matches!(a.pat, ArmPat::Nil | ArmPat::Cons(..)));
                if !list {
                    let ArmPat::Other(p) = &arms[0].pat else { unreachable!() };
                    let body = self.expr(&arms[0].body);
                    self.pat(p, x, &ty, body)
                } else {
                    let (mut nil, mut cons) = (None, None);
                    for arm in arms {
                        match &arm.pat {
                            ArmPat::Nil => nil = Some(self.expr(&arm.body)),
                            ArmPat::Cons(h, t) => cons = Some((h.clone(), t.clone(), self.expr(&arm.body))),
                            ArmPat::Other(p) => {
                                if nil.is_none() {
                                    let body = self.expr(&arm.body);
                                    nil = Some(self.pat(p, x.clone(), &ty, body));
                                }
                                if cons.is_none() {
                                    let body = self.expr(&arm.body);
                                    cons = Some((None, None, self.pat(p, x.clone(), &ty, body)));
                                }
                            }
                        }
                    }
                    let (mut head, mut tail, mut cons) = cons.expect("checked exhaustive");
                    let nil = nil.expect("checked exhaustive").nil_for(&x);
                    let shadowed = head.as_ref() == Some(&x) || tail.as_ref() == Some(&x);
                    if !shadowed && cons.free_vars().contains(&x) {
                        let h = head.get_or_insert_with(|| self.temp()).clone();
                        let t = tail.get_or_insert_with(|| self.temp()).clone();
                        let mut fresh = || self.temp();
                        cons = cons.reuse_for(&x, &h, &t, &ty, &mut fresh);
                    }
                    Core::Match { x, nil: Box::new(nil), head, tail, cons: Box::new(cons) }
                }
            }
            ExprKind::Let(p, e1, e2) => {
                let ty = self.inf.concrete(e1.id);
                let c1 = self.expr(e1);
                let c2 = self.expr(e2);
                match p {
                    Pat::Var(x) => let_in(Some(x.clone()), ty, c1, c2),
                    Pat::Wild => let_in(None, ty, c1, c2),
                    Pat::Pair(..) => {
                        let t = self.temp();
                        let inner = self.pat(p, t.clone(), &ty, c2);
                        let_in(Some(t), ty, c1, inner)
                    }
                }
            }
            ExprKind::Call(f, args) => {
                let atoms = args.iter().map(|a| self.atom(a, &mut binds)).collect();
                Core::App(self.index[f], atoms)
            }
            ExprKind::Tick(r) => Core::Tick(*r),
            ExprKind::Fail(m) => Core::Fail(m.clone()),
        };
        wrap(binds, core)
    }
}

fn check_params(f: &FnDef) -> Result<()> {
    let mut declared = Vec::new();
    for (_, t) in &f.params {
        params_of(t, &mut declared);
    }
    let mut used = Vec::new();
    params_of(&f.ret, &mut used);
    for p in used {
        if !declared.contains(&p) {
            return Err(Error::at(
                f.pos,
                format!("`{}` returns the type parameter `{p}`, which no argument mentions", f.name),
            ));
        }
    }
    Ok(())
}

/// Type-checks a program and lowers it to the core.
pub fn check(prog: &Program) -> Result<Module> {
    let mut inf = Infer { prog, subst: Vec::new(), types: vec![None; prog.exprs] };
    for f in &prog.fns {
        check_params(f)?;
        let env: HashMap<String, Ty> =
            f.params.iter().map(|(x, t)| (x.clone(), from_type(t, &HashMap::new()))).collect();
        let tb = inf.infer(&f.body, &env)?;
        inf.unify(f.body.pos, &from_type(&f.ret, &HashMap::new()), &tb)?;
    }
    let index: HashMap<String, usize> = prog.fns.iter().enumerate().map(|(i, f)| (f.name.clone(), i)).collect();
    let mut lower = Lower { inf: &inf, index: &index, temps: 0 };
    let fns = prog
        .fns
        .iter()
        .map(|f| CoreFn {
            name: f.name.clone(),
            params: f.params.clone(),
            ret: f.ret.clone(),
            body: lower.expr(&f.body),
        })
        .collect();
    Ok(Module { fns })
}

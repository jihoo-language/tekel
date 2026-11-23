//! The let-normal core that the analysis and the interpreter both work on.
//!
//! Every argument of a constructor, operator or call is an atom, so every
//! value that is used twice has a name, and the analysis can see each place
//! where potential has to be shared.

use crate::rat::Rat;
use crate::syntax::{BinOp, Type};
use std::collections::BTreeSet;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Atom {
    Var(String),
    Int(i64),
    Bool(bool),
    Unit,
    Nil,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Prim {
    Bin(BinOp),
    Neg,
    Not,
}

#[derive(Clone, Debug)]
pub enum Core {
    Atom(Atom),
    Prim(Prim, Vec<Atom>),
    Cons(Atom, Atom),
    Pair(Atom, Atom),
    If(Atom, Box<Core>, Box<Core>),
    /// `match x { [] => nil, head :: tail => cons }`
    Match {
        x: String,
        nil: Box<Core>,
        head: Option<String>,
        tail: Option<String>,
        cons: Box<Core>,
    },
    /// The list `x`, inside the branch of a match on `x` that named its head
    /// and tail. Its potential is that of `head :: tail`, and rebuilding it
    /// allocates nothing.
    Reuse {
        x: String,
        head: String,
        tail: String,
    },
    /// `let (a, b) = x in body`
    Split {
        x: String,
        a: Option<String>,
        b: Option<String>,
        body: Box<Core>,
    },
    Let {
        x: Option<String>,
        ty: Type,
        e1: Box<Core>,
        e2: Box<Core>,
    },
    /// A call of the function with this index in [`Module::fns`].
    App(usize, Vec<Atom>),
    Tick(Rat),
    Fail(String),
}

#[derive(Clone, Debug)]
pub struct CoreFn {
    pub name: String,
    pub params: Vec<(String, Type)>,
    pub ret: Type,
    pub body: Core,
}

#[derive(Clone, Debug)]
pub struct Module {
    pub fns: Vec<CoreFn>,
}

impl Module {
    pub fn index(&self, name: &str) -> Option<usize> {
        self.fns.iter().position(|f| f.name == name)
    }
}

impl Atom {
    pub fn var(&self) -> Option<&str> {
        match self {
            Atom::Var(x) => Some(x),
            _ => None,
        }
    }
}

fn atom_fv(a: &Atom, out: &mut BTreeSet<String>) {
    if let Atom::Var(x) = a {
        out.insert(x.clone());
    }
}

fn bind(out: &mut BTreeSet<String>, inner: BTreeSet<String>, bound: &[&Option<String>]) {
    for x in inner {
        if !bound.iter().any(|b| b.as_deref() == Some(x.as_str())) {
            out.insert(x);
        }
    }
}

impl Core {
    pub fn free_vars(&self) -> BTreeSet<String> {
        let mut out = BTreeSet::new();
        self.fv(&mut out);
        out
    }

    fn fv(&self, out: &mut BTreeSet<String>) {
        match self {
            Core::Atom(a) => atom_fv(a, out),
            Core::Prim(_, args) | Core::App(_, args) => args.iter().for_each(|a| atom_fv(a, out)),
            Core::Cons(a, b) | Core::Pair(a, b) => {
                atom_fv(a, out);
                atom_fv(b, out);
            }
            Core::If(c, t, e) => {
                atom_fv(c, out);
                t.fv(out);
                e.fv(out);
            }
            Core::Match { x, nil, head, tail, cons } => {
                out.insert(x.clone());
                nil.fv(out);
                bind(out, cons.free_vars(), &[head, tail]);
            }
            Core::Split { x, a, b, body } => {
                out.insert(x.clone());
                bind(out, body.free_vars(), &[a, b]);
            }
            Core::Let { x, e1, e2, .. } => {
                e1.fv(out);
                bind(out, e2.free_vars(), &[x]);
            }
            Core::Reuse { head, tail, .. } => {
                out.insert(head.clone());
                out.insert(tail.clone());
            }
            Core::Tick(_) | Core::Fail(_) => {}
        }
    }

    fn binds(&self, y: &str) -> bool {
        let is = |b: &Option<String>| b.as_deref() == Some(y);
        match self {
            Core::Match { head, tail, .. } => is(head) || is(tail),
            Core::Split { a, b, .. } => is(a) || is(b),
            Core::Let { x, .. } => is(x),
            _ => false,
        }
    }

    /// Rewrites the uses of `x` in the nil branch of a match on `x`, where `x` is `[]`.
    pub fn nil_for(self, x: &str) -> Core {
        let a = |at: Atom| if at.var() == Some(x) { Atom::Nil } else { at };
        match self {
            Core::Atom(at) => Core::Atom(a(at)),
            Core::Cons(h, t) => Core::Cons(a(h), a(t)),
            Core::Pair(p, q) => Core::Pair(a(p), a(q)),
            Core::App(f, args) => Core::App(f, args.into_iter().map(a).collect()),
            Core::If(c, t, f) => Core::If(c, Box::new(t.nil_for(x)), Box::new(f.nil_for(x))),
            // Matching `[]` again takes the nil branch.
            Core::Match { x: y, nil, .. } if y == x => nil.nil_for(x),
            Core::Match { x: y, nil, head, tail, cons } => {
                let shadow = head.as_deref() == Some(x) || tail.as_deref() == Some(x);
                let cons = if shadow { cons } else { Box::new(cons.nil_for(x)) };
                Core::Match { x: y, nil: Box::new(nil.nil_for(x)), head, tail, cons }
            }
            Core::Split { x: y, a: p, b: q, body } => {
                let shadow = p.as_deref() == Some(x) || q.as_deref() == Some(x);
                let body = if shadow { body } else { Box::new(body.nil_for(x)) };
                Core::Split { x: y, a: p, b: q, body }
            }
            Core::Let { x: y, ty, e1, e2 } => {
                let e1 = Box::new(e1.nil_for(x));
                let e2 = if y.as_deref() == Some(x) { e2 } else { Box::new(e2.nil_for(x)) };
                Core::Let { x: y, ty, e1, e2 }
            }
            other => other,
        }
    }

    /// Rewrites the uses of `x` in the cons branch of a match on `x` to
    /// [`Core::Reuse`]. A use under a binder of `head` or `tail` is left alone.
    pub fn reuse_for(self, x: &str, head: &str, tail: &str, ty: &Type, fresh: &mut dyn FnMut() -> String) -> Core {
        if self.binds(x) || self.binds(head) || self.binds(tail) {
            // Rewrite only the parts that are outside the binder.
            return match self {
                Core::Let { x: y, ty: t, e1, e2 } => {
                    Core::Let { x: y, ty: t, e1: Box::new(e1.reuse_for(x, head, tail, ty, fresh)), e2 }
                }
                other => other,
            };
        }
        let reuse = || Core::Reuse { x: x.to_string(), head: head.to_string(), tail: tail.to_string() };
        let uses = |atoms: &[&Atom]| atoms.iter().any(|a| a.var() == Some(x));
        match self {
            Core::Atom(Atom::Var(y)) if y == x => reuse(),
            Core::If(c, t, f) => Core::If(
                c,
                Box::new(t.reuse_for(x, head, tail, ty, fresh)),
                Box::new(f.reuse_for(x, head, tail, ty, fresh)),
            ),
            Core::Match { x: y, nil, head: h, tail: t, cons } => {
                let nil = Box::new(nil.reuse_for(x, head, tail, ty, fresh));
                let cons = Box::new(cons.reuse_for(x, head, tail, ty, fresh));
                if y == x {
                    // Matching `x` again in its own cons branch: bind the copy.
                    let v = fresh();
                    let m = Core::Match { x: v.clone(), nil, head: h, tail: t, cons };
                    Core::Let { x: Some(v), ty: ty.clone(), e1: Box::new(reuse()), e2: Box::new(m) }
                } else {
                    Core::Match { x: y, nil, head: h, tail: t, cons }
                }
            }
            Core::Split { x: y, a, b, body } => {
                Core::Split { x: y, a, b, body: Box::new(body.reuse_for(x, head, tail, ty, fresh)) }
            }
            Core::Let { x: y, ty: t, e1, e2 } => Core::Let {
                x: y,
                ty: t,
                e1: Box::new(e1.reuse_for(x, head, tail, ty, fresh)),
                e2: Box::new(e2.reuse_for(x, head, tail, ty, fresh)),
            },
            node @ (Core::Cons(..) | Core::Pair(..) | Core::App(..)) => {
                let hit = match &node {
                    Core::Cons(a, b) | Core::Pair(a, b) => uses(&[a, b]),
                    Core::App(_, args) => uses(&args.iter().collect::<Vec<_>>()),
                    _ => false,
                };
                if !hit {
                    return node;
                }
                let v = fresh();
                let sub = |a: Atom| if a.var() == Some(x) { Atom::Var(v.clone()) } else { a };
                let inner = match node {
                    Core::Cons(a, b) => Core::Cons(sub(a), sub(b)),
                    Core::Pair(a, b) => Core::Pair(sub(a), sub(b)),
                    Core::App(f, args) => Core::App(f, args.into_iter().map(sub).collect()),
                    _ => unreachable!(),
                };
                Core::Let { x: Some(v), ty: ty.clone(), e1: Box::new(reuse()), e2: Box::new(inner) }
            }
            other => other,
        }
    }
}

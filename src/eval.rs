//! The interpreter. It counts the cost of a run under the chosen metric and,
//! when given the bounds, audits every call against its bound.

use crate::aara::{Ann, Bound};
use crate::core::{Atom, Core, Module, Prim};
use crate::rat::Rat;
use crate::syntax::{BinOp, Metric, Type};
use std::fmt;
use std::rc::Rc;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Val {
    Int(i64),
    Bool(bool),
    Unit,
    Nil,
    Cons(V, V),
    Pair(V, V),
}

pub type V = Rc<Val>;

impl fmt::Display for Val {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Val::Int(n) => write!(f, "{n}"),
            Val::Bool(b) => write!(f, "{b}"),
            Val::Unit => write!(f, "()"),
            Val::Pair(a, b) => write!(f, "({a}, {b})"),
            Val::Nil | Val::Cons(..) => {
                write!(f, "[")?;
                let mut cur = self;
                let mut first = true;
                while let Val::Cons(h, t) = cur {
                    if !first {
                        write!(f, ", ")?;
                    }
                    first = false;
                    write!(f, "{h}")?;
                    cur = t;
                }
                write!(f, "]")
            }
        }
    }
}

pub fn length(v: &Val) -> usize {
    let mut n = 0;
    let mut cur = v;
    while let Val::Cons(_, t) = cur {
        n += 1;
        cur = t;
    }
    n
}

/// The potential of a value at an annotated type.
pub fn potential(v: &Val, a: &Ann<Rat>) -> Rat {
    match (a, v) {
        (Ann::Pair(x, y), Val::Pair(p, q)) => potential(p, x) + potential(q, y),
        (Ann::List(q, e), _) => {
            let n = length(v) as i128;
            let mut total: Rat = q.iter().enumerate().map(|(i, c)| *c * Rat::binom(n, i + 1)).sum();
            if e.annotations().iter().any(|(_, c)| !c.is_zero()) {
                let mut cur = v;
                while let Val::Cons(h, t) = cur {
                    total = total + potential(h, e);
                    cur = t;
                }
            }
            total
        }
        _ => Rat::ZERO,
    }
}

/// The bound of a call, evaluated at its arguments.
pub fn bound_at(b: &Bound, args: &[V]) -> Rat {
    let lists: Vec<&Val> = b
        .positions
        .iter()
        .map(|p| {
            let mut v: &Val = &args[p.param];
            for step in &p.path {
                let Val::Pair(x, y) = v else { unreachable!("a position goes through pairs") };
                v = if *step == 0 { x } else { y };
            }
            v
        })
        .collect();
    let lens: Vec<i128> = lists.iter().map(|v| length(v) as i128).collect();
    let mut total = b.constant;
    for (term, c) in &b.terms {
        total = total + term.iter().fold(*c, |acc, (p, k)| acc * Rat::binom(lens[*p], *k));
    }
    for (v, e) in lists.iter().zip(&b.elems) {
        if e.annotations().iter().any(|(_, c)| !c.is_zero()) {
            let mut cur: &Val = v;
            while let Val::Cons(h, t) = cur {
                total = total + potential(h, e);
                cur = t;
            }
        }
    }
    total
}

#[derive(Debug)]
pub enum RunError {
    Fail(String),
    Arith(String),
    /// A call cost more than its bound. This is a bug in Tekel.
    Unsound {
        function: String,
        cost: Rat,
        bound: Rat,
    },
}

impl fmt::Display for RunError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            RunError::Fail(m) => write!(f, "fail: {m}"),
            RunError::Arith(m) => write!(f, "{m}"),
            RunError::Unsound { function, cost, bound } => write!(
                f,
                "audit failed: a call of `{function}` cost {cost}, more than its bound {bound} (this is a bug in Tekel)"
            ),
        }
    }
}

pub struct Machine<'m> {
    m: &'m Module,
    metric: Metric,
    /// The bound of each function, if any, to audit calls against.
    audit: Option<&'m [Option<Bound>]>,
    pub cost: Rat,
    pub calls_audited: u64,
    env: Vec<(String, V)>,
}

impl<'m> Machine<'m> {
    pub fn new(m: &'m Module, metric: Metric, audit: Option<&'m [Option<Bound>]>) -> Machine<'m> {
        Machine { m, metric, audit, cost: Rat::ZERO, calls_audited: 0, env: Vec::new() }
    }

    fn lookup(&self, x: &str) -> V {
        self.env.iter().rev().find(|(y, _)| y == x).map(|(_, v)| v.clone()).expect("bound variable")
    }

    fn atom(&self, a: &Atom) -> V {
        match a {
            Atom::Var(x) => self.lookup(x),
            Atom::Int(n) => Rc::new(Val::Int(*n)),
            Atom::Bool(b) => Rc::new(Val::Bool(*b)),
            Atom::Unit => Rc::new(Val::Unit),
            Atom::Nil => Rc::new(Val::Nil),
        }
    }

    fn charge(&mut self, metric: Metric, r: Rat) {
        if self.metric == metric {
            self.cost = self.cost + r;
        }
    }

    pub fn call(&mut self, f: usize, args: Vec<V>) -> Result<V, RunError> {
        let start = self.cost;
        let bound = self.audit.and_then(|bs| bs[f].as_ref()).map(|b| bound_at(b, &args));
        self.charge(Metric::Steps, Rat::ONE);
        let def = &self.m.fns[f];
        let saved = std::mem::take(&mut self.env);
        self.env = def.params.iter().map(|(x, _)| x.clone()).zip(args).collect();
        let r = self.eval(&def.body);
        self.env = saved;
        let v = r?;
        if let Some(b) = bound {
            self.calls_audited += 1;
            let cost = self.cost - start;
            if cost > b {
                return Err(RunError::Unsound { function: def.name.clone(), cost, bound: b });
            }
        }
        Ok(v)
    }

    fn bind(&mut self, x: &Option<String>, v: V) {
        if let Some(x) = x {
            self.env.push((x.clone(), v));
        }
    }

    fn eval(&mut self, e: &Core) -> Result<V, RunError> {
        Ok(match e {
            Core::Atom(a) => self.atom(a),
            Core::Prim(p, args) => {
                let vs: Vec<V> = args.iter().map(|a| self.atom(a)).collect();
                Rc::new(prim(*p, &vs)?)
            }
            Core::Cons(h, t) => {
                self.charge(Metric::Alloc, Rat::ONE);
                Rc::new(Val::Cons(self.atom(h), self.atom(t)))
            }
            Core::Pair(a, b) => Rc::new(Val::Pair(self.atom(a), self.atom(b))),
            Core::If(c, t, f) => match &*self.atom(c) {
                Val::Bool(true) => self.eval(t)?,
                _ => self.eval(f)?,
            },
            Core::Match { x, nil, head, tail, cons } => {
                let v = self.lookup(x);
                match &*v {
                    Val::Cons(h, t) => {
                        let mark = self.env.len();
                        self.bind(head, h.clone());
                        self.bind(tail, t.clone());
                        let r = self.eval(cons);
                        self.env.truncate(mark);
                        r?
                    }
                    _ => self.eval(nil)?,
                }
            }
            Core::Split { x, a, b, body } => {
                let v = self.lookup(x);
                let Val::Pair(p, q) = &*v else { unreachable!("split of a pair") };
                let mark = self.env.len();
                self.bind(a, p.clone());
                self.bind(b, q.clone());
                let r = self.eval(body);
                self.env.truncate(mark);
                r?
            }
            Core::Let { x, e1, e2, .. } => {
                let v = self.eval(e1)?;
                let mark = self.env.len();
                self.bind(x, v);
                let r = self.eval(e2);
                self.env.truncate(mark);
                r?
            }
            Core::App(f, args) => {
                let vs = args.iter().map(|a| self.atom(a)).collect();
                self.call(*f, vs)?
            }
            Core::Reuse { x, .. } => self.lookup(x),
            Core::Tick(r) => {
                self.charge(Metric::Ticks, *r);
                Rc::new(Val::Unit)
            }
            Core::Fail(m) => return Err(RunError::Fail(m.clone())),
        })
    }
}

fn prim(p: Prim, vs: &[V]) -> Result<Val, RunError> {
    let int = |v: &V| match **v {
        Val::Int(n) => n,
        _ => unreachable!("typed"),
    };
    let overflow = || RunError::Arith("integer overflow".into());
    Ok(match p {
        Prim::Neg => Val::Int(int(&vs[0]).checked_neg().ok_or_else(overflow)?),
        Prim::Not => Val::Bool(*vs[0] == Val::Bool(false)),
        Prim::Bin(op) => {
            let (a, b) = (&vs[0], &vs[1]);
            match op {
                BinOp::Eq => Val::Bool(a == b),
                BinOp::Ne => Val::Bool(a != b),
                BinOp::And | BinOp::Or => unreachable!("lowered to if"),
                _ => {
                    let (x, y) = (int(a), int(b));
                    match op {
                        BinOp::Add => Val::Int(x.checked_add(y).ok_or_else(overflow)?),
                        BinOp::Sub => Val::Int(x.checked_sub(y).ok_or_else(overflow)?),
                        BinOp::Mul => Val::Int(x.checked_mul(y).ok_or_else(overflow)?),
                        BinOp::Div | BinOp::Mod if y == 0 => {
                            return Err(RunError::Arith("division by zero".into()));
                        }
                        BinOp::Div => Val::Int(x.checked_div_euclid(y).ok_or_else(overflow)?),
                        BinOp::Mod => Val::Int(x.checked_rem_euclid(y).ok_or_else(overflow)?),
                        BinOp::Lt => Val::Bool(x < y),
                        BinOp::Le => Val::Bool(x <= y),
                        BinOp::Gt => Val::Bool(x > y),
                        BinOp::Ge => Val::Bool(x >= y),
                        _ => unreachable!(),
                    }
                }
            }
        }
    })
}

// ---------------------------------------------------------------- values from text

pub fn list(items: Vec<V>) -> V {
    items.into_iter().rev().fold(Rc::new(Val::Nil), |t, h| Rc::new(Val::Cons(h, t)))
}

/// Parses a value literal such as `[3, 1, 2]`, `([1], true)` or `-4`, and
/// checks it against a type.
pub fn parse_value(src: &str, ty: &Type) -> Result<V, String> {
    let chars: Vec<char> = src.chars().filter(|c| !c.is_whitespace()).collect();
    let mut i = 0;
    let v = value(&chars, &mut i, ty)?;
    if i != chars.len() {
        return Err(format!("unexpected `{}` in value `{src}`", chars[i..].iter().collect::<String>()));
    }
    Ok(v)
}

fn value(c: &[char], i: &mut usize, ty: &Type) -> Result<V, String> {
    let want = |s: &str| format!("expected {s} for type {}", crate::types::show_type(ty));
    match ty {
        Type::Int | Type::Param(_) => {
            let start = *i;
            if c.get(*i) == Some(&'-') {
                *i += 1;
            }
            while c.get(*i).is_some_and(|ch| ch.is_ascii_digit()) {
                *i += 1;
            }
            let s: String = c[start..*i].iter().collect();
            s.parse::<i64>().map(|n| Rc::new(Val::Int(n))).map_err(|_| want("an integer"))
        }
        Type::Bool => {
            let rest: String = c[*i..].iter().collect();
            for (word, b) in [("true", true), ("false", false)] {
                if rest.starts_with(word) {
                    *i += word.len();
                    return Ok(Rc::new(Val::Bool(b)));
                }
            }
            Err(want("true or false"))
        }
        Type::Unit => {
            if c.get(*i) == Some(&'(') && c.get(*i + 1) == Some(&')') {
                *i += 2;
                Ok(Rc::new(Val::Unit))
            } else {
                Err(want("()"))
            }
        }
        Type::Pair(a, b) => {
            if c.get(*i) != Some(&'(') {
                return Err(want("a pair"));
            }
            *i += 1;
            let x = value(c, i, a)?;
            if c.get(*i) != Some(&',') {
                return Err(want("`,`"));
            }
            *i += 1;
            let y = value(c, i, b)?;
            if c.get(*i) != Some(&')') {
                return Err(want("`)`"));
            }
            *i += 1;
            Ok(Rc::new(Val::Pair(x, y)))
        }
        Type::List(a) => {
            if c.get(*i) != Some(&'[') {
                return Err(want("a list"));
            }
            *i += 1;
            let mut items = Vec::new();
            if c.get(*i) == Some(&']') {
                *i += 1;
                return Ok(list(items));
            }
            loop {
                items.push(value(c, i, a)?);
                match c.get(*i) {
                    Some(',') => *i += 1,
                    Some(']') => {
                        *i += 1;
                        return Ok(list(items));
                    }
                    _ => return Err(want("`,` or `]`")),
                }
            }
        }
    }
}

// ---------------------------------------------------------------- generated inputs

#[derive(Clone, Copy, Debug)]
pub enum Family {
    Ascending,
    Descending,
    Constant,
    Random(u64),
}

impl Family {
    pub fn all() -> Vec<Family> {
        let mut v = vec![Family::Ascending, Family::Descending, Family::Constant];
        v.extend((1..=5).map(Family::Random));
        v
    }
}

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        // SplitMix64.
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }
}

/// An input of type `ty` in which every list has length `n`.
pub fn generate(ty: &Type, n: usize, family: Family) -> V {
    let mut rng = Rng(match family {
        Family::Random(s) => s.wrapping_mul(0x2545_f491_4f6c_dd1d) ^ n as u64,
        _ => 0,
    });
    build(ty, n, family, &mut rng, 0)
}

fn build(ty: &Type, n: usize, fam: Family, rng: &mut Rng, k: usize) -> V {
    Rc::new(match ty {
        Type::Int | Type::Param(_) => Val::Int(match fam {
            Family::Ascending => k as i64,
            Family::Descending => n as i64 - k as i64,
            Family::Constant => 0,
            Family::Random(_) => (rng.next() % (n as u64 + 1)) as i64,
        }),
        Type::Bool => Val::Bool(match fam {
            Family::Ascending | Family::Constant => true,
            Family::Descending => false,
            Family::Random(_) => rng.next().is_multiple_of(2),
        }),
        Type::Unit => Val::Unit,
        Type::Pair(a, b) => Val::Pair(build(a, n, fam, rng, k), build(b, n, fam, rng, k)),
        Type::List(a) => {
            let items: Vec<V> = (0..n).map(|j| build(a, n, fam, rng, j)).collect();
            return list(items);
        }
    })
}

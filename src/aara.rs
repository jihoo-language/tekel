//! Automatic amortized resource analysis with multivariate polynomial potential.
//!
//! Every list in scope has a length. The *potential* of a context is a
//! polynomial in all of those lengths at once, written in the basis of
//! products of binomials `C(n₁, k₁) · C(n₂, k₂) ⋯`, with nonnegative
//! coefficients that the analysis has to find. The elements of a list carry
//! potential of their own, written in the same way but one list at a time.
//!
//! A typing says that the potential of a context pays for every step of an
//! expression and leaves the potential of its value. Taking a cell off a list
//! of length `n + 1` turns `C(n + 1, k)` into `C(n, k) + C(n, k − 1)`. Using a
//! list twice turns `C(n, i) · C(n, j)` back into a sum of `C(n, k)`. Neither
//! step needs to know `n`, so every check is a linear inequality between
//! coefficients, and a linear program finds the cheapest coefficients. Those
//! coefficients are the bound.
//!
//! The method is due to Hofmann and Jost (POPL 2003), extended to polynomial
//! potential by Hoffmann and Hofmann (ESOP 2010) and to potential that mixes
//! several lists by Hoffmann, Aehlig and Hofmann (POPL 2011, TOPLAS 2012),
//! the system behind RAML. Two mechanisms make polynomial bounds compose:
//!
//! * a recursive call may use the function's own type plus a *cost-free* type
//!   of lower degree, which carries potential through the call without paying
//!   for steps; and
//! * in `let x = e₁ in e₂`, the potential that mixes the variables of `e₁` with
//!   those of `e₂` is carried through `e₁` by cost-free typings, one for each
//!   mixed term, and becomes potential that mixes `x` with the variables of `e₂`.

use crate::core::{Atom, Core, Module};
use crate::error::{Error, Result};
use crate::lp::{Cmp, Linear, Lp, Outcome};
use crate::rat::Rat;
use crate::syntax::{Metric, Type};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::rc::Rc;

// ---------------------------------------------------------------- annotations

/// A one-list-at-a-time annotation of the elements of a list. `V` is an LP
/// variable while constraints are generated and a rational once solved.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Ann<V> {
    Base,
    /// A type parameter. It carries no potential.
    Param,
    Pair(Box<Ann<V>>, Box<Ann<V>>),
    /// `q[k-1]` is the coefficient of `C(n, k)`; a shorter vector means zeros.
    List(Vec<V>, Box<Ann<V>>),
}

impl<V: Copy> Ann<V> {
    pub fn map<W>(&self, f: &impl Fn(V) -> W) -> Ann<W> {
        match self {
            Ann::Base => Ann::Base,
            Ann::Param => Ann::Param,
            Ann::Pair(a, b) => Ann::Pair(Box::new(a.map(f)), Box::new(b.map(f))),
            Ann::List(q, e) => Ann::List(q.iter().map(|v| f(*v)).collect(), Box::new(e.map(f))),
        }
    }

    /// Every coefficient with its degree.
    pub fn annotations(&self) -> Vec<(usize, V)> {
        fn go<V: Copy>(a: &Ann<V>, out: &mut Vec<(usize, V)>) {
            match a {
                Ann::Base | Ann::Param => {}
                Ann::Pair(x, y) => {
                    go(x, out);
                    go(y, out);
                }
                Ann::List(q, e) => {
                    out.extend(q.iter().enumerate().map(|(i, v)| (i + 1, *v)));
                    go(e, out);
                }
            }
        }
        let mut out = Vec::new();
        go(self, &mut out);
        out
    }

    /// The list nodes reachable through pairs only, in order.
    pub fn positions(&self) -> Vec<(&Vec<V>, &Ann<V>)> {
        fn go<'a, V>(a: &'a Ann<V>, out: &mut Vec<(&'a Vec<V>, &'a Ann<V>)>) {
            match a {
                Ann::Pair(x, y) => {
                    go(x, out);
                    go(y, out);
                }
                Ann::List(q, e) => out.push((q, e)),
                _ => {}
            }
        }
        let mut out = Vec::new();
        go(self, &mut out);
        out
    }
}

/// The element types of the lists reachable through pairs only, in order.
/// These are the *positions* of a type: each has a length of its own.
pub fn positions(t: &Type) -> Vec<Type> {
    fn go(t: &Type, out: &mut Vec<Type>) {
        match t {
            Type::List(e) => out.push((**e).clone()),
            Type::Pair(a, b) => {
                go(a, out);
                go(b, out);
            }
            _ => {}
        }
    }
    let mut out = Vec::new();
    go(t, &mut out);
    out
}

/// The pairs of positions of `a` and `b` that are the same list. A type
/// parameter on either side matches nothing.
fn correspond(a: &Type, b: &Type) -> Vec<(usize, usize)> {
    fn go(a: &Type, b: &Type, ia: &mut usize, ib: &mut usize, out: &mut Vec<(usize, usize)>) {
        match (a, b) {
            (Type::List(_), Type::List(_)) => {
                out.push((*ia, *ib));
                *ia += 1;
                *ib += 1;
            }
            (Type::Pair(a1, a2), Type::Pair(b1, b2)) => {
                go(a1, b1, ia, ib, out);
                go(a2, b2, ia, ib, out);
            }
            _ => {
                *ia += positions(a).len();
                *ib += positions(b).len();
            }
        }
    }
    let mut out = Vec::new();
    go(a, b, &mut 0, &mut 0, &mut out);
    out
}

// ---------------------------------------------------------------- potentials

/// A multi-index: `(atom, k)` pairs, sorted by atom, every `k ≥ 1`. The empty
/// index is the constant term.
pub type Idx = Vec<(usize, usize)>;

/// The coefficients of a potential. A missing index has coefficient zero.
pub type Pot = BTreeMap<Idx, usize>;

pub fn degree_of(i: &Idx) -> usize {
    i.iter().map(|t| t.1).sum()
}

fn union(a: &Idx, b: &Idx) -> Idx {
    let mut out: Idx = a.iter().chain(b).copied().collect();
    out.sort();
    out
}

/// All indices over `atoms` of degree at most `d`, the constant included.
fn indices(atoms: &[usize], d: usize) -> Vec<Idx> {
    let mut sorted = atoms.to_vec();
    sorted.sort();
    let mut out: Vec<Idx> = vec![Vec::new()];
    for a in sorted {
        let mut next = Vec::new();
        for i in &out {
            let room = d - degree_of(i);
            next.push(i.clone());
            for k in 1..=room {
                let mut j = i.clone();
                j.push((a, k));
                next.push(j);
            }
        }
        out = next;
    }
    out
}

/// A value in a context: its type, one atom (a length) per position, and the
/// annotation of each position's elements.
#[derive(Clone, Debug)]
pub struct Val {
    pub ty: Type,
    pub atoms: Vec<usize>,
    pub elems: Vec<Ann<usize>>,
}

/// An annotated signature.
#[derive(Clone, Debug)]
pub struct Sig {
    pub params: Vec<Val>,
    pub pot: Pot,
    pub ret: Val,
    pub ret_pot: Pot,
}

impl Sig {
    fn shift(&self, off: usize) -> Sig {
        let val = |v: &Val| Val {
            ty: v.ty.clone(),
            atoms: v.atoms.clone(),
            elems: v.elems.iter().map(|a| a.map(&|x| x + off)).collect(),
        };
        let pot = |p: &Pot| p.iter().map(|(i, v)| (i.clone(), v + off)).collect();
        Sig {
            params: self.params.iter().map(val).collect(),
            pot: pot(&self.pot),
            ret: val(&self.ret),
            ret_pot: pot(&self.ret_pot),
        }
    }
}

#[derive(Clone, Debug)]
struct Ctx {
    vars: Vec<(String, Val)>,
    pot: Pot,
}

impl Ctx {
    fn get(&self, x: &str) -> &Val {
        &self.vars.iter().rev().find(|(y, _)| y == x).expect("variable in context").1
    }

    fn set(&mut self, x: &str, v: Val) {
        self.vars.retain(|(y, _)| y != x);
        self.vars.push((x.to_string(), v));
    }

    fn atoms(&self) -> HashSet<usize> {
        self.vars.iter().flat_map(|(_, v)| v.atoms.iter().copied()).collect()
    }

    /// Forgets the variables not in `keep`, and the potential that involves them.
    fn restrict(&self, keep: &BTreeSet<String>) -> Ctx {
        let vars: Vec<(String, Val)> = self.vars.iter().filter(|(x, _)| keep.contains(x)).cloned().collect();
        let mut c = Ctx { vars, pot: Pot::new() };
        let atoms = c.atoms();
        c.pot = self
            .pot
            .iter()
            .filter(|(i, _)| i.iter().all(|(a, _)| atoms.contains(a)))
            .map(|(i, v)| (i.clone(), *v))
            .collect();
        c
    }
}

/// The type and potential that an expression must produce.
#[derive(Clone, Debug)]
struct Res {
    val: Val,
    pot: Pot,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct Mode {
    degree: usize,
    cost_free: bool,
}

/// The constraints of one strongly connected component of the call graph, at
/// one degree, with the real cost or cost-free.
struct Template {
    lp: Lp,
    sigs: HashMap<usize, Sig>,
}

struct Cx {
    lp: Lp,
    sigs: HashMap<usize, Sig>,
    scc: usize,
    mode: Mode,
}

// ---------------------------------------------------------------- bounds

/// A list inside an argument: the argument and the way through pairs (0 = left).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Position {
    pub param: usize,
    pub path: Vec<u8>,
}

/// The bound found for a function, in the binomial basis.
#[derive(Clone, Debug)]
pub struct Bound {
    pub degree: usize,
    pub positions: Vec<Position>,
    /// Nonzero coefficients of products `Π C(|position|, k)`.
    pub terms: Vec<(Vec<(usize, usize)>, Rat)>,
    /// The potential of the elements of each position.
    pub elems: Vec<Ann<Rat>>,
    /// The constant part, including the cost of the call itself.
    pub constant: Rat,
}

pub fn param_positions(params: &[Type]) -> Vec<Position> {
    fn go(t: &Type, param: usize, path: &mut Vec<u8>, out: &mut Vec<Position>) {
        match t {
            Type::List(_) => out.push(Position { param, path: path.clone() }),
            Type::Pair(a, b) => {
                path.push(0);
                go(a, param, path, out);
                path.pop();
                path.push(1);
                go(b, param, path, out);
                path.pop();
            }
            _ => {}
        }
    }
    let mut out = Vec::new();
    for (i, t) in params.iter().enumerate() {
        go(t, i, &mut Vec::new(), &mut out);
    }
    out
}

// ---------------------------------------------------------------- the analysis

pub struct Analyzer<'m> {
    m: &'m Module,
    metric: Metric,
    scc_of: Vec<usize>,
    sccs: Vec<Vec<usize>>,
    memo: HashMap<(usize, Mode), Rc<Template>>,
    next_atom: usize,
}

fn lin(terms: &[(usize, i128)]) -> Linear {
    terms.iter().map(|&(v, c)| (v, Rat::int(c))).collect()
}

/// `Σ lhs − Σ rhs ≥ cost`, skipping constraints that hold trivially.
fn ge(lp: &mut Lp, lhs: &[Option<usize>], rhs: &[Option<usize>], cost: Rat) {
    let mut terms: Linear = Vec::new();
    for v in rhs.iter().flatten() {
        terms.push((*v, -Rat::ONE));
    }
    if terms.is_empty() && !cost.is_pos() {
        return;
    }
    for v in lhs.iter().flatten() {
        terms.push((*v, Rat::ONE));
    }
    lp.add(terms, Cmp::Ge, cost);
}

/// The coefficient of `C(n, k)` in `C(n, i) · C(n, j)`.
fn product_coeff(k: usize, i: usize, j: usize) -> Rat {
    if k < i.max(j) || k > i + j {
        return Rat::ZERO;
    }
    Rat::binom(k as i128, i) * Rat::binom(i as i128, i + j - k)
}

/// Tarjan's algorithm over the call graph.
fn sccs(m: &Module) -> Vec<Vec<usize>> {
    fn calls(e: &Core, out: &mut BTreeSet<usize>) {
        match e {
            Core::App(g, _) => {
                out.insert(*g);
            }
            Core::If(_, a, b) | Core::Match { nil: a, cons: b, .. } | Core::Let { e1: a, e2: b, .. } => {
                calls(a, out);
                calls(b, out);
            }
            Core::Split { body, .. } => calls(body, out),
            _ => {}
        }
    }
    let n = m.fns.len();
    let edges: Vec<Vec<usize>> = m
        .fns
        .iter()
        .map(|f| {
            let mut s = BTreeSet::new();
            calls(&f.body, &mut s);
            s.into_iter().collect()
        })
        .collect();
    struct St {
        index: Vec<Option<usize>>,
        low: Vec<usize>,
        on: Vec<bool>,
        stack: Vec<usize>,
        next: usize,
        out: Vec<Vec<usize>>,
    }
    fn visit(v: usize, edges: &[Vec<usize>], st: &mut St) {
        st.index[v] = Some(st.next);
        st.low[v] = st.next;
        st.next += 1;
        st.stack.push(v);
        st.on[v] = true;
        for &w in &edges[v] {
            match st.index[w] {
                None => {
                    visit(w, edges, st);
                    st.low[v] = st.low[v].min(st.low[w]);
                }
                Some(i) if st.on[w] => st.low[v] = st.low[v].min(i),
                _ => {}
            }
        }
        if Some(st.low[v]) == st.index[v] {
            let mut comp = Vec::new();
            loop {
                let w = st.stack.pop().unwrap();
                st.on[w] = false;
                comp.push(w);
                if w == v {
                    break;
                }
            }
            comp.sort();
            st.out.push(comp);
        }
    }
    let mut st =
        St { index: vec![None; n], low: vec![0; n], on: vec![false; n], stack: Vec::new(), next: 0, out: Vec::new() };
    for v in 0..n {
        if st.index[v].is_none() {
            visit(v, &edges, &mut st);
        }
    }
    st.out
}

impl<'m> Analyzer<'m> {
    pub fn new(m: &'m Module, metric: Metric) -> Analyzer<'m> {
        let sccs = sccs(m);
        let mut scc_of = vec![0; m.fns.len()];
        for (i, c) in sccs.iter().enumerate() {
            for &f in c {
                scc_of[f] = i;
            }
        }
        Analyzer { m, metric, scc_of, sccs, memo: HashMap::new(), next_atom: 0 }
    }

    pub fn metric(&self) -> Metric {
        self.metric
    }

    fn call_cost(&self, cf: bool) -> Rat {
        Rat::int(if !cf && self.metric == Metric::Steps { 1 } else { 0 })
    }

    fn cons_cost(&self, cf: bool) -> Rat {
        Rat::int(if !cf && self.metric == Metric::Alloc { 1 } else { 0 })
    }

    pub fn call_constant(&self) -> Rat {
        self.call_cost(false)
    }

    fn atom(&mut self) -> usize {
        self.next_atom += 1;
        self.next_atom
    }

    /// An element annotation for type `t`: fresh coefficients up to degree
    /// `Some(d)`, or none at all (no potential) for `None`.
    fn ann(lp: &mut Lp, t: &Type, d: Option<usize>) -> Ann<usize> {
        match t {
            Type::Int | Type::Bool | Type::Unit => Ann::Base,
            Type::Param(_) => Ann::Param,
            Type::Pair(a, b) => Ann::Pair(Box::new(Self::ann(lp, a, d)), Box::new(Self::ann(lp, b, d))),
            Type::List(a) => {
                let q = (0..d.unwrap_or(0)).map(|_| lp.fresh()).collect();
                Ann::List(q, Box::new(Self::ann(lp, a, d)))
            }
        }
    }

    /// The same shape as `a`, with fresh coefficients.
    fn relabel(lp: &mut Lp, a: &Ann<usize>) -> Ann<usize> {
        match a {
            Ann::Base => Ann::Base,
            Ann::Param => Ann::Param,
            Ann::Pair(x, y) => Ann::Pair(Box::new(Self::relabel(lp, x)), Box::new(Self::relabel(lp, y))),
            Ann::List(q, e) => Ann::List(q.iter().map(|_| lp.fresh()).collect(), Box::new(Self::relabel(lp, e))),
        }
    }

    fn val(&mut self, lp: &mut Lp, t: &Type, d: Option<usize>) -> Val {
        let pos = positions(t);
        Val {
            ty: t.clone(),
            atoms: pos.iter().map(|_| self.atom()).collect(),
            elems: pos.iter().map(|e| Self::ann(lp, e, d)).collect(),
        }
    }

    fn fresh_pot(lp: &mut Lp, atoms: &[usize], d: usize) -> Pot {
        indices(atoms, d).into_iter().map(|i| (i, lp.fresh())).collect()
    }

    /// The element potential on the left, added up, is at least that on the right.
    fn geq(lp: &mut Lp, lhs: &[&Ann<usize>], rhs: &[&Ann<usize>]) {
        let (mut ll, mut rl, mut lpair, mut rpair) = (Vec::new(), Vec::new(), Vec::new(), Vec::new());
        for a in lhs {
            match a {
                Ann::List(q, e) => ll.push((q, &**e)),
                Ann::Pair(x, y) => lpair.push((&**x, &**y)),
                _ => {}
            }
        }
        for a in rhs {
            match a {
                Ann::List(q, e) => rl.push((q, &**e)),
                Ann::Pair(x, y) => rpair.push((&**x, &**y)),
                _ => {}
            }
        }
        if !rl.is_empty() {
            let deg = rl.iter().map(|(q, _)| q.len()).max().unwrap_or(0);
            for i in 0..deg {
                let r: Vec<Option<usize>> = rl.iter().map(|(q, _)| q.get(i).copied()).collect();
                let l: Vec<Option<usize>> = ll.iter().map(|(q, _)| q.get(i).copied()).collect();
                ge(lp, &l, &r, Rat::ZERO);
            }
            let le: Vec<&Ann<usize>> = ll.iter().map(|(_, e)| *e).collect();
            let re: Vec<&Ann<usize>> = rl.iter().map(|(_, e)| *e).collect();
            Self::geq(lp, &le, &re);
        }
        if !rpair.is_empty() {
            let l1: Vec<_> = lpair.iter().map(|p| p.0).collect();
            let r1: Vec<_> = rpair.iter().map(|p| p.0).collect();
            Self::geq(lp, &l1, &r1);
            let l2: Vec<_> = lpair.iter().map(|p| p.1).collect();
            let r2: Vec<_> = rpair.iter().map(|p| p.1).collect();
            Self::geq(lp, &l2, &r2);
        }
    }

    /// Pays for the element annotation `b` out of the potential of value `x`.
    fn into_elem(lp: &mut Lp, ctx: &Ctx, x: &Val, b: &Ann<usize>) {
        for (p, (q, inner)) in b.positions().into_iter().enumerate() {
            let Some(&atom) = x.atoms.get(p) else { continue };
            for (k, v) in q.iter().enumerate() {
                let have = ctx.pot.get(&vec![(atom, k + 1)]).copied();
                ge(lp, &[have], &[Some(*v)], Rat::ZERO);
            }
            Self::geq(lp, &[&x.elems[p]], &[inner]);
        }
    }

    /// Splits variable `x` into two copies. The context keeps `x` for the
    /// second copy; the first is returned. Potential on the copies, including
    /// potential that mixes them, is paid for by the old potential of `x`,
    /// through `C(n, i) · C(n, j) = Σ_k c(k; i, j) · C(n, k)`.
    fn share(&mut self, lp: &mut Lp, ctx: &Ctx, x: &str, d: usize) -> (Ctx, Val) {
        let xv = ctx.get(x).clone();
        let copy = |s: &mut Self, lp: &mut Lp| Val {
            ty: xv.ty.clone(),
            atoms: xv.atoms.iter().map(|_| s.atom()).collect(),
            elems: xv.elems.iter().map(|a| Self::relabel(lp, a)).collect(),
        };
        let c1 = copy(self, lp);
        let c2 = copy(self, lp);
        for p in 0..xv.elems.len() {
            Self::geq(lp, &[&xv.elems[p]], &[&c1.elems[p], &c2.elems[p]]);
        }
        let xatoms: HashSet<usize> = xv.atoms.iter().copied().collect();
        let m = xv.atoms.len();
        let mut others: BTreeSet<Idx> = BTreeSet::new();
        let mut pot = Pot::new();
        for (i, v) in &ctx.pot {
            let o: Idx = i.iter().copied().filter(|(a, _)| !xatoms.contains(a)).collect();
            if o.len() == i.len() {
                pot.insert(i.clone(), *v);
            }
            others.insert(o);
        }
        let mut pays: BTreeMap<Idx, Vec<(usize, Rat)>> = BTreeMap::new();
        let both: Vec<usize> = c1.atoms.iter().chain(&c2.atoms).copied().collect();
        for o in &others {
            for ij in indices(&both, d - degree_of(o)) {
                if ij.is_empty() {
                    continue;
                }
                let at = |atoms: &Vec<usize>, p: usize| ij.iter().find(|(a, _)| *a == atoms[p]).map_or(0, |t| t.1);
                let is: Vec<usize> = (0..m).map(|p| at(&c1.atoms, p)).collect();
                let js: Vec<usize> = (0..m).map(|p| at(&c2.atoms, p)).collect();
                let var = lp.fresh();
                pot.insert(union(o, &ij), var);
                let mut ks: Vec<(Vec<usize>, Rat)> = vec![(Vec::new(), Rat::ONE)];
                for p in 0..m {
                    let mut next = Vec::new();
                    for (k, c) in &ks {
                        for kp in is[p].max(js[p])..=is[p] + js[p] {
                            let coeff = product_coeff(kp, is[p], js[p]);
                            if !coeff.is_zero() {
                                let mut k2 = k.clone();
                                k2.push(kp);
                                next.push((k2, *c * coeff));
                            }
                        }
                    }
                    ks = next;
                }
                for (k, c) in ks {
                    let mut target = o.clone();
                    for (p, kp) in k.iter().enumerate() {
                        if *kp > 0 {
                            target.push((xv.atoms[p], *kp));
                        }
                    }
                    target.sort();
                    pays.entry(target).or_default().push((var, c));
                }
            }
        }
        for (target, terms) in pays {
            let mut row: Linear = terms.into_iter().map(|(v, c)| (v, -c)).collect();
            if let Some(&have) = ctx.pot.get(&target) {
                row.push((have, Rat::ONE));
            }
            lp.add(row, Cmp::Ge, Rat::ZERO);
        }
        let mut out = Ctx { vars: ctx.vars.clone(), pot };
        out.set(x, c2);
        (out, c1)
    }

    /// Makes the variables among `atoms` distinct by sharing repeated ones.
    fn dedupe(&mut self, lp: &mut Lp, mut ctx: Ctx, atoms: &[&Atom], d: usize) -> (Ctx, Vec<Atom>) {
        let mut seen: HashSet<String> = HashSet::new();
        let mut out = Vec::new();
        for (n, a) in atoms.iter().enumerate() {
            match a {
                Atom::Var(x) if !seen.insert(x.clone()) => {
                    let (c, copy) = self.share(lp, &ctx, x, d);
                    let name = format!("%dup{n}:{x}");
                    ctx = c;
                    ctx.set(&name, copy);
                    out.push(Atom::Var(name));
                }
                a => out.push((*a).clone()),
            }
        }
        (ctx, out)
    }

    /// `ctx ⊢ e : res`: the potential of `ctx` pays for `e` and for `res`.
    fn walk(&mut self, cx: &mut Cx, mode: Mode, e: &Core, ctx: &Ctx, res: &Res) {
        let ctx = ctx.restrict(&e.free_vars());
        let d = mode.degree;
        let constant = |c: &Ctx| c.pot.get(&Vec::new()).copied();
        match e {
            Core::Atom(Atom::Var(x)) => {
                let xv = ctx.get(x).clone();
                Self::transfer(&mut cx.lp, &ctx, &[(Some(&xv), &res.val.ty, 0)], res);
            }
            Core::Atom(_) | Core::Prim(..) | Core::Tick(_) => {
                let cost = match e {
                    Core::Tick(r) if !mode.cost_free && self.metric == Metric::Ticks => *r,
                    _ => Rat::ZERO,
                };
                ge(&mut cx.lp, &[constant(&ctx)], &[res.pot.get(&Vec::new()).copied()], cost);
            }
            Core::Cons(..) | Core::Reuse { .. } => {
                let (h, t, cost) = match e {
                    Core::Cons(h, t) => (h.clone(), t.clone(), self.cons_cost(mode.cost_free)),
                    Core::Reuse { head, tail, .. } => (Atom::Var(head.clone()), Atom::Var(tail.clone()), Rat::ZERO),
                    _ => unreachable!(),
                };
                let (ctx, args) = self.dedupe(&mut cx.lp, ctx, &[&h, &t], d);
                let (h, t) = (&args[0], &args[1]);
                let r = res.val.atoms[0];
                let b = &res.val.elems[0];
                let s = t.var().map(|t| ctx.get(t).atoms[0]);
                let out = |k: usize| {
                    if k == 0 { res.pot.get(&Vec::new()).copied() } else { res.pot.get(&vec![(r, k)]).copied() }
                };
                // C(n+1, k) = C(n, k) + C(n, k-1)
                for k in 0..=d {
                    let have = match (k, s) {
                        (0, _) => constant(&ctx),
                        (_, Some(s)) => ctx.pot.get(&vec![(s, k)]).copied(),
                        (_, None) => None,
                    };
                    if k > 0 && s.is_none() {
                        break;
                    }
                    ge(&mut cx.lp, &[have], &[out(k), out(k + 1)], if k == 0 { cost } else { Rat::ZERO });
                }
                if let Some(h) = h.var() {
                    let hv = ctx.get(h).clone();
                    Self::into_elem(&mut cx.lp, &ctx, &hv, b);
                }
                if let Some(t) = t.var() {
                    let tv = ctx.get(t).clone();
                    Self::geq(&mut cx.lp, &[&tv.elems[0]], &[b]);
                }
            }
            Core::Pair(a, b) => {
                let (ctx, args) = self.dedupe(&mut cx.lp, ctx, &[a, b], d);
                let Type::Pair(ta, tb) = &res.val.ty else { unreachable!("a pair builds a pair") };
                let off = positions(ta).len();
                let va = args[0].var().map(|x| ctx.get(x).clone());
                let vb = args[1].var().map(|x| ctx.get(x).clone());
                let parts = [(va.as_ref(), &**ta, 0), (vb.as_ref(), &**tb, off)];
                Self::transfer(&mut cx.lp, &ctx, &parts, res);
            }
            Core::If(_, t, f) => {
                self.walk(cx, mode, t, &ctx, res);
                self.walk(cx, mode, f, &ctx, res);
            }
            Core::Match { x, nil, head, tail, cons } => self.walk_match(cx, mode, ctx, x, nil, head, tail, cons, res),
            Core::Split { x, a, b, body } => {
                let (mut ctx, xv) = if body.free_vars().contains(x) && a.as_ref() != Some(x) && b.as_ref() != Some(x) {
                    self.share(&mut cx.lp, &ctx, x, d)
                } else {
                    let v = ctx.get(x).clone();
                    (ctx.clone(), v)
                };
                let Type::Pair(ta, tb) = &xv.ty else { unreachable!("split of a pair") };
                let na = positions(ta).len();
                let n = xv.atoms.len();
                let part = |t: &Type, from: usize, to: usize| Val {
                    ty: t.clone(),
                    atoms: xv.atoms[from..to].to_vec(),
                    elems: xv.elems[from..to].to_vec(),
                };
                if let Some(a) = a {
                    ctx.set(a, part(ta, 0, na));
                }
                if let Some(b) = b {
                    ctx.set(b, part(tb, na, n));
                }
                self.walk(cx, mode, body, &ctx, res);
            }
            Core::Let { x, ty, e1, e2 } => self.walk_let(cx, mode, ctx, x, ty, e1, e2, res),
            Core::App(g, args) => self.walk_app(cx, mode, ctx, *g, args, res),
            Core::Fail(_) => {}
        }
    }

    /// Moves the potential of `parts` into `res`. Each part is a value, its
    /// type inside the result, and the offset of its positions there.
    /// A part without a value is a literal: its lists are empty, so the
    /// terms that involve them vanish.
    fn transfer(lp: &mut Lp, ctx: &Ctx, parts: &[(Option<&Val>, &Type, usize)], res: &Res) {
        let mut map: HashMap<usize, usize> = HashMap::new();
        let mut matched = HashSet::new();
        let mut empty: HashSet<usize> = HashSet::new();
        for (v, t, off) in parts {
            match v {
                Some(v) => {
                    for (i, j) in correspond(&v.ty, t) {
                        map.insert(res.val.atoms[off + j], v.atoms[i]);
                        matched.insert(off + j);
                        Self::geq(lp, &[&v.elems[i]], &[&res.val.elems[off + j]]);
                    }
                }
                None => {
                    for j in 0..positions(t).len() {
                        matched.insert(off + j);
                        empty.insert(res.val.atoms[off + j]);
                    }
                }
            }
        }
        for j in 0..res.val.elems.len() {
            if !matched.contains(&j) {
                Self::geq(lp, &[], &[&res.val.elems[j]]);
            }
        }
        for (beta, v) in &res.pot {
            if beta.iter().any(|(a, _)| empty.contains(a)) {
                continue;
            }
            let alpha: Option<Idx> = beta.iter().map(|(a, k)| map.get(a).map(|b| (*b, *k))).collect();
            let have = alpha.and_then(|mut a| {
                a.sort();
                ctx.pot.get(&a).copied()
            });
            ge(lp, &[have], &[Some(*v)], Rat::ZERO);
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn walk_match(
        &mut self,
        cx: &mut Cx,
        mode: Mode,
        ctx: Ctx,
        x: &str,
        nil: &Core,
        head: &Option<String>,
        tail: &Option<String>,
        cons: &Core,
        res: &Res,
    ) {
        let d = mode.degree;
        let mut rest = nil.free_vars();
        for v in cons.free_vars() {
            if Some(&v) != head.as_ref() && Some(&v) != tail.as_ref() {
                rest.insert(v);
            }
        }
        let (mut ctx, xv) = if rest.contains(x) {
            self.share(&mut cx.lp, &ctx, x, d)
        } else {
            let v = ctx.get(x).clone();
            let mut c = ctx.clone();
            c.vars.retain(|(y, _)| y != x);
            (c, v)
        };
        let s = xv.atoms[0];
        let elem = xv.elems[0].clone();
        // []: the terms that involve the length of `x` vanish.
        let nil_ctx = Ctx {
            vars: ctx.vars.clone(),
            pot: ctx.pot.iter().filter(|(i, _)| i.iter().all(|(a, _)| *a != s)).map(|(i, v)| (i.clone(), *v)).collect(),
        };
        self.walk(cx, mode, nil, &nil_ctx, res);
        // h :: t: C(n+1, k) = C(n, k) + C(n, k-1), for every other index.
        let Type::List(elem_ty) = &xv.ty else { unreachable!("match on a list") };
        let t_atom = self.atom();
        let mut pot = Pot::new();
        let mut bases: BTreeSet<Idx> = BTreeSet::new();
        for i in ctx.pot.keys() {
            bases.insert(i.iter().copied().filter(|(a, _)| *a != s).collect());
        }
        for base in bases {
            let top = if tail.is_some() { d - degree_of(&base) } else { 0 };
            for k in 0..=top {
                let with = |k: usize| {
                    let mut i = base.clone();
                    if k > 0 {
                        i.push((s, k));
                        i.sort();
                    }
                    ctx.pot.get(&i).copied()
                };
                let (a, b) = (with(k), with(k + 1));
                if a.is_none() && b.is_none() {
                    continue;
                }
                let v = cx.lp.fresh();
                let mut row = lin(&[(v, 1)]);
                for w in [a, b].into_iter().flatten() {
                    row.push((w, -Rat::ONE));
                }
                cx.lp.add(row, Cmp::Le, Rat::ZERO);
                let mut i = base.clone();
                if k > 0 {
                    i.push((t_atom, k));
                    i.sort();
                }
                pot.insert(i, v);
            }
        }
        if let Some(h) = head {
            // The head has one element's worth of potential.
            let hv = Val {
                ty: (**elem_ty).clone(),
                atoms: positions(elem_ty).iter().map(|_| self.atom()).collect(),
                elems: elem.positions().into_iter().map(|(_, inner)| inner.clone()).collect(),
            };
            for (p, (q, _)) in elem.positions().into_iter().enumerate() {
                for (k, v) in q.iter().enumerate() {
                    pot.insert(vec![(hv.atoms[p], k + 1)], *v);
                }
            }
            ctx.set(h, hv);
        }
        if let Some(t) = tail {
            ctx.set(t, Val { ty: xv.ty.clone(), atoms: vec![t_atom], elems: vec![elem.clone()] });
        }
        ctx.pot = pot;
        self.walk(cx, mode, cons, &ctx, res);
    }

    #[allow(clippy::too_many_arguments)]
    fn walk_let(
        &mut self,
        cx: &mut Cx,
        mode: Mode,
        ctx: Ctx,
        x: &Option<String>,
        ty: &Type,
        e1: &Core,
        e2: &Core,
        res: &Res,
    ) {
        let d = mode.degree;
        let fv1 = e1.free_vars();
        let mut fv2 = e2.free_vars();
        if let Some(x) = x {
            fv2.remove(x);
        }
        let mut ctx = ctx;
        let mut firsts: Vec<(String, Val)> = Vec::new();
        let names: Vec<String> = ctx.vars.iter().map(|(y, _)| y.clone()).collect();
        for y in names {
            if fv1.contains(&y) && fv2.contains(&y) {
                let (c, copy) = self.share(&mut cx.lp, &ctx, &y, d);
                ctx = c;
                firsts.push((y, copy));
            }
        }
        let mut vars1: Vec<(String, Val)> =
            ctx.vars.iter().filter(|(y, _)| fv1.contains(y) && !fv2.contains(y)).cloned().collect();
        vars1.extend(firsts);
        let vars2: Vec<(String, Val)> = ctx.vars.iter().filter(|(y, _)| fv2.contains(y)).cloned().collect();
        let atoms1: HashSet<usize> = vars1.iter().flat_map(|(_, v)| v.atoms.iter().copied()).collect();
        let atoms2: HashSet<usize> = vars2.iter().flat_map(|(_, v)| v.atoms.iter().copied()).collect();
        let mut p1 = Pot::new();
        let mut r2 = Pot::new();
        let mut mixed: BTreeMap<Idx, Pot> = BTreeMap::new();
        for (i, v) in &ctx.pot {
            let a1: Idx = i.iter().copied().filter(|(a, _)| atoms1.contains(a)).collect();
            let a2: Idx = i.iter().copied().filter(|(a, _)| atoms2.contains(a)).collect();
            if a1.len() + a2.len() != i.len() {
                continue;
            }
            match (a1.is_empty(), a2.is_empty()) {
                (_, true) => {
                    p1.insert(a1, *v);
                }
                (true, false) => {
                    r2.insert(a2, *v);
                }
                (false, false) => {
                    mixed.entry(a2).or_default().insert(a1, *v);
                }
            }
        }
        let v1 = self.val(&mut cx.lp, ty, Some(d));
        let res1 = Res { pot: Self::fresh_pot(&mut cx.lp, &v1.atoms, d), val: v1 };
        self.walk(cx, mode, e1, &Ctx { vars: vars1.clone(), pot: p1 }, &res1);
        for (b, v) in &res1.pot {
            r2.insert(b.clone(), *v);
        }
        // Potential that mixes the two sides goes through `e1` cost-free,
        // one typing for each mixed index of the second side.
        for (a2, mut pot) in mixed {
            let dd = d - degree_of(&a2);
            // The slice of the context's potential along `a2` includes its constant.
            if let Some(q) = r2.remove(&a2) {
                pot.insert(Vec::new(), q);
            }
            let zero = |lp: &mut Lp, v: &Val| Val {
                ty: v.ty.clone(),
                atoms: v.atoms.clone(),
                elems: positions(&v.ty).iter().map(|t| Self::ann(lp, t, None)).collect(),
            };
            let vars: Vec<(String, Val)> = vars1.iter().map(|(y, v)| (y.clone(), zero(&mut cx.lp, v))).collect();
            let rv = zero(&mut cx.lp, &res1.val);
            let rs = Res { pot: Self::fresh_pot(&mut cx.lp, &rv.atoms, dd), val: rv };
            self.walk(cx, Mode { degree: dd, cost_free: true }, e1, &Ctx { vars, pot }, &rs);
            for (b, v) in &rs.pot {
                r2.insert(union(&a2, b), *v);
            }
        }
        let mut ctx2 = Ctx { vars: vars2, pot: r2 };
        if let Some(x) = x {
            ctx2.set(x, res1.val.clone());
        }
        self.walk(cx, mode, e2, &ctx2, res);
    }

    fn walk_app(&mut self, cx: &mut Cx, mode: Mode, ctx: Ctx, g: usize, args: &[Atom], res: &Res) {
        let refs: Vec<&Atom> = args.iter().collect();
        let (ctx, args) = self.dedupe(&mut cx.lp, ctx, &refs, mode.degree);
        let mut pieces: Vec<Sig> = Vec::new();
        if self.scc_of[g] == cx.scc && mode == cx.mode {
            pieces.push(cx.sigs[&g].clone());
            if mode.degree >= 1 {
                let t = self.template(cx.scc, Mode { degree: mode.degree - 1, cost_free: true });
                let off = cx.lp.embed(&t.lp);
                pieces.push(t.sigs[&g].shift(off));
            }
        } else {
            let t = self.template(self.scc_of[g], mode);
            let off = cx.lp.embed(&t.lp);
            pieces.push(t.sigs[&g].shift(off));
        }
        // Arguments: the callee's potential is paid from the caller's
        // corresponding index. Indices on a literal `[]` vanish.
        let mut wants: BTreeMap<Idx, Vec<Option<usize>>> = BTreeMap::new();
        for p in &pieces {
            let mut map = HashMap::new();
            for (a, pv) in args.iter().zip(&p.params) {
                if let Some(x) = a.var() {
                    let xv = ctx.get(x);
                    for (i, j) in correspond(&xv.ty, &pv.ty) {
                        map.insert(pv.atoms[j], xv.atoms[i]);
                    }
                }
            }
            for (alpha, v) in &p.pot {
                if alpha.is_empty() {
                    continue;
                }
                let caller: Option<Idx> = alpha.iter().map(|(a, k)| map.get(a).map(|b| (*b, *k))).collect();
                if let Some(mut caller) = caller {
                    caller.sort();
                    wants.entry(caller).or_default().push(Some(*v));
                }
            }
        }
        for (caller, rhs) in wants {
            let have = ctx.pot.get(&caller).copied();
            ge(&mut cx.lp, &[have], &rhs, Rat::ZERO);
        }
        for (n, a) in args.iter().enumerate() {
            let Some(x) = a.var() else { continue };
            let xv = ctx.get(x).clone();
            for (i, j) in correspond(&xv.ty, &pieces[0].params[n].ty) {
                let targets: Vec<&Ann<usize>> = pieces.iter().map(|p| &p.params[n].elems[j]).collect();
                Self::geq(&mut cx.lp, &[&xv.elems[i]], &targets);
            }
        }
        // Constants: enough to make the call, and what is left after it.
        let k = self.call_cost(mode.cost_free);
        let mut enough: Linear = Vec::new();
        let mut left: Linear = Vec::new();
        if let Some(&c) = ctx.pot.get(&Vec::new()) {
            enough.push((c, Rat::ONE));
            left.push((c, Rat::ONE));
        }
        for p in &pieces {
            if let Some(&b) = p.pot.get(&Vec::new()) {
                enough.push((b, -Rat::ONE));
                left.push((b, -Rat::ONE));
            }
            if let Some(&a) = p.ret_pot.get(&Vec::new()) {
                left.push((a, Rat::ONE));
            }
        }
        if let Some(&r0) = res.pot.get(&Vec::new()) {
            left.push((r0, -Rat::ONE));
        }
        cx.lp.add(enough, Cmp::Ge, k);
        cx.lp.add(left, Cmp::Ge, k);
        // The result.
        let rmap = correspond(&pieces[0].ret.ty, &res.val.ty);
        let mut matched = HashSet::new();
        for (i, j) in &rmap {
            matched.insert(*j);
            let srcs: Vec<&Ann<usize>> = pieces.iter().map(|p| &p.ret.elems[*i]).collect();
            Self::geq(&mut cx.lp, &srcs, &[&res.val.elems[*j]]);
        }
        for j in 0..res.val.elems.len() {
            if !matched.contains(&j) {
                Self::geq(&mut cx.lp, &[], &[&res.val.elems[j]]);
            }
        }
        for (beta, v) in &res.pot {
            if beta.is_empty() {
                continue;
            }
            let mut srcs = Vec::new();
            for p in &pieces {
                let back: HashMap<usize, usize> =
                    rmap.iter().map(|(i, j)| (res.val.atoms[*j], p.ret.atoms[*i])).collect();
                let idx: Option<Idx> = beta.iter().map(|(a, k)| back.get(a).map(|b| (*b, *k))).collect();
                if let Some(mut idx) = idx {
                    idx.sort();
                    srcs.push(p.ret_pot.get(&idx).copied());
                }
            }
            ge(&mut cx.lp, &srcs, &[Some(*v)], Rat::ZERO);
        }
    }

    fn template(&mut self, scc: usize, mode: Mode) -> Rc<Template> {
        if let Some(t) = self.memo.get(&(scc, mode)) {
            return t.clone();
        }
        let mut cx = Cx { lp: Lp::default(), sigs: HashMap::new(), scc, mode };
        let fns = self.sccs[scc].clone();
        let d = mode.degree;
        for &f in &fns {
            let def = &self.m.fns[f];
            let params: Vec<Val> = def.params.iter().map(|(_, t)| self.val(&mut cx.lp, t, Some(d))).collect();
            let atoms: Vec<usize> = params.iter().flat_map(|v| v.atoms.iter().copied()).collect();
            let pot = Self::fresh_pot(&mut cx.lp, &atoms, d);
            let ret = self.val(&mut cx.lp, &def.ret, Some(d));
            let ret_pot = Self::fresh_pot(&mut cx.lp, &ret.atoms, d);
            cx.sigs.insert(f, Sig { params, pot, ret, ret_pot });
        }
        for &f in &fns {
            let def = &self.m.fns[f];
            let sig = cx.sigs[&f].clone();
            let ctx = Ctx {
                vars: def.params.iter().map(|(x, _)| x.clone()).zip(sig.params.iter().cloned()).collect(),
                pot: sig.pot.clone(),
            };
            let res = Res { val: sig.ret.clone(), pot: sig.ret_pot.clone() };
            self.walk(&mut cx, mode, &def.body, &ctx, &res);
        }
        let t = Rc::new(Template { lp: cx.lp, sigs: cx.sigs });
        self.memo.insert((scc, mode), t.clone());
        t
    }

    /// The constraints of a call of `f` at this degree, and its signature.
    pub fn instance(&mut self, f: usize, degree: usize) -> (Lp, Sig) {
        let t = self.template(self.scc_of[f], Mode { degree, cost_free: false });
        (t.lp.clone(), t.sigs[&f].clone())
    }

    /// Minimizes the bound: the coefficients of the highest degree first,
    /// then lower ones, then the constant.
    pub fn objectives(sig: &Sig, degree: usize) -> Vec<Linear> {
        let mut objs: Vec<Linear> = Vec::new();
        for k in (1..=degree).rev() {
            let mut o = Linear::new();
            for (i, v) in &sig.pot {
                if degree_of(i) == k {
                    o.push((*v, Rat::ONE));
                }
            }
            for p in &sig.params {
                for e in &p.elems {
                    for (j, v) in e.annotations() {
                        if j == k {
                            o.push((v, Rat::ONE));
                        }
                    }
                }
            }
            if !o.is_empty() {
                objs.push(o);
            }
        }
        if let Some(&c) = sig.pot.get(&Vec::new()) {
            objs.push(vec![(c, Rat::ONE)]);
        }
        objs
    }

    fn read_bound(&self, f: usize, sig: &Sig, x: &[Rat], degree: usize) -> Bound {
        let types: Vec<Type> = self.m.fns[f].params.iter().map(|(_, t)| t.clone()).collect();
        let positions = param_positions(&types);
        let atoms: Vec<usize> = sig.params.iter().flat_map(|v| v.atoms.iter().copied()).collect();
        let index: HashMap<usize, usize> = atoms.iter().enumerate().map(|(i, a)| (*a, i)).collect();
        let mut terms = Vec::new();
        for (i, v) in &sig.pot {
            if i.is_empty() || x[*v].is_zero() {
                continue;
            }
            let mut t: Vec<(usize, usize)> = i.iter().map(|(a, k)| (index[a], *k)).collect();
            t.sort();
            terms.push((t, x[*v]));
        }
        let elems = sig.params.iter().flat_map(|v| v.elems.iter().map(|a| a.map(&|w| x[w]))).collect();
        let c = sig.pot.get(&Vec::new()).map_or(Rat::ZERO, |v| x[*v]);
        Bound { degree, positions, terms, elems, constant: c + self.call_cost(false) }
    }

    /// Finds the least bound of the least degree, up to `max_degree`.
    pub fn bound(&mut self, f: usize, max_degree: usize) -> Result<Option<Bound>> {
        for d in 0..=max_degree {
            if let Some(b) = self.bound_with(f, d, |_, _| {})? {
                return Ok(Some(b));
            }
        }
        Ok(None)
    }

    /// The least bound at a fixed degree, under extra constraints on the signature.
    pub fn bound_with(&mut self, f: usize, degree: usize, extra: impl Fn(&mut Lp, &Sig)) -> Result<Option<Bound>> {
        let (mut lp, sig) = self.instance(f, degree);
        extra(&mut lp, &sig);
        let objs = Self::objectives(&sig, degree);
        Ok(match solve(&lp, &objs)? {
            Outcome::Infeasible => None,
            Outcome::Optimal(x) => Some(self.read_bound(f, &sig, &x, degree)),
        })
    }
}

fn solve(lp: &Lp, objs: &[Linear]) -> Result<Outcome> {
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| lp.solve(objs)));
    r.map_err(|e| {
        let msg = e
            .downcast_ref::<&str>()
            .map(|s| s.to_string())
            .or_else(|| e.downcast_ref::<String>().cloned())
            .unwrap_or_else(|| "the linear program failed".into());
        Error::new(msg)
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn product_of_binomials() {
        for i in 0..4 {
            for j in 0..4 {
                for n in 0..9i128 {
                    let lhs = Rat::binom(n, i) * Rat::binom(n, j);
                    let rhs: Rat = (0..=i + j).map(|k| product_coeff(k, i, j) * Rat::binom(n, k)).sum();
                    assert_eq!(lhs, rhs, "i={i} j={j} n={n}");
                }
            }
        }
    }

    #[test]
    fn index_count() {
        // Monomials of degree ≤ 2 in 3 variables: C(5, 2) = 10.
        assert_eq!(indices(&[1, 2, 3], 2).len(), 10);
    }
}

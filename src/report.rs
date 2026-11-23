//! Writing bounds the way people read them, and checking declared budgets.

use crate::aara::{Analyzer, Ann, Bound, Position, degree_of, param_positions};
use crate::core::CoreFn;
use crate::error::{Error, Result};
use crate::lp::Cmp;
use crate::poly::Poly;
use crate::rat::Rat;
use crate::syntax::{Budget, Type};
use std::collections::{BTreeMap, HashMap};

const SUPERSCRIPTS: [char; 10] = ['⁰', '¹', '²', '³', '⁴', '⁵', '⁶', '⁷', '⁸', '⁹'];

fn power(base: &str, k: usize) -> String {
    if k == 1 {
        return base.to_string();
    }
    let sup: String = k.to_string().chars().map(|c| SUPERSCRIPTS[c.to_digit(10).unwrap() as usize]).collect();
    format!("{base}{sup}")
}

// ---------------------------------------------------------------- polynomials in several sizes

/// A monomial: `(variable, exponent)` pairs sorted by variable.
type Mono = Vec<(usize, usize)>;

/// A polynomial in several sizes, in the monomial basis.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct MPoly(pub BTreeMap<Mono, Rat>);

impl MPoly {
    fn add_term(&mut self, m: Mono, c: Rat) {
        let e = self.0.entry(m.clone()).or_insert(Rat::ZERO);
        *e = *e + c;
        if e.is_zero() {
            self.0.remove(&m);
        }
    }

    fn mul(&self, o: &MPoly) -> MPoly {
        let mut out = MPoly::default();
        for (a, x) in &self.0 {
            for (b, y) in &o.0 {
                let mut m: BTreeMap<usize, usize> = a.iter().copied().collect();
                for (v, e) in b {
                    *m.entry(*v).or_insert(0) += e;
                }
                out.add_term(m.into_iter().collect(), *x * *y);
            }
        }
        out
    }

    fn one() -> MPoly {
        let mut p = MPoly::default();
        p.add_term(Vec::new(), Rat::ONE);
        p
    }

    fn of_univariate(var: usize, p: &Poly) -> MPoly {
        let mut out = MPoly::default();
        for (k, c) in p.0.iter().enumerate() {
            if !c.is_zero() {
                out.add_term(if k == 0 { Vec::new() } else { vec![(var, k)] }, *c);
            }
        }
        out
    }

    /// `Π C(n_v, k_v)` in the monomial basis.
    fn of_binomials(term: &[(usize, usize)]) -> MPoly {
        term.iter().fold(MPoly::one(), |acc, (v, k)| acc.mul(&MPoly::of_univariate(*v, &Poly::binomial(*k))))
    }

    fn degree(m: &Mono) -> usize {
        m.iter().map(|t| t.1).sum()
    }
}

fn position_name(p: &Position, params: &[(String, Type)]) -> String {
    let mut s = params[p.param].0.clone();
    for step in &p.path {
        s.push_str(if *step == 0 { ".0" } else { ".1" });
    }
    s
}

fn show_mono(m: &Mono, names: &[String]) -> String {
    m.iter().map(|(v, e)| power(&format!("|{}|", names[*v]), *e)).collect::<Vec<_>>().join("·")
}

/// A sum of terms `(degree, coeff, text)`, written highest degree first.
fn show_terms(mut terms: Vec<(usize, Rat, String)>, constant: Rat) -> String {
    terms.sort_by_key(|t| std::cmp::Reverse(t.0));
    let mut parts: Vec<(Rat, String)> = terms.into_iter().map(|(_, c, t)| (c, t)).collect();
    if !constant.is_zero() || parts.is_empty() {
        parts.push((constant, String::new()));
    }
    let mut out = String::new();
    for (i, (c, t)) in parts.iter().enumerate() {
        let mag = c.abs();
        let body = if t.is_empty() {
            mag.to_string()
        } else if mag == Rat::ONE {
            t.clone()
        } else {
            format!("{mag}·{t}")
        };
        let sign = match (i, c.is_neg()) {
            (0, true) => "-",
            (0, false) => "",
            (_, true) => " - ",
            (_, false) => " + ",
        };
        out.push_str(sign);
        out.push_str(&body);
    }
    out
}

fn element_name(depth: usize, avoid: &[String]) -> String {
    ["x", "y", "z", "u", "v", "w"]
        .iter()
        .map(|s| s.to_string())
        .filter(|s| !avoid.contains(s))
        .nth(depth)
        .unwrap_or_else(|| format!("x{depth}"))
}

/// The terms of the element potential `a` of the list written `name`.
fn describe_elems(a: &Ann<Rat>, name: &str, depth: usize, avoid: &[String], out: &mut Vec<(usize, Rat, String)>) {
    let y = element_name(depth, avoid);
    let mut inner = Vec::new();
    describe(a, &y, depth + 1, avoid, &mut inner);
    if !inner.is_empty() {
        let deg = inner.iter().map(|t| t.0).max().unwrap_or(0) + 1;
        let text = show_terms(inner, Rat::ZERO);
        let text = if text.contains(' ') { format!("({text})") } else { text };
        out.push((deg, Rat::ONE, format!("Σ_{{{y}∈{name}}} {text}")));
    }
}

/// The terms of the potential of a value written `name` at annotation `a`.
fn describe(a: &Ann<Rat>, name: &str, depth: usize, avoid: &[String], out: &mut Vec<(usize, Rat, String)>) {
    match a {
        Ann::Base | Ann::Param => {}
        Ann::Pair(x, y) => {
            describe(x, &format!("{name}.0"), depth, avoid, out);
            describe(y, &format!("{name}.1"), depth, avoid, out);
        }
        Ann::List(q, e) => {
            let p = Poly::from_binomial(q);
            for (k, c) in p.0.iter().enumerate().skip(1) {
                if !c.is_zero() {
                    out.push((k, *c, power(&format!("|{name}|"), k)));
                }
            }
            describe_elems(e, name, depth, avoid, out);
        }
    }
}

fn bound_poly(b: &Bound) -> MPoly {
    let mut p = MPoly::default();
    for (term, c) in &b.terms {
        for (m, x) in MPoly::of_binomials(term).0 {
            p.add_term(m, x * *c);
        }
    }
    p
}

pub fn show_bound(b: &Bound, params: &[(String, Type)]) -> String {
    let avoid: Vec<String> = params.iter().map(|(x, _)| x.clone()).collect();
    let names: Vec<String> = b.positions.iter().map(|p| position_name(p, params)).collect();
    let poly = bound_poly(b);
    let mut constant = b.constant;
    let mut terms = Vec::new();
    for (m, c) in &poly.0 {
        if m.is_empty() {
            constant = constant + *c;
        } else {
            terms.push((MPoly::degree(m), *c, show_mono(m, &names)));
        }
    }
    for (e, name) in b.elems.iter().zip(&names) {
        describe_elems(e, name, 0, &avoid, &mut terms);
    }
    show_terms(terms, constant)
}

fn leads(a: &Ann<Rat>, name: &str, depth: usize, avoid: &[String], out: &mut Vec<String>) {
    match a {
        Ann::Base | Ann::Param => {}
        Ann::Pair(x, y) => {
            leads(x, &format!("{name}.0"), depth, avoid, out);
            leads(y, &format!("{name}.1"), depth, avoid, out);
        }
        Ann::List(q, e) => {
            if let Some(k) = Poly::from_binomial(q).degree().filter(|k| *k > 0) {
                out.push(power(&format!("|{name}|"), k));
            }
            elem_leads(e, name, depth, avoid, out);
        }
    }
}

fn elem_leads(e: &Ann<Rat>, name: &str, depth: usize, avoid: &[String], out: &mut Vec<String>) {
    let y = element_name(depth, avoid);
    let mut inner = Vec::new();
    leads(e, &y, depth + 1, avoid, &mut inner);
    for t in inner {
        out.push(format!("Σ_{{{y}∈{name}}} {t}"));
    }
}

/// The growth of a bound: its terms of highest degree, and the leading terms
/// of the element potential.
pub fn show_order(b: &Bound, params: &[(String, Type)]) -> String {
    let avoid: Vec<String> = params.iter().map(|(x, _)| x.clone()).collect();
    let names: Vec<String> = b.positions.iter().map(|p| position_name(p, params)).collect();
    let poly = bound_poly(b);
    let top = poly.0.keys().map(MPoly::degree).max().unwrap_or(0);
    let mut out: Vec<String> = Vec::new();
    if top > 0 {
        for m in poly.0.keys().filter(|m| MPoly::degree(m) == top) {
            out.push(show_mono(m, &names));
        }
    }
    for (e, name) in b.elems.iter().zip(&names) {
        elem_leads(e, name, 0, &avoid, &mut out);
    }
    if out.is_empty() { "O(1)".into() } else { format!("O({})", out.join(" + ")) }
}

// ---------------------------------------------------------------- budgets

/// A declared budget as a polynomial in the lengths of the list parameters.
pub struct SplitBudget {
    /// Monomial coefficients, over the indices of the parameters' positions.
    pub poly: MPoly,
    pub degree: usize,
}

pub fn split_budget(f: &CoreFn, b: &Budget) -> Result<SplitBudget> {
    let types: Vec<Type> = f.params.iter().map(|(_, t)| t.clone()).collect();
    let positions = param_positions(&types);
    let mut poly = MPoly::default();
    for m in &b.terms {
        let mut exps: BTreeMap<usize, usize> = BTreeMap::new();
        for (x, k) in &m.sizes {
            let Some(i) = f.params.iter().position(|(y, _)| y == x) else {
                return Err(Error::at(b.pos, format!("`{x}` is not a parameter of `{}`", f.name)));
            };
            let Some(p) = positions.iter().position(|p| p.param == i && p.path.is_empty()) else {
                return Err(Error::at(b.pos, format!("`|{x}|` is the length of a list, but `{x}` is not a list")));
            };
            *exps.entry(p).or_insert(0) += k;
        }
        poly.add_term(exps.into_iter().collect(), m.coeff);
    }
    let degree = poly.0.keys().map(MPoly::degree).max().unwrap_or(0);
    Ok(SplitBudget { poly, degree })
}

pub fn show_budget(f: &CoreFn, s: &SplitBudget) -> String {
    let types: Vec<Type> = f.params.iter().map(|(_, t)| t.clone()).collect();
    let names: Vec<String> = param_positions(&types).iter().map(|p| position_name(p, &f.params)).collect();
    let mut constant = Rat::ZERO;
    let mut terms = Vec::new();
    for (m, c) in &s.poly.0 {
        if m.is_empty() {
            constant = *c;
        } else {
            terms.push((MPoly::degree(m), *c, show_mono(m, &names)));
        }
    }
    show_terms(terms, constant)
}

/// The budget in the basis of products of binomials.
fn budget_binomial(s: &SplitBudget) -> HashMap<Vec<(usize, usize)>, Rat> {
    let mut out: HashMap<Vec<(usize, usize)>, Rat> = HashMap::new();
    for (m, c) in &s.poly.0 {
        // Expand each n^k into binomials and multiply out.
        let mut acc: Vec<(Vec<(usize, usize)>, Rat)> = vec![(Vec::new(), *c)];
        for (v, e) in m {
            let mut mono = vec![Rat::ZERO; e + 1];
            mono[*e] = Rat::ONE;
            let (c0, b) = Poly(mono).to_binomial();
            let mut next = Vec::new();
            for (t, x) in &acc {
                if !c0.is_zero() {
                    next.push((t.clone(), *x * c0));
                }
                for (j, y) in b.iter().enumerate() {
                    if !y.is_zero() {
                        let mut t2 = t.clone();
                        t2.push((*v, j + 1));
                        next.push((t2, *x * *y));
                    }
                }
            }
            acc = next;
        }
        for (t, x) in acc {
            let e = out.entry(t).or_insert(Rat::ZERO);
            *e = *e + x;
        }
    }
    out
}

/// `bound ≤ budget` for all inputs, decided exactly when both are sums of
/// one-list polynomials and the elements carry no potential.
fn within_exactly(bound: &Bound, s: &SplitBudget) -> bool {
    if bound.elems.iter().any(|e| e.annotations().iter().any(|(_, c)| !c.is_zero())) {
        return false;
    }
    if bound.terms.iter().any(|(t, _)| t.len() > 1) || s.poly.0.keys().any(|m| m.len() > 1) {
        return false;
    }
    let n = bound.positions.len();
    let mut diff = vec![Poly::zero(); n];
    let mut slack = -bound.constant;
    for (m, c) in &s.poly.0 {
        match m.first() {
            None => slack = slack + *c,
            Some((v, e)) => {
                let mut p = vec![Rat::ZERO; e + 1];
                p[*e] = *c;
                diff[*v] = diff[*v].add(&Poly(p));
            }
        }
    }
    for (t, c) in &bound.terms {
        let (v, k) = t[0];
        diff[v] = diff[v].add(&Poly::binomial(k).scale(-*c));
    }
    for d in diff {
        match d.min_on_naturals() {
            Some(m) => slack = slack + m,
            None => return false,
        }
    }
    !slack.is_neg()
}

pub enum Verdict {
    Within,
    Exceeds,
}

/// Checks a function against its budget. `best` is the bound found without one.
pub fn check_budget(
    an: &mut Analyzer,
    index: usize,
    s: &SplitBudget,
    best: Option<&Bound>,
    max_degree: usize,
) -> Result<Verdict> {
    if let Some(b) = best
        && within_exactly(b, s)
    {
        return Ok(Verdict::Within);
    }
    // Otherwise look for a bound under the budget coefficient by coefficient
    // in the binomial basis, which implies that it fits for every input.
    let caps = budget_binomial(s);
    let degree = s.degree.max(best.map_or(0, |b| b.degree)).min(max_degree.max(s.degree));
    let call = an.call_constant();
    let found = an.bound_with(index, degree, |lp, sig| {
        let atoms: Vec<usize> = sig.params.iter().flat_map(|v| v.atoms.iter().copied()).collect();
        let pos: HashMap<usize, usize> = atoms.iter().enumerate().map(|(i, a)| (*a, i)).collect();
        for (i, v) in &sig.pot {
            let mut key: Vec<(usize, usize)> = i.iter().map(|(a, k)| (pos[a], *k)).collect();
            key.sort();
            let mut cap = caps.get(&key).copied().unwrap_or(Rat::ZERO);
            if degree_of(i) == 0 {
                cap = cap - call;
            }
            lp.add(vec![(*v, Rat::ONE)], Cmp::Le, cap);
        }
        for p in &sig.params {
            for e in &p.elems {
                for (_, v) in e.annotations() {
                    lp.add(vec![(v, Rat::ONE)], Cmp::Le, Rat::ZERO);
                }
            }
        }
    })?;
    Ok(if found.is_some() { Verdict::Within } else { Verdict::Exceeds })
}

//! A small exact linear-programming solver.
//!
//! Sparse tableau simplex over exact rationals with two phases and Bland's
//! rule as a fallback against cycling. Several objectives are minimized
//! lexicographically: after each optimum, every nonbasic column with a
//! positive reduced cost is fixed at zero, which keeps that optimum while
//! the next objective is minimized.

use crate::rat::Rat;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Cmp {
    Le,
    Ge,
    Eq,
}

#[derive(Clone, Debug)]
pub struct Constraint {
    pub terms: Vec<(usize, Rat)>,
    pub cmp: Cmp,
    pub rhs: Rat,
}

/// A system of linear constraints over variables that are all `≥ 0`.
#[derive(Clone, Debug, Default)]
pub struct Lp {
    pub nvars: usize,
    pub rows: Vec<Constraint>,
}

pub type Linear = Vec<(usize, Rat)>;

#[derive(Debug, PartialEq, Eq)]
pub enum Outcome {
    Optimal(Vec<Rat>),
    Infeasible,
}

impl Lp {
    pub fn fresh(&mut self) -> usize {
        self.nvars += 1;
        self.nvars - 1
    }

    pub fn add(&mut self, terms: Linear, cmp: Cmp, rhs: Rat) {
        self.rows.push(Constraint { terms, cmp, rhs });
    }

    /// Appends a copy of `other` with its variables renumbered; returns the offset.
    pub fn embed(&mut self, other: &Lp) -> usize {
        let off = self.nvars;
        self.nvars += other.nvars;
        for c in &other.rows {
            self.rows.push(Constraint {
                terms: c.terms.iter().map(|&(v, q)| (v + off, q)).collect(),
                cmp: c.cmp,
                rhs: c.rhs,
            });
        }
        off
    }

    /// Minimizes each objective in turn, keeping the optima of the earlier ones.
    pub fn solve(&self, objectives: &[Linear]) -> Outcome {
        match Tableau::build(self) {
            None => Outcome::Infeasible,
            Some(mut t) => {
                if !t.phase_one() {
                    return Outcome::Infeasible;
                }
                for obj in objectives {
                    t.optimize(obj);
                }
                Outcome::Optimal(t.values(self.nvars))
            }
        }
    }
}

type Row = Vec<(usize, Rat)>;

struct Tableau {
    rows: Vec<Row>,
    rhs: Vec<Rat>,
    basis: Vec<usize>,
    ncols: usize,
    is_basic: Vec<bool>,
    banned: Vec<bool>,
    artificial: Vec<bool>,
    cost: Vec<Rat>,
    z: Rat,
}

fn normalize(terms: &[(usize, Rat)]) -> Row {
    let mut t: Row = terms.iter().copied().filter(|(_, q)| !q.is_zero()).collect();
    t.sort_by_key(|(v, _)| *v);
    let mut out: Row = Vec::with_capacity(t.len());
    for (v, q) in t {
        match out.last_mut() {
            Some((w, p)) if *w == v => *p = *p + q,
            _ => out.push((v, q)),
        }
    }
    out.retain(|(_, q)| !q.is_zero());
    out
}

fn coef(row: &Row, c: usize) -> Rat {
    match row.binary_search_by_key(&c, |(v, _)| *v) {
        Ok(i) => row[i].1,
        Err(_) => Rat::ZERO,
    }
}

/// `a - f·b` for sorted sparse rows.
fn axpy(a: &Row, f: Rat, b: &Row) -> Row {
    let mut out = Vec::with_capacity(a.len() + b.len());
    let (mut i, mut j) = (0, 0);
    while i < a.len() || j < b.len() {
        if j == b.len() || (i < a.len() && a[i].0 < b[j].0) {
            out.push(a[i]);
            i += 1;
        } else if i == a.len() || b[j].0 < a[i].0 {
            out.push((b[j].0, -(f * b[j].1)));
            j += 1;
        } else {
            let q = a[i].1 - f * b[j].1;
            if !q.is_zero() {
                out.push((a[i].0, q));
            }
            i += 1;
            j += 1;
        }
    }
    out
}

impl Tableau {
    fn build(lp: &Lp) -> Option<Tableau> {
        let mut rows = Vec::new();
        let mut rhs = Vec::new();
        let mut kinds = Vec::new();
        for c in &lp.rows {
            let mut terms = normalize(&c.terms);
            let mut b = c.rhs;
            let mut cmp = c.cmp;
            if terms.is_empty() {
                let ok = match cmp {
                    Cmp::Le => !b.is_neg(),
                    Cmp::Ge => !b.is_pos(),
                    Cmp::Eq => b.is_zero(),
                };
                if !ok {
                    return None;
                }
                continue;
            }
            // Make the right-hand side nonnegative; a `≥ 0` row becomes `≤ 0`.
            if b.is_neg() || (b.is_zero() && cmp == Cmp::Ge) {
                for t in terms.iter_mut() {
                    t.1 = -t.1;
                }
                b = -b;
                cmp = match cmp {
                    Cmp::Le => Cmp::Ge,
                    Cmp::Ge => Cmp::Le,
                    Cmp::Eq => Cmp::Eq,
                };
            }
            rows.push(terms);
            rhs.push(b);
            kinds.push(cmp);
        }
        let mut ncols = lp.nvars;
        let mut basis = vec![0; rows.len()];
        let mut artificial = vec![false; ncols];
        for (i, k) in kinds.iter().enumerate() {
            match k {
                Cmp::Le => {
                    rows[i].push((ncols, Rat::ONE));
                    basis[i] = ncols;
                    artificial.push(false);
                    ncols += 1;
                }
                Cmp::Ge => {
                    rows[i].push((ncols, -Rat::ONE));
                    artificial.push(false);
                    ncols += 1;
                    rows[i].push((ncols, Rat::ONE));
                    basis[i] = ncols;
                    artificial.push(true);
                    ncols += 1;
                }
                Cmp::Eq => {
                    rows[i].push((ncols, Rat::ONE));
                    basis[i] = ncols;
                    artificial.push(true);
                    ncols += 1;
                }
            }
        }
        let mut is_basic = vec![false; ncols];
        for &b in &basis {
            is_basic[b] = true;
        }
        Some(Tableau {
            rows,
            rhs,
            basis,
            ncols,
            is_basic,
            banned: vec![false; ncols],
            artificial,
            cost: vec![Rat::ZERO; ncols],
            z: Rat::ZERO,
        })
    }

    fn pivot(&mut self, r: usize, c: usize) {
        let a = coef(&self.rows[r], c);
        let inv = a.recip();
        for t in self.rows[r].iter_mut() {
            t.1 = t.1 * inv;
        }
        self.rhs[r] = self.rhs[r] * inv;
        let pivot_row = std::mem::take(&mut self.rows[r]);
        let pr = self.rhs[r];
        for i in 0..self.rows.len() {
            if i == r {
                continue;
            }
            let f = coef(&self.rows[i], c);
            if f.is_zero() {
                continue;
            }
            self.rows[i] = axpy(&self.rows[i], f, &pivot_row);
            self.rhs[i] = self.rhs[i] - f * pr;
        }
        let f = self.cost[c];
        if !f.is_zero() {
            for &(j, v) in &pivot_row {
                self.cost[j] = self.cost[j] - f * v;
            }
            self.z = self.z + f * pr;
        }
        self.rows[r] = pivot_row;
        self.is_basic[self.basis[r]] = false;
        self.basis[r] = c;
        self.is_basic[c] = true;
    }

    /// Runs the simplex method on the current cost row. Returns false if unbounded.
    fn run(&mut self) -> bool {
        let mut degenerate = 0usize;
        loop {
            let bland = degenerate > 64;
            let mut enter = None;
            let mut best = Rat::ZERO;
            for j in 0..self.ncols {
                if self.is_basic[j] || self.banned[j] || !self.cost[j].is_neg() {
                    continue;
                }
                if bland {
                    enter = Some(j);
                    break;
                }
                if self.cost[j] < best {
                    best = self.cost[j];
                    enter = Some(j);
                }
            }
            let Some(c) = enter else { return true };
            let mut leave: Option<(usize, Rat)> = None;
            for i in 0..self.rows.len() {
                let a = coef(&self.rows[i], c);
                if !a.is_pos() {
                    continue;
                }
                let ratio = self.rhs[i] / a;
                let better = match leave {
                    None => true,
                    Some((l, r)) => ratio < r || (ratio == r && self.basis[i] < self.basis[l]),
                };
                if better {
                    leave = Some((i, ratio));
                }
            }
            let Some((r, ratio)) = leave else { return false };
            if ratio.is_zero() {
                degenerate += 1;
            } else {
                degenerate = 0;
            }
            self.pivot(r, c);
        }
    }

    fn set_objective(&mut self, obj: &[Rat]) {
        self.cost = obj.to_vec();
        self.z = Rat::ZERO;
        for i in 0..self.rows.len() {
            let cb = obj[self.basis[i]];
            if cb.is_zero() {
                continue;
            }
            for &(j, v) in &self.rows[i] {
                self.cost[j] = self.cost[j] - cb * v;
            }
            self.z = self.z + cb * self.rhs[i];
        }
    }

    fn phase_one(&mut self) -> bool {
        let obj: Vec<Rat> = (0..self.ncols).map(|j| if self.artificial[j] { Rat::ONE } else { Rat::ZERO }).collect();
        self.set_objective(&obj);
        self.run();
        if self.z.is_pos() {
            return false;
        }
        // Drive the artificial variables that are still basic (at zero) out.
        let mut i = 0;
        while i < self.rows.len() {
            if self.artificial[self.basis[i]] {
                let j = self.rows[i].iter().find(|(j, q)| !self.artificial[*j] && !q.is_zero()).map(|t| t.0);
                match j {
                    Some(j) => self.pivot(i, j),
                    None => {
                        // A redundant row.
                        self.is_basic[self.basis[i]] = false;
                        self.rows.swap_remove(i);
                        self.rhs.swap_remove(i);
                        self.basis.swap_remove(i);
                        continue;
                    }
                }
            }
            i += 1;
        }
        for j in 0..self.ncols {
            if self.artificial[j] {
                self.banned[j] = true;
            }
        }
        true
    }

    fn optimize(&mut self, objective: &Linear) {
        let mut obj = vec![Rat::ZERO; self.ncols];
        for &(v, q) in objective {
            obj[v] = obj[v] + q;
        }
        self.set_objective(&obj);
        let bounded = self.run();
        assert!(bounded, "tekel: objective is unbounded (objectives must be bounded below)");
        for j in 0..self.ncols {
            if !self.is_basic[j] && self.cost[j].is_pos() {
                self.banned[j] = true;
            }
        }
    }

    fn values(&self, n: usize) -> Vec<Rat> {
        let mut x = vec![Rat::ZERO; n];
        for (i, &b) in self.basis.iter().enumerate() {
            if b < n {
                x[b] = self.rhs[i];
            }
        }
        x
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn r(n: i128) -> Rat {
        Rat::int(n)
    }

    #[test]
    fn small_lp() {
        // minimize x + y  s.t.  x + 2y ≥ 4,  3x + y ≥ 6
        let mut lp = Lp::default();
        let x = lp.fresh();
        let y = lp.fresh();
        lp.add(vec![(x, r(1)), (y, r(2))], Cmp::Ge, r(4));
        lp.add(vec![(x, r(3)), (y, r(1))], Cmp::Ge, r(6));
        let Outcome::Optimal(v) = lp.solve(&[vec![(x, r(1)), (y, r(1))]]) else { panic!() };
        assert_eq!(v[x] + v[y], Rat::new(14, 5));
        assert_eq!(v[x], Rat::new(8, 5));
    }

    #[test]
    fn infeasible() {
        let mut lp = Lp::default();
        let x = lp.fresh();
        lp.add(vec![(x, r(1))], Cmp::Le, r(1));
        lp.add(vec![(x, r(1))], Cmp::Ge, r(2));
        assert_eq!(lp.solve(&[]), Outcome::Infeasible);
    }

    #[test]
    fn lexicographic() {
        // minimize y first, then x, subject to x + y ≥ 3, x ≤ 2.
        let mut lp = Lp::default();
        let x = lp.fresh();
        let y = lp.fresh();
        lp.add(vec![(x, r(1)), (y, r(1))], Cmp::Ge, r(3));
        lp.add(vec![(x, r(1))], Cmp::Le, r(2));
        let Outcome::Optimal(v) = lp.solve(&[vec![(y, r(1))], vec![(x, r(1))]]) else { panic!() };
        assert_eq!((v[x], v[y]), (r(2), r(1)));
    }

    #[test]
    fn equalities() {
        let mut lp = Lp::default();
        let x = lp.fresh();
        let y = lp.fresh();
        lp.add(vec![(x, r(1)), (y, r(-1))], Cmp::Eq, r(0));
        lp.add(vec![(x, r(1)), (y, r(1))], Cmp::Eq, r(4));
        let Outcome::Optimal(v) = lp.solve(&[vec![(x, r(1))]]) else { panic!() };
        assert_eq!((v[x], v[y]), (r(2), r(2)));
    }
}

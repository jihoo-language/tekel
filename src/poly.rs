//! Univariate polynomials with exact rational coefficients.
//!
//! The analysis works in the binomial basis `C(n, 1), C(n, 2), …`, in which
//! the potential of a list shifts cleanly when a cell is taken off. People
//! read the monomial basis `n, n², …`. This module converts between them.

use crate::rat::Rat;

/// Coefficients in the monomial basis, lowest degree first.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Poly(pub Vec<Rat>);

impl Poly {
    pub fn zero() -> Poly {
        Poly(Vec::new())
    }

    fn trim(mut self) -> Poly {
        while self.0.last().is_some_and(|c| c.is_zero()) {
            self.0.pop();
        }
        self
    }

    pub fn degree(&self) -> Option<usize> {
        self.0.iter().rposition(|c| !c.is_zero())
    }

    pub fn add(&self, o: &Poly) -> Poly {
        let n = self.0.len().max(o.0.len());
        let at = |p: &Poly, i: usize| p.0.get(i).copied().unwrap_or(Rat::ZERO);
        Poly((0..n).map(|i| at(self, i) + at(o, i)).collect()).trim()
    }

    pub fn scale(&self, k: Rat) -> Poly {
        Poly(self.0.iter().map(|c| *c * k).collect()).trim()
    }

    pub fn mul(&self, o: &Poly) -> Poly {
        if self.0.is_empty() || o.0.is_empty() {
            return Poly::zero();
        }
        let mut out = vec![Rat::ZERO; self.0.len() + o.0.len() - 1];
        for (i, a) in self.0.iter().enumerate() {
            for (j, b) in o.0.iter().enumerate() {
                out[i + j] = out[i + j] + *a * *b;
            }
        }
        Poly(out).trim()
    }

    pub fn eval(&self, x: Rat) -> Rat {
        self.0.iter().rev().fold(Rat::ZERO, |acc, c| acc * x + *c)
    }

    /// `C(n, k) = n (n-1) … (n-k+1) / k!` in the monomial basis.
    pub fn binomial(k: usize) -> Poly {
        let mut p = Poly(vec![Rat::ONE]);
        for i in 0..k {
            p = p.mul(&Poly(vec![Rat::int(-(i as i128)), Rat::ONE]));
            p = p.scale(Rat::new(1, (i + 1) as i128));
        }
        p
    }

    /// Converts `Σ b[i] · C(n, i+1)` to the monomial basis.
    pub fn from_binomial(b: &[Rat]) -> Poly {
        b.iter().enumerate().fold(Poly::zero(), |acc, (i, c)| acc.add(&Poly::binomial(i + 1).scale(*c)))
    }

    /// Writes this polynomial as `c₀ + Σ b[i] · C(n, i+1)`; returns `(c₀, b)`.
    pub fn to_binomial(&self) -> (Rat, Vec<Rat>) {
        let mut rest = self.clone();
        let deg = rest.degree().unwrap_or(0);
        let mut b = vec![Rat::ZERO; deg];
        for k in (1..=deg).rev() {
            // C(n, k) has leading coefficient 1/k!.
            let lead = rest.0.get(k).copied().unwrap_or(Rat::ZERO);
            let fact: i128 = (1..=k as i128).product();
            let c = lead * Rat::int(fact);
            b[k - 1] = c;
            rest = rest.add(&Poly::binomial(k).scale(-c));
        }
        (rest.0.first().copied().unwrap_or(Rat::ZERO), b)
    }

    /// The least value at a natural number, or `None` if unbounded below.
    pub fn min_on_naturals(&self) -> Option<Rat> {
        let Some(d) = self.degree() else { return Some(Rat::ZERO) };
        if d == 0 {
            return Some(self.0[0]);
        }
        if self.0[d].is_neg() {
            return None;
        }
        // Past every real root of the derivative the polynomial increases.
        // Cauchy's bound puts those roots below 1 + max |aᵢ / a_lead|.
        let deriv: Vec<Rat> = (1..=d).map(|i| self.0[i] * Rat::int(i as i128)).collect();
        let lead = deriv[d - 1];
        let bound = deriv[..d - 1].iter().map(|c| (*c / lead).abs()).max().unwrap_or(Rat::ZERO) + Rat::ONE;
        let last = bound.ceil().max(0) + 1;
        (0..=last).map(|n| self.eval(Rat::int(n))).min()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn r(n: i128, d: i128) -> Rat {
        Rat::new(n, d)
    }

    #[test]
    fn binomial_round_trip() {
        let b = vec![r(3, 2), r(1, 1), r(2, 1)];
        let p = Poly::from_binomial(&b);
        let (c0, back) = p.to_binomial();
        assert_eq!(c0, Rat::ZERO);
        assert_eq!(back, b);
        for n in 0..10 {
            let direct: Rat = b.iter().enumerate().map(|(i, c)| *c * Rat::binom(n, i + 1)).sum();
            assert_eq!(p.eval(Rat::int(n)), direct);
        }
    }

    #[test]
    fn minimum_on_naturals() {
        // n² - 5n + 7 has its least natural value 1 at n = 2 and n = 3.
        let p = Poly(vec![r(7, 1), r(-5, 1), r(1, 1)]);
        assert_eq!(p.min_on_naturals(), Some(r(1, 1)));
        assert_eq!(Poly(vec![r(0, 1), r(-1, 1)]).min_on_naturals(), None);
    }
}

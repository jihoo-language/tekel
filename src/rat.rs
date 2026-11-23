//! Exact rationals over `i128`.
//!
//! Every bound Tekel prints is exact. Arithmetic that would overflow `i128`
//! panics with a message instead of wrapping; the analysis catches it and
//! reports the function as too large to weigh.

use std::cmp::Ordering;
use std::fmt;
use std::ops::{Add, Div, Mul, Neg, Sub};

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Rat {
    num: i128,
    den: i128,
}

pub const OVERFLOW: &str = "tekel: exact arithmetic overflowed 128 bits";

fn gcd(mut a: i128, mut b: i128) -> i128 {
    a = a.abs();
    b = b.abs();
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

fn ck(x: Option<i128>) -> i128 {
    x.expect(OVERFLOW)
}

impl Rat {
    pub const ZERO: Rat = Rat { num: 0, den: 1 };
    pub const ONE: Rat = Rat { num: 1, den: 1 };

    pub fn new(num: i128, den: i128) -> Rat {
        assert!(den != 0, "zero denominator");
        let g = gcd(num, den);
        let (mut n, mut d) = (num / g, den / g);
        if d < 0 {
            n = ck(n.checked_neg());
            d = ck(d.checked_neg());
        }
        Rat { num: n, den: d }
    }

    pub fn int(n: i128) -> Rat {
        Rat { num: n, den: 1 }
    }

    pub fn num(self) -> i128 {
        self.num
    }

    pub fn den(self) -> i128 {
        self.den
    }

    pub fn is_zero(self) -> bool {
        self.num == 0
    }

    pub fn is_pos(self) -> bool {
        self.num > 0
    }

    pub fn is_neg(self) -> bool {
        self.num < 0
    }

    pub fn is_int(self) -> bool {
        self.den == 1
    }

    pub fn abs(self) -> Rat {
        if self.num < 0 { -self } else { self }
    }

    /// Smallest integer that is at least `self`.
    pub fn ceil(self) -> i128 {
        let q = self.num.div_euclid(self.den);
        if self.num.rem_euclid(self.den) == 0 { q } else { q + 1 }
    }

    pub fn recip(self) -> Rat {
        Rat::new(self.den, self.num)
    }

    /// `n` choose `k` as an exact rational.
    pub fn binom(n: i128, k: usize) -> Rat {
        if n < 0 || (k as i128) > n {
            return Rat::ZERO;
        }
        let mut r: i128 = 1;
        for i in 0..k as i128 {
            r = ck(r.checked_mul(n - i)) / (i + 1);
        }
        Rat::int(r)
    }
}

impl Add for Rat {
    type Output = Rat;
    fn add(self, o: Rat) -> Rat {
        if self.den == o.den {
            return Rat::new(ck(self.num.checked_add(o.num)), self.den);
        }
        let g = gcd(self.den, o.den);
        let l = self.den / g;
        let r = o.den / g;
        let n = ck(ck(self.num.checked_mul(r)).checked_add(ck(o.num.checked_mul(l))));
        Rat::new(n, ck(self.den.checked_mul(r)))
    }
}

impl Sub for Rat {
    type Output = Rat;
    fn sub(self, o: Rat) -> Rat {
        self + (-o)
    }
}

impl Neg for Rat {
    type Output = Rat;
    fn neg(self) -> Rat {
        Rat { num: ck(self.num.checked_neg()), den: self.den }
    }
}

impl Mul for Rat {
    type Output = Rat;
    fn mul(self, o: Rat) -> Rat {
        if self.num == 0 || o.num == 0 {
            return Rat::ZERO;
        }
        let g1 = gcd(self.num, o.den);
        let g2 = gcd(o.num, self.den);
        let n = ck((self.num / g1).checked_mul(o.num / g2));
        let d = ck((self.den / g2).checked_mul(o.den / g1));
        Rat::new(n, d)
    }
}

impl Div for Rat {
    type Output = Rat;
    #[allow(clippy::suspicious_arithmetic_impl)]
    fn div(self, o: Rat) -> Rat {
        self * o.recip()
    }
}

impl PartialOrd for Rat {
    fn partial_cmp(&self, o: &Rat) -> Option<Ordering> {
        Some(self.cmp(o))
    }
}

impl Ord for Rat {
    fn cmp(&self, o: &Rat) -> Ordering {
        (*self - *o).num.cmp(&0)
    }
}

impl std::iter::Sum for Rat {
    fn sum<I: Iterator<Item = Rat>>(it: I) -> Rat {
        it.fold(Rat::ZERO, |a, b| a + b)
    }
}

impl fmt::Display for Rat {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.den == 1 { write!(f, "{}", self.num) } else { write!(f, "{}/{}", self.num, self.den) }
    }
}

impl fmt::Debug for Rat {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{self}")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn arithmetic() {
        let a = Rat::new(1, 2);
        let b = Rat::new(1, 3);
        assert_eq!(a + b, Rat::new(5, 6));
        assert_eq!(a - b, Rat::new(1, 6));
        assert_eq!(a * b, Rat::new(1, 6));
        assert_eq!(a / b, Rat::new(3, 2));
        assert_eq!(Rat::new(2, -4), Rat::new(-1, 2));
        assert!(a > b);
        assert_eq!(Rat::new(7, 2).ceil(), 4);
        assert_eq!(Rat::new(-7, 2).ceil(), -3);
        assert_eq!(Rat::binom(5, 2), Rat::int(10));
        assert_eq!(Rat::binom(1, 2), Rat::ZERO);
    }
}

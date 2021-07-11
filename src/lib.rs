//! Test floating point numbers for equality
//!
//! In scenarios like testing it is often times more useful to know whether two floating point
//! numbers are close to each other rather than exactly equal. Due to finite precision of computers
//! we usually cannot even expect bitwise equality of two values even if underlaying math suggests
//! it. This is where [`is_close`](https://crates.io/crates/is_close) comes in. The crate is
//! strongly inspired by
//! [Python's PEP 485](https://www.python.org/dev/peps/pep-0485/) _aka_
//! [`math.isclose`](https://docs.python.org/3/library/math.html#math.isclose).
//!
//! ## Examples
//!
//! Basic usage ...
//! ```
//! extern crate is_close;
//! use is_close::default;
//!
//! assert!(default().is_close(42.0, 42.0));
//! assert!(!default().is_close(13.0, 37.0));
//!
//! assert!(default().all_close(vec![9.0, 10.0], vec![9.0, 10.0]));
//! assert!(!default().all_close(vec![0.0, 10.0], vec![9.0, 10.0]));
//!
//! assert!(default().any_close(vec![0.0, 10.0], vec![9.0, 10.0]));
//! assert!(!default().any_close(vec![0.0, 0.0], vec![9.0, 10.0]));
//! ```
//!
//! ... and the same with macros
//! ```
//! #[macro_use]
//! extern crate is_close;
//!
//! # fn main() {
//! assert!(is_close!(42.0, 42.0));
//! assert!(!is_close!(13.0, 37.0));
//!
//! assert!(all_close!(vec![9.0, 10.0], vec![9.0, 10.0]));
//! assert!(!all_close!(vec![0.0, 10.0], vec![9.0, 10.0]));
//!
//! assert!(any_close!(vec![0.0, 10.0], vec![9.0, 10.0]));
//! assert!(!any_close!(vec![0.0, 0.0], vec![9.0, 10.0]));
//! # }
//! ```
//!
//! ## Advanced Usage
//!
//! There are different ways to determine whether two values are close to each other or not.
//! A few paramenters playing into the comparison of two floats. While `is_close` comes with sane
//! [default settings], following examples illustrate how to tweak the comparison
//! to suit your needs:
//!
//! ### Relative Tolerance
//! The amount of error allowed, relative to the magnitude of the input values.
//! Check out [`Method`].
//! ```
//! # #[macro_use]
//! # extern crate is_close;
//! # fn main() {
//! assert!(is_close!(9.9, 10.0, rel_tol=1e-2));
//! assert!(!is_close!(9.9, 10.0, rel_tol=1e-3));
//! # }
//! ```
//!
//! ### Absolute Tolerance
//! The absolute tolerance is useful for comparisons near zero.
//! ```
//! # #[macro_use]
//! # extern crate is_close;
//! # fn main() {
//! assert!(is_close!(0.0, 0.1, abs_tol=1e-1));
//! assert!(!is_close!(0.0, 0.1, abs_tol=1e-2));
//! # }
//! ```
//!
//! ### Methods:
//! The strategy of how to interpret relative tolerance, see [`Method`]:
//!
//! **Weak (default):** relative tolerance is scaled by the larger of the two values
//! ```
//! # #[macro_use]
//! # extern crate is_close;
//! # use is_close::default;
//! use is_close::WEAK;
//!
//! # fn main() {
//! assert!(default().method("weak").rel_tol(1e-1).is_close(9.0, 10.0));
//! assert!(!default().method(WEAK).rel_tol(1e-2).is_close(9.0, 10.0));
//! # }
//! ```
//!
//! **Strong:** relative tolerance is scaled by the smaller of the two values
//! ```
//! # #[macro_use]
//! # extern crate is_close;
//! # use is_close::default;
//! use is_close::STRONG;
//!
//! # fn main() {
//! assert!(all_close!(vec![9.0, 10.0], vec![10.0, 9.0], rel_tol=2e-1, method="STRONG"));
//! assert!(!any_close!(vec![9.0, 10.0], vec![10.0, 9.0], rel_tol=1e-1, method=STRONG));
//! # }
//! ```
//!
//! **Average:** relative tolerance is scaled by the average of the two values
//! ```
//! # #[macro_use]
//! # extern crate is_close;
//! # use is_close::default;
//! use is_close::AVERAGE;
//!
//! # fn main() {
//! assert!(is_close!(9.0, 10.0, rel_tol=2e-1, method="average"));
//! assert!(!is_close!(9.0, 10.0, rel_tol=1e-1, method=AVERAGE));
//! # }
//! ```
//!
//! **Asymmetric:** the second value (`b`) is used for scaling the tolerance
//! ```
//! # #[macro_use]
//! # extern crate is_close;
//! # use is_close::default;
//! use is_close::ASYMMETRIC;
//!
//! # fn main() {
//! let ic = default().method(ASYMMETRIC).rel_tol(1e-1).compile();
//! assert!(ic.is_close(9.0, 10.0));
//! assert!(!ic.is_close(10.0, 9.0));
//! # }
//! ```
//!
extern crate num_traits;

use std::fmt::Debug;

use num_traits::{cast::cast, Float};

/// Strategies for handling relative tolerance
///
/// For detailed reasoning on the pros and cons of the different variants checkout
/// [PEP 485](https://www.python.org/dev/peps/pep-0485/#relative-difference).
///
#[derive(Clone, Debug)]
pub enum Method {
    /// Relative tolerance is scaled by the larger of the two values (default)
    Weak,
    /// Relative tolerance is scaled by the smaller of the two values
    Strong,
    /// Relative tolerance is scaled by the average of the two values
    Average,
    /// The second value (`b`) is used for scaling the tolerance
    Asymmetric,
}

impl Method {
    #[inline]
    fn common_checks<T: Float>(a: T, b: T) -> Option<bool> {
        if a == b {
            Some(true)
        } else if !a.is_finite() || !b.is_finite() {
            Some(false)
        } else {
            None
        }
    }

    fn method<'a, T: Float + 'a>(&self, rel_tol: T, abs_tol: T) -> Box<dyn Fn(T, T) -> bool + 'a> {
        match self {
            Method::Asymmetric => Box::new(move |a, b| match Self::common_checks(a, b) {
                Some(result) => result,
                None => {
                    let diff = Float::abs(a - b);
                    (diff <= Float::abs(rel_tol * b)) || (diff <= abs_tol)
                }
            }),
            Method::Average => Box::new(move |a, b| match Self::common_checks(a, b) {
                Some(result) => result,
                None => {
                    let diff = Float::abs(a - b);
                    diff <= (rel_tol * (a + b) / cast(2.0).unwrap()).abs()
                        || (diff <= abs_tol)
                }
            }),
            Method::Strong => Box::new(move |a, b| match Self::common_checks(a, b) {
                Some(result) => result,
                None => {
                    let diff = Float::abs(a - b);
                    ((diff <= Float::abs(rel_tol * b)) && (diff <= Float::abs(rel_tol * a)))
                        || (diff <= abs_tol)
                }
            }),
            Method::Weak => Box::new(move |a, b| match Self::common_checks(a, b) {
                Some(result) => result,
                None => {
                    let diff = Float::abs(a - b);
                    ((diff <= Float::abs(rel_tol * b)) || (diff <= Float::abs(rel_tol * a)))
                        || (diff <= abs_tol)
                }
            }),
        }
    }
}

/// Shorthand for [`Method::Asymmetric`]
pub const ASYMMETRIC: Method = Method::Asymmetric;

/// Shorthand for [`Method::Average`]
pub const AVERAGE: Method = Method::Average;

/// Shorthand for [`Method::Strong`]
pub const STRONG: Method = Method::Strong;

/// Shorthand for [`Method::Weak`]
pub const WEAK: Method = Method::Weak;

impl From<&str> for Method {
    fn from(s: &str) -> Self {
        match s.to_lowercase().as_ref() {
            "asymmetric" => Self::Asymmetric,
            "average" => Self::Average,
            "strong" => Self::Strong,
            "weak" => Self::Weak,
            _ => panic!("unknown method {:?}", s),
        }
    }
}

/// Default relative tolerance
pub const DEFAULT_REL_TOL: f64 = 1e-8;

/// Default absolute tolerance
pub const DEFAULT_ABS_TOL: f64 = 0.0;

/// Float Comparator
pub struct Comparator<'a, T: Float> {
    is_close: Box<dyn Fn(T, T) -> bool + 'a>,
}

impl<T: Float> Comparator<'_, T> {
    /// Check whether or not two values `a` and `b` are close to each other
    pub fn is_close(&self, a: T, b: T) -> bool {
        (self.is_close)(a, b)
    }

    /// Check whether or not two iterables `a` and `b` are pairwise close to each other
    pub fn all_close<I, J>(&self, a: I, b: J) -> bool
        where
            I: IntoIterator<Item=T>,
            J: IntoIterator<Item=T>,
    {
        a.into_iter()
            .zip(b.into_iter())
            .all(|(x, y)| self.is_close(x, y))
    }

    /// Check whether or not two iterables `a` and `b` are pairwise close to each other in at least one place
    pub fn any_close<I, J>(&self, a: I, b: J) -> bool
        where
            I: IntoIterator<Item=T>,
            J: IntoIterator<Item=T>,
    {
        a.into_iter()
            .zip(b.into_iter())
            .any(|(x, y)| self.is_close(x, y))
    }
}

/// Builder for [`Comparator`] functions. It holds the following parameters:
///
/// - `rel_tol`: maximum difference for being considered close, relative to the magnitude of the
///         input values. It defaults to [`DEFAULT_REL_TOL`].
/// - `abs_tol`: maximum difference for being considered close, regardless of the magnitude of the
///         input values. It defaults to [`DEFAULT_ABS_TOL`].
/// - `method`: strategy of how to interpret relative tolerance. It defaults to [`Method::Weak`].
///
#[derive(Clone, Debug)]
pub struct ComparatorBuilder<T: Float> {
    rel_tol: T,
    abs_tol: T,
    method: Method,
}

impl<T: Float> Default for ComparatorBuilder<T> {
    fn default() -> Self {
        ComparatorBuilder {
            rel_tol: cast(DEFAULT_REL_TOL).unwrap(),
            abs_tol: cast(DEFAULT_ABS_TOL).unwrap(),
            method: WEAK,
        }
    }
}

impl<T: Float> ComparatorBuilder<T> {
    /// Set the relative tolerance
    pub fn rel_tol(&mut self, value: T) -> &mut Self {
        self.rel_tol = value.abs();
        self
    }

    /// Set the absolute tolerance
    pub fn abs_tol(&mut self, value: T) -> &mut Self {
        self.abs_tol = value.abs();
        self
    }

    /// Set the strategy used to handle relative tolerance
    pub fn method<M: Into<Method>>(&mut self, method: M) -> &mut Self {
        self.method = method.into();
        self
    }
}

impl<'a, T: Float + 'a> ComparatorBuilder<T> {
    // Compile current configuration into a closure which increases speed when called multiple times
    pub fn compile(&self) -> Comparator<'a, T> {
        Comparator {
            is_close: self.method.method(self.rel_tol, self.abs_tol),
        }
    }

    /// Shorthand for `compile().is_close(a, b)`
    pub fn is_close(&self, a: T, b: T) -> bool {
        self.compile().is_close(a, b)
    }

    /// Shorthand for `compile().all_close(a, b)`
    pub fn all_close<I, J>(&self, a: I, b: J) -> bool
        where
            I: IntoIterator<Item=T>,
            J: IntoIterator<Item=T>,
    {
        self.compile().all_close(a, b)
    }

    /// Shorthand for `compile().any_close(a, b)`
    pub fn any_close<I, J>(&self, a: I, b: J) -> bool
        where
            I: IntoIterator<Item=T>,
            J: IntoIterator<Item=T>,
    {
        self.compile().any_close(a, b)
    }
}

/// Create default [`IsClose`] configuration: `{ rel_tol: 1e-8, abs_tol: 0.0, method: "weak" }`
pub fn default<T: Float>() -> ComparatorBuilder<T> {
    ComparatorBuilder::default()
}

/// Check whether or not two values `a` and `b` are close to each other
///
/// ## Usage
/// ```
/// #[macro_use]
/// extern crate is_close;
/// use is_close::AVERAGE;
///
/// # fn main() {
/// assert!(is_close!(1.0, 1.0));
/// assert!(!is_close!(1.0, 2.0));
/// assert!(is_close!(9.0, 10.0, rel_tol=2e-1, method=AVERAGE));
/// assert!(!is_close!(9.0, 10.0, rel_tol=1e-1, method=AVERAGE));
/// # }
/// ```
#[macro_export]
macro_rules! is_close {
    ($a:expr, $b:expr $(, $set:ident = $val:expr)*) => {
        {
            $crate::default()$(.$set($val))*.is_close($a, $b)
        }
    };
}

/// Check whether or not two iterables `a` and `b` are pairwise close to each other
///
/// ## Usage
/// ```
/// #[macro_use]
/// extern crate is_close;
/// use is_close::STRONG;
///
/// # fn main() {
/// assert!(all_close!(vec![9.0, 10.0], vec![9.0, 10.0]));
/// assert!(!all_close!(vec![0.0, 10.0], vec![9.0, 10.0]));
/// assert!(all_close!(vec![9.0, 10.0], vec![10.0, 9.0], rel_tol=2e-1, method=STRONG));
/// assert!(!all_close!(vec![9.0, 10.0], vec![10.0, 0.0], rel_tol=2e-1, method=STRONG));
/// # }
/// ```
#[macro_export]
macro_rules! all_close {
    ($a:expr, $b:expr $(, $set:ident = $val:expr)*) => {
        {
            $crate::default()$(.$set($val))*.all_close($a, $b)
        }
    };
}

/// Check whether or not two iterables `a` and `b` are pairwise close to each other in at least one place
///
/// ## Usage
/// ```
/// #[macro_use]
/// extern crate is_close;
/// use is_close::STRONG;
///
/// # fn main() {
/// assert!(any_close!(vec![0.0, 10.0], vec![9.0, 10.0]));
/// assert!(!any_close!(vec![0.0, 0.0], vec![9.0, 10.0]));
/// assert!(any_close!(vec![9.0, 10.0], vec![10.0, 9.5], rel_tol=1e-1, method=STRONG));
/// assert!(!any_close!(vec![9.0, 10.0], vec![10.0, 9.0], rel_tol=1e-1, method=STRONG));
/// # }
/// ```
#[macro_export]
macro_rules! any_close {
    ($a:expr, $b:expr $(, $set:ident = $val:expr)*) => {
        {
            $crate::default()$(.$set($val))*.any_close($a, $b)
        }
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_debug() {
        assert_eq!(
            "ComparatorBuilder { rel_tol: 0.00000001, abs_tol: 0.0, method: Weak }",
            format!("{:?}", default::<f64>())
        )
    }

    #[test]
    fn test_exact() {
        for (a, b) in &[
            (2.0, 2.0),
            (0.1e200, 0.1e200),
            (1.123e-300, 1.123e-300),
            (0.0, -0.0),
        ] {
            assert!(default().rel_tol(0.0).abs_tol(0.0).is_close(*a, *b));
            assert!(is_close!(*a, *b, abs_tol = 0.0));
        }
    }

    #[test]
    fn test_relative() {
        for (a, b) in &[
            (1e8, 1e8 + 1.),
            (-1e-8, -1.000000009e-8),
            (1.12345678, 1.12345679),
        ] {
            assert!(default().rel_tol(1e-8).is_close(*a, *b));
            assert!(is_close!(*a, *b, rel_tol = 1e-8));
            assert!(!default().rel_tol(1e-9).is_close(*a, *b));
            assert!(!is_close!(*a, *b, rel_tol = 1e-9));
        }
    }

    #[test]
    fn test_zero() {
        for (a, b) in &[(1e-9, 0.0), (-1e-9, 0.0), (-1e-150, 0.0)] {
            assert!(default().abs_tol(1e-8).is_close(*a, *b));
            assert!(is_close!(*a, *b, abs_tol = 1e-8));
            assert!(!default().rel_tol(0.9).is_close(*a, *b));
            assert!(!is_close!(*a, *b, rel_tol = 0.9));
        }
    }

    #[test]
    fn test_non_finite() {
        for (a, b) in &[
            (f64::INFINITY, f64::INFINITY),
            (f64::NEG_INFINITY, f64::NEG_INFINITY),
        ] {
            assert!(default().abs_tol(0.999999999999999).is_close(*a, *b));
            assert!(is_close!(*a, *b, abs_tol = 0.999999999999999));
        }

        for (a, b) in &[
            (f64::NAN, f64::NAN),
            (f64::NAN, 1e-100),
            (1e-100, f64::NAN),
            (f64::INFINITY, f64::NAN),
            (f64::NAN, f64::INFINITY),
            (f64::INFINITY, f64::NEG_INFINITY),
            (f64::INFINITY, 1.0),
            (1.0, f64::INFINITY),
        ] {
            assert!(!default().abs_tol(0.999999999999999).is_close(*a, *b));
            assert!(!is_close!(*a, *b, abs_tol = 0.999999999999999));
        }
    }

    #[test]
    fn test_other_methods() {
        assert!(default().method("weak").rel_tol(1e-1).is_close(9.0, 10.0));
        assert!(default().method("weak").rel_tol(1e-1).is_close(10.0, 9.0));
        assert!(!default().method(WEAK).rel_tol(1e-2).is_close(9.0, 10.0));
        assert!(!default().method(WEAK).rel_tol(1e-2).is_close(10.0, 9.0));

        assert!(all_close!(
            vec![9.0, 10.0],
            vec![10.0, 9.0],
            rel_tol = 2e-1,
            method = "STRONG"
        ));
        assert!(!any_close!(
            vec![9.0, 10.0],
            vec![10.0, 9.0],
            rel_tol = 1e-1,
            method = STRONG
        ));

        assert!(is_close!(9.0, 10.0, rel_tol = 2e-1, method = "average"));
        assert!(is_close!(10.0, 9.0, rel_tol = 2e-1, method = "average"));
        assert!(!is_close!(9.0, 10.0, rel_tol = 1e-1, method = AVERAGE));
        assert!(!is_close!(10.0, 9.0, rel_tol = 1e-1, method = AVERAGE));

        let ic = default().method(ASYMMETRIC).rel_tol(1e-1).compile();
        assert!(ic.is_close(9.0, 10.0));
        assert!(!ic.is_close(10.0, 9.0));
    }

    #[test]
    #[should_panic(expected = "unknown method \"fnord\"")]
    fn test_unknown_method() {
        default::<f64>().method("fnord");
    }

    #[test]
    fn test_all_close() {
        assert!(default().all_close(vec![0.0, 1.0, 2.0], (0..3).into_iter().map(|i| i as f64)));
        assert!(all_close!(
            vec![0.0, 1.0, 2.0],
            (0..3).into_iter().map(|i| i as f64)
        ));
        assert!(!default().all_close(vec![0.0, 1.0, 3.0], (0..3).into_iter().map(|i| i as f64)));
        assert!(!all_close!(
            vec![0.0, 1.0, 3.0],
            (0..3).into_iter().map(|i| i as f64)
        ));
    }
}

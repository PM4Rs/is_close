//! Determine whether floating point numbers are close in value
//!
//! In use cases such as testing it is often times more useful to know whether two floating point
//! numbers are close to each other rather than exactly equal. Due to finite precision of computers,
//! we usually cannot even expect bitwise equality of two values even if underlaying math suggests
//! it. This is where [`is_close`](https://crates.io/crates/is_close) comes in. The crate is
//! strongly inspired by
//! [Python's PEP 485 _aka_ `math.isclose`](https://www.python.org/dev/peps/pep-0485/).
//!
//! ## Examples
//!
//! **Basic usage ...**
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
//! **... and the same with macros**
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
//! ### Advanced Usage
//!
//! There are different ways to determine whether two values are close to each other or not.
//! There are a few paramenters playing into the comparison of two floats. `is_close` comes with
//! sane [default settings](fn.default.html). However, the following examples illustrate how to
//! tweak the comparison to suit your needs:
//!
//! **Relative Tolerance:** the amount of error allowed, relative to the magnitude of the input
//! values:
//! ```
//! # #[macro_use]
//! # extern crate is_close;
//! # fn main() {
//! assert!(is_close!(9.9, 10.0, rel_tol=1e-2));
//! assert!(!is_close!(9.9, 10.0, rel_tol=1e-3));
//! # }
//! ```
//!
//! **Absolute Tolerance:** useful for comparisons to zero:
//! ```
//! # #[macro_use]
//! # extern crate is_close;
//! # fn main() {
//! assert!(is_close!(0.0, 0.1, abs_tol=1e-1));
//! assert!(!is_close!(0.0, 0.1, abs_tol=1e-2));
//! # }
//! ```
//!
//! **Other Methods:** the strategy of how to interpret relative tolerance, see
//! [`Method`](enum.Method.html):
//! ```
//! # #[macro_use]
//! # extern crate is_close;
//! # use is_close::default;
//! use is_close::{ASYMMETRIC, WEAK, STRONG, AVERAGE};
//!
//! # fn main() {
//! // Weak: relative tolerance is scaled by the larger of the two values (default)
//! assert!(default().method("weak").rel_tol(1e-1).is_close(9.0, 10.0));
//! assert!(default().method("weak").rel_tol(1e-1).is_close(10.0, 9.0));
//! assert!(!default().method(WEAK).rel_tol(1e-2).is_close(9.0, 10.0));
//! assert!(!default().method(WEAK).rel_tol(1e-2).is_close(10.0, 9.0));
//!
//! // Strong: relative tolerance is scaled by the smaller of the two values
//! assert!(all_close!(vec![9.0, 10.0], vec![10.0, 9.0], rel_tol=2e-1, method="STRONG"));
//! assert!(!any_close!(vec![9.0, 10.0], vec![10.0, 9.0], rel_tol=1e-1, method=STRONG));
//!
//! // Average: relative tolerance is scaled by the average of the two values
//! assert!(is_close!(9.0, 10.0, rel_tol=2e-1, method="average"));
//! assert!(is_close!(10.0, 9.0, rel_tol=2e-1, method="average"));
//! assert!(!is_close!(9.0, 10.0, rel_tol=1e-1, method=AVERAGE));
//! assert!(!is_close!(10.0, 9.0, rel_tol=1e-1, method=AVERAGE));
//!
//! // Asymmetric: he second value (`b`) is used for scaling the tolerance
//! let ic = default().method(ASYMMETRIC).rel_tol(1e-1).compile();
//! assert!(ic(9.0, 10.0));
//! assert!(!ic(10.0, 9.0));
//! # }
//! ```
//!
extern crate num_traits;

use std::fmt::{Debug, Formatter};

use num_traits::{cast, Float};

/// Strategies of handling relative tolerance
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

/// Shorthand for [`Method::Asymmetric`](enum.Method.html)
pub const ASYMMETRIC: Method = Method::Asymmetric;

/// Shorthand for [`Method::Average`](enum.Method.html)
pub const AVERAGE: Method = Method::Average;

/// Shorthand for [`Method::Strong`](enum.Method.html)
pub const STRONG: Method = Method::Strong;

/// Shorthand for [`Method::Weak`](enum.Method.html)
pub const WEAK: Method = Method::Weak;

impl From<&str> for Method {
    fn from(s: &str) -> Self {
        match s.to_lowercase().as_ref() {
            "asymmetric" => Self::Asymmetric,
            "average" => Self::Average,
            "strong" => Self::Strong,
            "weak" => Self::Weak,
            _ => panic!(format!("unknown method {:?}", s)),
        }
    }
}

/// Compare two floats with some tolerance
///
/// This type holds information on how to compare floats and is heavily inspired by
/// [Python's PEP 485](https://www.python.org/dev/peps/pep-0485/). It holds the following parameters:
///
/// - `rel_tol`: maximum difference for being considered "close", relative to the magnitude of the
///         input values, defaults to 1e-8
/// - `abs_tol`: maximum difference for being considered "close", regardless of the magnitude of the
///         input values, defaults to 0.0
/// - `method`: strategy of how to interpret relative tolerance, see [`Method`](enum.Method.html)
///
pub struct IsClose<T: Float> {
    _rel_tol: T,
    _abs_tol: T,
    _method: Method,
}

impl<T: Float> Default for IsClose<T> {
    fn default() -> Self {
        IsClose {
            _rel_tol: cast::cast(1e-8).unwrap(),
            _abs_tol: cast::cast(0.0).unwrap(),
            _method: WEAK,
        }
    }
}

impl<T: Float + Debug> Debug for IsClose<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut f = f.debug_struct("IsClose");

        f.field("rel_tol", &self._rel_tol);
        f.field("abs_tol", &self._abs_tol);
        f.field("method", &self._method);

        f.finish()
    }
}

impl<T: Float + 'static> IsClose<T> {
    /// Set the relative tolerance
    pub fn rel_tol(&mut self, value: T) -> &mut Self {
        self._rel_tol = value.abs();
        self
    }

    /// Set the absolute tolerance
    pub fn abs_tol(&mut self, value: T) -> &mut Self {
        self._abs_tol = value.abs();
        self
    }

    /// Set the strategy used to handle relative tolerance
    pub fn method<M: Into<Method>>(&mut self, method: M) -> &mut Self {
        self._method = method.into();
        self
    }

    /// Compile current configuration into a closure which increases speed when called multiple times
    pub fn compile(&self) -> Box<dyn Fn(T, T) -> bool> {
        let rel_tol = self._rel_tol;
        let abs_tol = self._abs_tol;

        let _is_close: Box<dyn Fn(T, T, T) -> bool> = match self._method {
            Method::Asymmetric => {
                Box::new(move |_, b, diff| (diff <= Float::abs(rel_tol * b)) || (diff <= abs_tol))
            }
            Method::Average => Box::new(move |a, b, diff| {
                diff <= (rel_tol * (a + b) / cast::cast(2.0).unwrap()).abs() || (diff <= abs_tol)
            }),
            Method::Strong => Box::new(move |a, b, diff| {
                ((diff <= Float::abs(rel_tol * b)) && (diff <= Float::abs(rel_tol * a)))
                    || (diff <= abs_tol)
            }),
            Method::Weak => Box::new(move |a, b, diff| {
                ((diff <= Float::abs(rel_tol * b)) || (diff <= Float::abs(rel_tol * a)))
                    || (diff <= abs_tol)
            }),
        };

        Box::new(move |a: T, b: T| {
            // trivial case
            if a == b {
                return true;
            }

            // check border cases
            let diff = (b - a).abs();
            if !diff.is_finite() {
                return false;
            }

            // assess difference by chosen method
            _is_close(a, b, diff)
        })
    }

    /// Check whether or not two values `a` and `b` are "close" to each other
    pub fn is_close(&self, a: T, b: T) -> bool {
        self.compile()(a, b)
    }

    /// Check whether or not two iterables `a` and `b` are pairwise "close" to each other
    pub fn all_close<I, J>(&self, a: I, b: J) -> bool
    where
        I: IntoIterator<Item = T>,
        J: IntoIterator<Item = T>,
    {
        let _is_close = self.compile();
        a.into_iter()
            .zip(b.into_iter())
            .all(|(x, y)| _is_close(x, y))
    }

    /// Check whether or not two iterables `a` and `b` are pairwise "close" to each other in at least one place
    pub fn any_close<I, J>(&self, a: I, b: J) -> bool
    where
        I: IntoIterator<Item = T>,
        J: IntoIterator<Item = T>,
    {
        let _is_close = self.compile();
        a.into_iter()
            .zip(b.into_iter())
            .any(|(x, y)| _is_close(x, y))
    }
}

/// Create default [`IsClose`](struct.IsClose.html) configuration: `{ rel_tol: 1e-8, abs_tol: 0.0, method: "weak" }`
pub fn default<T: Float>() -> IsClose<T> {
    IsClose::default()
}

/// Check whether or not two values `a` and `b` are "close" to each other
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

/// Check whether or not two iterables `a` and `b` are pairwise "close" to each other
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

/// Check whether or not two iterables `a` and `b` are pairwise "close" to each other in at least one place
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
            "IsClose { rel_tol: 0.00000001, abs_tol: 0.0, method: Weak }",
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
        assert!(ic(9.0, 10.0));
        assert!(!ic(10.0, 9.0));
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

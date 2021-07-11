# is_close
**Determine whether floating point numbers are close in value**

[![Build Status](https://travis-ci.org/PM4Rs/is_close.svg?branch=main)](https://travis-ci.org/PM4Rs/is_close)
[![Crate](https://img.shields.io/crates/v/is_close)](https://crates.io/crates/is_close)
[![API](https://docs.rs/is_close/badge.svg)](https://docs.rs/is_close)
[![License](https://img.shields.io/crates/l/is_close)](https://crates.io/crates/is_close#license)
[![Downloads](https://img.shields.io/crates/d/is_close)](https://crates.io/crates/is_close)

In scenarios such as testing it is often times more useful to know whether two floating point
numbers are close to each other rather than exactly equal. Due to finite precision of computers,
we usually cannot even expect bitwise equality of two values even if underlying math suggests
it. This is where [`is_close`](https://crates.io/crates/is_close) comes into play. This crate is
strongly inspired by Python [PEP 485](https://www.python.org/dev/peps/pep-0485/) _aka_
[`math.isclose`](https://docs.python.org/3/library/math.html#math.isclose).

## Usage

```rust
#[macro_use]
extern crate is_close;

assert!(is_close!(42.0, 42.0));
assert!(all_close!(vec![9.0, 10.0], vec![9.0, 10.0]));
assert!(any_close!(vec![0.0, 10.0], vec![9.0, 10.0]));
```

You'll find plenty of examples at our [documentation](https://docs.rs/is_close).

## License
Copyright © 2020 The _promi_ Developers

_is_close_ is licensed under MIT **OR** Apache 2.0 license

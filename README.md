# is_close
**Determine whether floating point numbers are close in value**

[![Build Status](https://travis-ci.org/PM4Rs/is_close.svg?branch=master)](https://travis-ci.org/PM4Rs/is_close)
[![Crate](https://img.shields.io/crates/v/is_close)](https://crates.io/crates/is_close)
[![API](https://docs.rs/is_close/badge.svg)](https://docs.rs/is_close)
[![License](https://img.shields.io/crates/l/is_close)](https://crates.io/crates/is_close#license)
[![Downloads](https://img.shields.io/crates/d/is_close)](https://crates.io/crates/is_close)

In use cases such as testing it is often times more useful to know whether two floating point
numbers are close to each other rather than exactly equal. Due to finite precision of computers,
we usually cannot even expect bitwise equality of two values even if underlaying math suggests
it. This is where [`is_close`](https://crates.io/crates/is_close) comes in. The crate is
strongly inspired by
[Python's PEP 485 _aka_ `math.isclose`](https://www.python.org/dev/peps/pep-0485/).

## Usage

You'll find plenty of examples at our [documentation](https://docs.rs/is_close).

## License
Copyright © 2020 The _promi_ Developers

_is_close_ is licensed under MIT **OR** Apache 2.0 license
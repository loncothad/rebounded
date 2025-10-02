//! Values bound by some kind of interval.

mod ints;

#[doc(inline)]
pub use ints::*;

pub enum Error {
    BelowLowerBound,
    AboveUpperBound,
}

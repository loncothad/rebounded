use crate::Error;

macro_rules! bounded_ints {
    ($($wrapped_name:ident($num_type:ident)),*) => {
        $(
            /// Bounded type (inclusive) that holds a value that is `MIN <= value <= MAX`
            ///
            /// Has the same representation as the primitive type.
            ///
            /// ### Safety
            ///
            /// Creating an instance with `MIN > MAX` is undefined behavior.
            #[repr(transparent)]
            #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
            pub struct $wrapped_name<const MIN: $num_type, const MAX: $num_type> {
                inner: $num_type,
            }

            impl<const MIN: $num_type, const MAX: $num_type> $wrapped_name<MIN, MAX> {
                /// Upper bound.
                pub const MAX: $num_type = MAX;
                /// Upper bound, represented as the *bounded* type.
                pub const MAX_PACKED: Self = Self::pack_const(MAX);
                /// Lower bound.
                pub const MIN: $num_type = MIN;
                /// Lower bound, represented as the *bounded* type.
                pub const MIN_PACKED: Self = Self::pack_const(MIN);

                /// Returns `Self::MIN`.
                pub const fn min(&self) -> $num_type {
                    MIN
                }

                /// Returns `Self::MAX`.
                pub const fn max(&self) -> $num_type {
                    MAX
                }

                fn pack(value: $num_type) -> Self {
                    Self {
                        inner: value
                    }
                }

                const fn pack_const(value: $num_type) -> Self {
                    Self {
                        inner: value
                    }
                }

                #[inline]
                fn assert() {
                    assert!(MIN < MAX);
                }

                /// Create a new value of the type.
                ///
                /// Returns the error if the provided `value` was outside of the defined
                /// bounds.
                pub fn new<N: Into<$num_type> + PartialOrd<$num_type> + Ord>(
                    value: N,
                ) -> Result<Self, Error> {
                    Self::assert();

                    if value > MAX {
                        Err(Error::AboveUpperBound)
                    } else if value < MIN {
                        Err(Error::BelowLowerBound)
                    } else {
                        Ok(Self::pack(value.into()))
                    }
                }

                /// Create a new value of the type without any checks.
                ///
                /// ### Safety
                ///
                /// User is responsible for providing the value that is already between
                /// the defined bounds. Creating a value outside of the defined bounds
                /// is undefined behavior.
                pub unsafe fn new_unchecked<N: Into<$num_type>>(value: N) -> Self {
                    Self::assert();
                    Self::pack(value.into())
                }

                /// Create a new value of the type.
                ///
                /// If `value` is within range, returns a new instance; otherwise,
                /// clamps it to the upper or lower bound.
                pub fn new_clamped<N: Into<$num_type> + PartialOrd<$num_type> + Ord>(value: N) -> Self {
                    Self::pack(Self::clamp(value.into()))
                }

                /// Returns the underlying value.
                ///
                /// This value is guaranteed to be between `Self::MIN` and `Self::MAX`.
                pub fn get(self) -> $num_type {
                    self.inner
                }

                /// `const`-compatible `Self::get`.
                pub const fn get_const(&self) -> $num_type {
                    self.inner
                }

                /// Check if abstract value is within bounds.
                pub fn is_in_bounds(n: &$num_type) -> bool {
                    n >= &Self::MIN && n <= &Self::MAX
                }

                fn filter_map_opt(n: Option<$num_type>) -> Option<Self> {
                    n.filter(Self::is_in_bounds).map(Self::pack)
                }

                /// Clamp the provided `n` between the `Self::MIN` and `Self::MAX`.
                pub fn clamp(n: $num_type) -> $num_type {
                    n.clamp(MIN, MAX)
                }

                /// Checked integer addition. Computes `self + rhs`, returning `None` if
                /// either bound overflow or integer overflow occurred.
                pub fn checked_add<Rhs: Into<$num_type>>(self, rhs: Rhs) -> Option<Self> {
                    Self::filter_map_opt(self.inner.checked_add(rhs.into()))
                }

                /// Unchecked integer addition. Computes `self + rhs`, assuming overflow
                /// cannot occur.
                ///
                /// ### Safety
                ///
                /// This results in undefined behavior if the result overflows the primitive
                /// type's bounds or the `[MIN, MAX]` bounds of this type.
                pub unsafe fn unchecked_add<Rhs: Into<$num_type>>(self, rhs: Rhs) -> Self {
                    Self::pack(unsafe { self.inner.unchecked_add(rhs.into()) })
                }

                /// Checked integer subtraction. Computes `self - rhs`, returning `None` if
                /// either bound overflow or integer overflow occurred.
                pub fn checked_sub<Rhs: Into<$num_type>>(self, rhs: Rhs) -> Option<Self> {
                    Self::filter_map_opt(self.inner.checked_sub(rhs.into()))
                }

                /// Unchecked integer subtraction. Computes `self - rhs`, assuming overflow
                /// cannot occur.
                ///
                /// ### Safety
                ///
                /// This results in undefined behavior if the result overflows the primitive
                /// type's bounds or the `[MIN, MAX]` bounds of this type.
                pub unsafe fn unchecked_sub<Rhs: Into<$num_type>>(self, rhs: Rhs) -> Self {
                    Self::pack(unsafe { self.inner.unchecked_sub(rhs.into()) })
                }

                /// Checked integer multiplication. Computes `self * rhs`, returning `None`
                /// if either bound overflow or integer overflow occurred.
                pub fn checked_mul<Rhs: Into<$num_type>>(self, rhs: Rhs) -> Option<Self> {
                    Self::filter_map_opt(self.inner.checked_mul(rhs.into()))
                }

                /// Unchecked integer multiplication. Computes `self * rhs`, assuming
                /// overflow cannot occur.
                ///
                /// ### Safety
                ///
                /// This results in undefined behavior if the result overflows the primitive
                /// type's bounds or the `[MIN, MAX]` bounds of this type.
                pub unsafe fn unchecked_mul<Rhs: Into<$num_type>>(self, rhs: Rhs) -> Self {
                    Self::pack(unsafe { self.inner.unchecked_mul(rhs.into()) })
                }

                /// Checked integer division. Computes `self / rhs`, returning `None` if
                /// either bound overflow or integer overflow occurred.
                pub fn checked_div<Rhs: Into<$num_type>>(self, rhs: Rhs) -> Option<Self> {
                    Self::filter_map_opt(self.inner.checked_div(rhs.into()))
                }

                /// Checked integer remainder. Computes `self % rhs`, returning `None` if
                /// either bound overflow or integer overflow occurred.
                pub fn checked_rem<Rhs: Into<$num_type>>(self, rhs: Rhs) -> Option<Self> {
                    Self::filter_map_opt(self.inner.checked_rem(rhs.into()))
                }

                /// Checked negation. Computes `-self`, returning `None` if bound overflow
                /// or `self == inner_num_repr::MIN` occurred.
                pub fn checked_neg(self) -> Option<Self> {
                    Self::filter_map_opt(self.inner.checked_neg())
                }

                /// Checked integer exponentiation. Computes `self.pow()`, returning `None`
                /// if bound overflow or `self == inner_num_repr::MIN` occurred.
                pub fn checked_pow(self, exp: u32) -> Option<Self> {
                    Self::filter_map_opt(self.inner.checked_pow(exp))
                }
            }

            impl<const MIN: $num_type, const MAX: $num_type> ::core::fmt::Display
                for $wrapped_name<MIN, MAX>
            {
                /// Uses the formatter of the `inner_num_repr`.
                fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
                    self.inner.fmt(f)
                }
            }

            impl<const MIN: $num_type, const MAX: $num_type> ::core::fmt::Debug
                for $wrapped_name<MIN, MAX>
            {
                /// Example of the string representation:
                ///
                /// ```text
                /// 5 ∈ [1, 10]
                /// ```
                fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
                    write!(f, "{} ∈ [{MIN}, {MAX}]", self.inner)
                }
            }

            impl<const MIN: $num_type, const MAX: $num_type> PartialEq<$num_type>
                for $wrapped_name<MIN, MAX>
            {
                fn eq(&self, other: &$num_type) -> bool {
                    self.inner.eq(other)
                }

                fn ne(&self, other: &$num_type) -> bool {
                    self.inner.ne(other)
                }
            }

            impl<const MIN: $num_type, const MAX: $num_type> PartialOrd<$num_type> for $wrapped_name<MIN, MAX> {
                fn partial_cmp(&self, other: &$num_type) -> Option<::core::cmp::Ordering> {
                    self.inner.partial_cmp(other)
                }

                fn lt(&self, other: &$num_type) -> bool {
                    self.inner.lt(other)
                }

                fn le(&self, other: &$num_type) -> bool {
                    self.inner.le(other)
                }

                fn gt(&self, other: &$num_type) -> bool {
                    self.inner.gt(other)
                }

                fn ge(&self, other: &$num_type) -> bool {
                    self.inner.ge(other)
                }
            }

            impl<const MIN: $num_type, const MAX: $num_type> Into<$num_type>
                for $wrapped_name<MIN, MAX>
            {
                fn into(self) -> $num_type {
                    self.inner
                }
            }

            impl<const MIN: $num_type, const MAX: $num_type> TryFrom<$num_type>
                for $wrapped_name<MIN, MAX>
            {
                type Error = Error;

                fn try_from(value: $num_type) -> Result<Self, Self::Error> {
                    Self::new(value)
                }
            }
        )*
    }
}

bounded_ints! {
    BoundedInt8(i8),
    BoundedInt16(i16),
    BoundedInt32(i32),
    BoundedInt64(i64),
    BoundedIsize(isize),
    BoundedUInt8(u8),
    BoundedUInt16(u16),
    BoundedUInt32(u32),
    BoundedUInt64(u64),
    BoundedUsize(usize)
}

macro_rules! impl_from_for_i8 {
    ($($bounded_int_name:ident),*) => {
        $(
            impl From<$bounded_int_name<{ i8::MIN as _ }, { i8::MAX as _ }>> for i8 {
                fn from(value: $bounded_int_name<-128, 127>) -> Self {
                    value.inner as i8
                }
            }
        )*
    };
}

macro_rules! impl_from_for_u8 {
    ($($bounded_int_name:ident),*) => {
        $(
            impl From<$bounded_int_name<{ u8::MIN as _ }, { u8::MAX as _ }>> for u8 {
                fn from(value: $bounded_int_name<0, 255>) -> Self {
                    value.inner as u8
                }
            }
        )*
    };
}

macro_rules! impl_from_for_i16 {
    ($($bounded_int_name:ident),*) => {
        $(
            impl From<$bounded_int_name<{ i16::MIN as _ }, { i16::MAX as _ }>> for i16 {
                fn from(value: $bounded_int_name<-32768, 32767>) -> Self {
                    value.inner as i16
                }
            }
        )*
    };
}

macro_rules! impl_from_for_u16 {
    ($($bounded_int_name:ident),*) => {
        $(
            impl From<$bounded_int_name<{ u16::MIN as _ }, { u16::MAX as _ }>> for u16 {
                fn from(value: $bounded_int_name<0, 65535>) -> Self {
                    value.inner as u16
                }
            }
        )*
    };
}

macro_rules! impl_from_for_i32 {
    ($($bounded_int_name:ident),*) => {
        $(
            impl From<$bounded_int_name<{ i32::MIN as _ }, { i32::MAX as _ }>> for i32 {
                fn from(value: $bounded_int_name<-2147483648, 2147483647>) -> Self {
                    value.inner as i32
                }
            }
        )*
    };
}

macro_rules! impl_from_for_u32 {
    ($($bounded_int_name:ident),*) => {
        $(
            impl From<$bounded_int_name<{ u32::MIN as _ }, { u32::MAX as _ }>> for u32 {
                fn from(value: $bounded_int_name<0, 4294967295>) -> Self {
                    value.inner as u32
                }
            }
        )*
    };
}

impl_from_for_i8!(BoundedInt16, BoundedInt32, BoundedInt64, BoundedIsize);
impl_from_for_u8!(
    BoundedUInt16,
    BoundedUInt32,
    BoundedUInt64,
    BoundedUsize,
    BoundedInt16,
    BoundedInt32,
    BoundedInt64,
    BoundedIsize
);
impl_from_for_i16!(BoundedInt32, BoundedInt64, BoundedIsize);
impl_from_for_u16!(
    BoundedUInt32,
    BoundedUInt64,
    BoundedUsize,
    BoundedInt32,
    BoundedInt64,
    BoundedIsize
);
impl_from_for_i32!(BoundedInt64, BoundedIsize);
impl_from_for_u32!(BoundedUInt64, BoundedUsize, BoundedInt64);

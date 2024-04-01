use crate::{AnyBitPattern, ZeroableInOption};
use core::num::{
  NonZeroI128, NonZeroI16, NonZeroI32, NonZeroI64, NonZeroI8, NonZeroIsize,
  NonZeroU128, NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU8, NonZeroUsize,
};

// Note(Lokathor): This is the neat part!!
unsafe impl<T: AnyBitPatternInOption> AnyBitPattern for Option<T> {}

/// Trait for types which are [AnyBitPattern](AnyBitPattern) when wrapped in
/// [Option](core::option::Option).
///
/// ## Safety
///
/// * `Option<YourType>` must uphold the same invariants as
///   [AnyBitPattern](AnyBitPattern).
pub unsafe trait AnyBitPatternInOption: ZeroableInOption {}

unsafe impl AnyBitPatternInOption for NonZeroI8 {}
unsafe impl AnyBitPatternInOption for NonZeroI16 {}
unsafe impl AnyBitPatternInOption for NonZeroI32 {}
unsafe impl AnyBitPatternInOption for NonZeroI64 {}
unsafe impl AnyBitPatternInOption for NonZeroI128 {}
unsafe impl AnyBitPatternInOption for NonZeroIsize {}
unsafe impl AnyBitPatternInOption for NonZeroU8 {}
unsafe impl AnyBitPatternInOption for NonZeroU16 {}
unsafe impl AnyBitPatternInOption for NonZeroU32 {}
unsafe impl AnyBitPatternInOption for NonZeroU64 {}
unsafe impl AnyBitPatternInOption for NonZeroU128 {}
unsafe impl AnyBitPatternInOption for NonZeroUsize {}

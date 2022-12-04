use super::*;

// Note(Lokathor): This is the neat part!!
unsafe impl<T: AnyBitPatternInOption> AnyBitPattern for Option<T> {}

/// Trait for types which are [AnyBitPattern](AnyBitPattern) when wrapped in
/// [Option](core::option::Option).
///
/// ## Safety
///
/// * `Option<YourType>` must uphold the same invariants as
///   [AnyBitPattern](AnyBitPattern).
pub unsafe trait AnyBitPatternInOption:
  ZeroableInOption + Copy + 'static
{
}

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

unsafe impl<T: AnyBitPatternInOption> AnyBitPatternInOption for Wrapping<T> {}
unsafe impl<T: AnyBitPatternInOption> AnyBitPatternInOption
  for core::cmp::Reverse<T>
{
}

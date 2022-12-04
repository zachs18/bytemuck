use super::*;

// Note(Lokathor): This is the neat part!!
unsafe impl<T: NoUninitInOption> NoUninit for Option<T> {}

/// Trait for types which are [NoUninit](NoUninit) when wrapped in
/// [Option](core::option::Option).
///
/// ## Safety
///
/// * `Option<YourType>` must uphold the same invariants as
///   [NoUninit](NoUninit).
pub unsafe trait NoUninitInOption: Copy + 'static {}

unsafe impl NoUninitInOption for NonZeroI8 {}
unsafe impl NoUninitInOption for NonZeroI16 {}
unsafe impl NoUninitInOption for NonZeroI32 {}
unsafe impl NoUninitInOption for NonZeroI64 {}
unsafe impl NoUninitInOption for NonZeroI128 {}
unsafe impl NoUninitInOption for NonZeroIsize {}
unsafe impl NoUninitInOption for NonZeroU8 {}
unsafe impl NoUninitInOption for NonZeroU16 {}
unsafe impl NoUninitInOption for NonZeroU32 {}
unsafe impl NoUninitInOption for NonZeroU64 {}
unsafe impl NoUninitInOption for NonZeroU128 {}
unsafe impl NoUninitInOption for NonZeroUsize {}

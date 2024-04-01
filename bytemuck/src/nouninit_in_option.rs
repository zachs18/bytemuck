use core::num::{
  NonZeroI128, NonZeroI16, NonZeroI32, NonZeroI64, NonZeroI8, NonZeroIsize,
  NonZeroU128, NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU8, NonZeroUsize,
};

use crate::NoUninit;

// Note(Lokathor): This is the neat part!!
unsafe impl<T: NoUninitInOption> NoUninit for Option<T> {}

/// Trait for types which are [NoUninit](NoUninit) when wrapped in
/// [Option](core::option::Option).
///
/// ## Safety
///
/// * `Option<T>` must uphold the same invariants as [NoUninit](NoUninit).
/// * **Reminder:** pointers are **not** NoUninit! **Do not** mix this trait
///   with a newtype over [NonNull](core::ptr::NonNull).
pub unsafe trait NoUninitInOption: Sized {}

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

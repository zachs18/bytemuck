use crate::Zeroable;
use core::{
  num::{
    NonZeroI128, NonZeroI16, NonZeroI32, NonZeroI64, NonZeroI8, NonZeroIsize,
    NonZeroU128, NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU8, NonZeroUsize,
  },
  ptr::NonNull,
};

// Note(Lokathor): This is the neat part!!
unsafe impl<T: ZeroableInOption> Zeroable for Option<T> {}

/// Trait for types which are [Zeroable] when wrapped in
/// [Option](core::option::Option).
///
/// ## Safety
///
/// * `Option<YourType>` must uphold the same invariants as [Zeroable].
pub unsafe trait ZeroableInOption: Sized {}

unsafe impl ZeroableInOption for NonZeroI8 {}
unsafe impl ZeroableInOption for NonZeroI16 {}
unsafe impl ZeroableInOption for NonZeroI32 {}
unsafe impl ZeroableInOption for NonZeroI64 {}
unsafe impl ZeroableInOption for NonZeroI128 {}
unsafe impl ZeroableInOption for NonZeroIsize {}
unsafe impl ZeroableInOption for NonZeroU8 {}
unsafe impl ZeroableInOption for NonZeroU16 {}
unsafe impl ZeroableInOption for NonZeroU32 {}
unsafe impl ZeroableInOption for NonZeroU64 {}
unsafe impl ZeroableInOption for NonZeroU128 {}
unsafe impl ZeroableInOption for NonZeroUsize {}

// Note: this does not create NULL vtable because we get `None` anyway.
unsafe impl<T: ?Sized> ZeroableInOption for NonNull<T> {}
unsafe impl<T: ?Sized> ZeroableInOption for &'_ T {}
unsafe impl<T: ?Sized> ZeroableInOption for &'_ mut T {}

#[cfg(feature = "alloc")]
#[cfg_attr(feature = "nightly_docs", doc(cfg(feature = "alloc")))]
unsafe impl<T: ?Sized> ZeroableInOption for alloc::boxed::Box<T> {}

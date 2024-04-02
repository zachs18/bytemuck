use core::{
  marker::{PhantomData, PhantomPinned},
  mem::ManuallyDrop,
  num::{Saturating, Wrapping},
};

/// Trait for types that can be safely created with
/// [`zeroed`](core::mem::zeroed).
///
/// An all-zeroes value may or may not be the same value as the
/// [Default](core::default::Default) value of the type.
///
/// ## Safety
///
/// * Your type must be inhabited (eg: no
///   [Infallible](core::convert::Infallible)).
/// * Your type must be allowed to be an "all zeroes" bit pattern (eg: no
///   [`NonNull<T>`](core::ptr::NonNull)).
///
/// ## Features
///
/// Some `impl`s are feature gated due to the MSRV policy:
///
/// * `MaybeUninit<T>` was not available in 1.34.0, but is available under the
///   `zeroable_maybe_uninit` feature flag.
/// * `Atomic*` types require Rust 1.60.0 or later to work on certain platforms,
///   but is available under the `zeroable_atomics` feature flag.
/// * `[T; N]` for arbitrary `N` requires the `min_const_generics` feature flag.
pub unsafe trait Zeroable {
  /// Calls [`zeroed`](core::mem::zeroed).
  ///
  /// This is a trait method so that you can write `MyType::zeroed()` in your
  /// code. It is a contract of this trait that if you implement it on your type
  /// you **must not** override this method.
  #[inline]
  fn zeroed() -> Self
  where
    Self: Sized,
  {
    unsafe { core::mem::zeroed() }
  }

  /// Fill all bytes of `self` with zeroes (see [`Zeroable`]).
  ///
  /// This is similar to `*self = Zeroable::zeroed()`, but guarantees that any
  /// padding bytes in `self` are zeroed as well.
  ///
  /// Depending on the implementing type, the previous value may or may not be
  /// dropped before the new all-zero value is written. If dropping the previous
  /// value fails, then `self` will be left in a valid (but not necessarily
  /// all-zero-byte) state.
  ///
  /// Note for implementors: The default implementation does not drop `self`
  /// before writing zeros. If your type has drop glue you may want to override
  /// this method.
  #[inline]
  fn write_zero(&mut self) {
    let guard = EnsureZeroWrite(self);
    drop(guard);
  }
}

struct EnsureZeroWrite<T: ?Sized>(*mut T);
impl<T: ?Sized> Drop for EnsureZeroWrite<T> {
  #[inline(always)]
  fn drop(&mut self) {
    let bytes = core::mem::size_of_val(self);
    unsafe {
      core::ptr::write_bytes(self.0.cast::<u8>(), 0u8, bytes);
    }
  }
}

unsafe impl<T: Zeroable> Zeroable for [T] {
  #[inline]
  fn write_zero(&mut self) {
    if core::mem::needs_drop::<T>() {
      // If `T` needs to be dropped then we should do this one item at a time,
      // in case one of the intermediate drops does a panic.
      self.iter_mut().for_each(T::write_zero);
    } else {
      // Otherwise we can be really fast and just fill everthing with zeros.
      let guard = EnsureZeroWrite(self);
      drop(guard);
    }
  }
}

// all-zeros is valid UTF-8
unsafe impl Zeroable for str {}

unsafe impl Zeroable for () {}
unsafe impl Zeroable for bool {}
unsafe impl Zeroable for char {}
unsafe impl Zeroable for u8 {}
unsafe impl Zeroable for i8 {}
unsafe impl Zeroable for u16 {}
unsafe impl Zeroable for i16 {}
unsafe impl Zeroable for u32 {}
unsafe impl Zeroable for i32 {}
unsafe impl Zeroable for u64 {}
unsafe impl Zeroable for i64 {}
unsafe impl Zeroable for usize {}
unsafe impl Zeroable for isize {}
unsafe impl Zeroable for u128 {}
unsafe impl Zeroable for i128 {}
unsafe impl Zeroable for f32 {}
unsafe impl Zeroable for f64 {}
unsafe impl<T: Zeroable> Zeroable for Wrapping<T> {}
unsafe impl<T: Zeroable> Zeroable for Saturating<T> {}
unsafe impl<T: Zeroable> Zeroable for core::cmp::Reverse<T> {}

// Note: we can't implement this for all `T: ?Sized` types because it would
// create NULL pointers for vtables.
// Maybe one day this could be changed to be implemented for
// `T: ?Sized where <T as core::ptr::Pointee>::Metadata: Zeroable`.
unsafe impl<T> Zeroable for *mut T {}
unsafe impl<T> Zeroable for *const T {}
unsafe impl<T> Zeroable for *mut [T] {}
unsafe impl<T> Zeroable for *const [T] {}
unsafe impl Zeroable for *mut str {}
unsafe impl Zeroable for *const str {}

unsafe impl<T: ?Sized> Zeroable for PhantomData<T> {}
unsafe impl Zeroable for PhantomPinned {}

// Don't need to override `write_zero`, since ManuallyDrop doesn't drop anyway
unsafe impl<T: Zeroable + ?Sized> Zeroable for ManuallyDrop<T> {}
unsafe impl<T: Zeroable + ?Sized> Zeroable for core::cell::UnsafeCell<T> {
  fn write_zero(&mut self) {
    unsafe {
      let guard = EnsureZeroWrite(self);
      core::ptr::drop_in_place(guard.0);
      drop(guard);
    }
  }
}
unsafe impl<T: Zeroable + ?Sized> Zeroable for core::cell::Cell<T> {
  fn write_zero(&mut self) {
    unsafe {
      let guard = EnsureZeroWrite(self);
      core::ptr::drop_in_place(guard.0);
      drop(guard);
    }
  }
}

mod atomic_impls {
  use super::Zeroable;

  #[cfg(target_has_atomic = "8")]
  #[cfg_attr(feature = "nightly_docs", doc(cfg(target_has_atomic = "8")))]
  unsafe impl Zeroable for core::sync::atomic::AtomicBool {}
  #[cfg(target_has_atomic = "8")]
  #[cfg_attr(feature = "nightly_docs", doc(cfg(target_has_atomic = "8")))]
  unsafe impl Zeroable for core::sync::atomic::AtomicU8 {}
  #[cfg(target_has_atomic = "8")]
  #[cfg_attr(feature = "nightly_docs", doc(cfg(target_has_atomic = "8")))]
  unsafe impl Zeroable for core::sync::atomic::AtomicI8 {}

  #[cfg(target_has_atomic = "16")]
  #[cfg_attr(feature = "nightly_docs", doc(cfg(target_has_atomic = "16")))]
  unsafe impl Zeroable for core::sync::atomic::AtomicU16 {}
  #[cfg(target_has_atomic = "16")]
  #[cfg_attr(feature = "nightly_docs", doc(cfg(target_has_atomic = "16")))]
  unsafe impl Zeroable for core::sync::atomic::AtomicI16 {}

  #[cfg(target_has_atomic = "32")]
  #[cfg_attr(feature = "nightly_docs", doc(cfg(target_has_atomic = "32")))]
  unsafe impl Zeroable for core::sync::atomic::AtomicU32 {}
  #[cfg(target_has_atomic = "32")]
  #[cfg_attr(feature = "nightly_docs", doc(cfg(target_has_atomic = "32")))]
  unsafe impl Zeroable for core::sync::atomic::AtomicI32 {}

  #[cfg(target_has_atomic = "64")]
  #[cfg_attr(feature = "nightly_docs", doc(cfg(target_has_atomic = "64")))]
  unsafe impl Zeroable for core::sync::atomic::AtomicU64 {}
  #[cfg(target_has_atomic = "64")]
  #[cfg_attr(feature = "nightly_docs", doc(cfg(target_has_atomic = "64")))]
  unsafe impl Zeroable for core::sync::atomic::AtomicI64 {}

  #[cfg(target_has_atomic = "ptr")]
  #[cfg_attr(feature = "nightly_docs", doc(cfg(target_has_atomic = "ptr")))]
  unsafe impl Zeroable for core::sync::atomic::AtomicUsize {}
  #[cfg(target_has_atomic = "ptr")]
  #[cfg_attr(feature = "nightly_docs", doc(cfg(target_has_atomic = "ptr")))]
  unsafe impl Zeroable for core::sync::atomic::AtomicIsize {}

  #[cfg(target_has_atomic = "ptr")]
  #[cfg_attr(feature = "nightly_docs", doc(cfg(target_has_atomic = "ptr")))]
  unsafe impl<T> Zeroable for core::sync::atomic::AtomicPtr<T> {}

  #[cfg(feature = "nightly_atomic_128")]
  #[cfg(target_has_atomic = "128")]
  #[cfg_attr(
    feature = "nightly_docs",
    doc(cfg(all(target_has_atomic = "128", feature = "nightly_atomic_128")))
  )]
  unsafe impl Zeroable for core::sync::atomic::AtomicU128 {}
  #[cfg(feature = "nightly_atomic_128")]
  #[cfg(target_has_atomic = "128")]
  #[cfg_attr(
    feature = "nightly_docs",
    doc(cfg(all(target_has_atomic = "128", feature = "nightly_atomic_128")))
  )]
  unsafe impl Zeroable for core::sync::atomic::AtomicI128 {}
}

unsafe impl<T> Zeroable for core::mem::MaybeUninit<T> {}

unsafe impl<A: Zeroable + ?Sized> Zeroable for (A,) {}
unsafe impl<A: Zeroable, B: Zeroable + ?Sized> Zeroable for (A, B) {}
unsafe impl<A: Zeroable, B: Zeroable, C: Zeroable + ?Sized> Zeroable
  for (A, B, C)
{
}
unsafe impl<A: Zeroable, B: Zeroable, C: Zeroable, D: Zeroable + ?Sized>
  Zeroable for (A, B, C, D)
{
}
unsafe impl<
    A: Zeroable,
    B: Zeroable,
    C: Zeroable,
    D: Zeroable,
    E: Zeroable + ?Sized,
  > Zeroable for (A, B, C, D, E)
{
}
unsafe impl<
    A: Zeroable,
    B: Zeroable,
    C: Zeroable,
    D: Zeroable,
    E: Zeroable,
    F: Zeroable + ?Sized,
  > Zeroable for (A, B, C, D, E, F)
{
}
unsafe impl<
    A: Zeroable,
    B: Zeroable,
    C: Zeroable,
    D: Zeroable,
    E: Zeroable,
    F: Zeroable,
    G: Zeroable + ?Sized,
  > Zeroable for (A, B, C, D, E, F, G)
{
}
unsafe impl<
    A: Zeroable,
    B: Zeroable,
    C: Zeroable,
    D: Zeroable,
    E: Zeroable,
    F: Zeroable,
    G: Zeroable,
    H: Zeroable + ?Sized,
  > Zeroable for (A, B, C, D, E, F, G, H)
{
}

unsafe impl<T, const N: usize> Zeroable for [T; N] where T: Zeroable {}

impl_unsafe_marker_for_simd!(
  #[cfg(target_arch = "wasm32")]
  unsafe impl Zeroable for core::arch::wasm32::{v128}
);

impl_unsafe_marker_for_simd!(
  #[cfg(target_arch = "aarch64")]
  unsafe impl Zeroable for core::arch::aarch64::{
    float32x2_t, float32x2x2_t, float32x2x3_t, float32x2x4_t, float32x4_t,
    float32x4x2_t, float32x4x3_t, float32x4x4_t, float64x1_t, float64x1x2_t,
    float64x1x3_t, float64x1x4_t, float64x2_t, float64x2x2_t, float64x2x3_t,
    float64x2x4_t, int16x4_t, int16x4x2_t, int16x4x3_t, int16x4x4_t, int16x8_t,
    int16x8x2_t, int16x8x3_t, int16x8x4_t, int32x2_t, int32x2x2_t, int32x2x3_t,
    int32x2x4_t, int32x4_t, int32x4x2_t, int32x4x3_t, int32x4x4_t, int64x1_t,
    int64x1x2_t, int64x1x3_t, int64x1x4_t, int64x2_t, int64x2x2_t, int64x2x3_t,
    int64x2x4_t, int8x16_t, int8x16x2_t, int8x16x3_t, int8x16x4_t, int8x8_t,
    int8x8x2_t, int8x8x3_t, int8x8x4_t, poly16x4_t, poly16x4x2_t, poly16x4x3_t,
    poly16x4x4_t, poly16x8_t, poly16x8x2_t, poly16x8x3_t, poly16x8x4_t,
    poly64x1_t, poly64x1x2_t, poly64x1x3_t, poly64x1x4_t, poly64x2_t,
    poly64x2x2_t, poly64x2x3_t, poly64x2x4_t, poly8x16_t, poly8x16x2_t,
    poly8x16x3_t, poly8x16x4_t, poly8x8_t, poly8x8x2_t, poly8x8x3_t, poly8x8x4_t,
    uint16x4_t, uint16x4x2_t, uint16x4x3_t, uint16x4x4_t, uint16x8_t,
    uint16x8x2_t, uint16x8x3_t, uint16x8x4_t, uint32x2_t, uint32x2x2_t,
    uint32x2x3_t, uint32x2x4_t, uint32x4_t, uint32x4x2_t, uint32x4x3_t,
    uint32x4x4_t, uint64x1_t, uint64x1x2_t, uint64x1x3_t, uint64x1x4_t,
    uint64x2_t, uint64x2x2_t, uint64x2x3_t, uint64x2x4_t, uint8x16_t,
    uint8x16x2_t, uint8x16x3_t, uint8x16x4_t, uint8x8_t, uint8x8x2_t,
    uint8x8x3_t, uint8x8x4_t,
  }
);

impl_unsafe_marker_for_simd!(
  #[cfg(target_arch = "x86")]
  unsafe impl Zeroable for core::arch::x86::{
    __m128i, __m128, __m128d,
    __m256i, __m256, __m256d,
  }
);

impl_unsafe_marker_for_simd!(
  #[cfg(target_arch = "x86_64")]
    unsafe impl Zeroable for core::arch::x86_64::{
        __m128i, __m128, __m128d,
        __m256i, __m256, __m256d,
    }
);

#[cfg(feature = "nightly_portable_simd")]
#[cfg_attr(
  feature = "nightly_docs",
  doc(cfg(feature = "nightly_portable_simd"))
)]
unsafe impl<T, const N: usize> Zeroable for core::simd::Simd<T, N>
where
  T: core::simd::SimdElement + Zeroable,
  core::simd::LaneCount<N>: core::simd::SupportedLaneCount,
{
}

impl_unsafe_marker_for_simd!(
  #[cfg(all(target_arch = "x86", feature = "nightly_stdsimd"))]
  unsafe impl Zeroable for core::arch::x86::{
    __m128bh, __m256bh, __m512,
    __m512bh, __m512d, __m512i,
  }
);

impl_unsafe_marker_for_simd!(
  #[cfg(all(target_arch = "x86_64", feature = "nightly_stdsimd"))]
  unsafe impl Zeroable for core::arch::x86_64::{
    __m128bh, __m256bh, __m512,
    __m512bh, __m512d, __m512i,
  }
);

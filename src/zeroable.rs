use super::*;

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
pub unsafe trait Zeroable: Sized {
  /// Calls [`zeroed`](core::mem::zeroed).
  ///
  /// This is a trait method so that you can write `MyType::zeroed()` in your
  /// code. It is a contract of this trait that if you implement it on your type
  /// you **must not** override this method.
  #[inline]
  fn zeroed() -> Self {
    unsafe { core::mem::zeroed() }
  }
}
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

unsafe impl<T: Zeroable> Zeroable for PhantomData<T> {}
unsafe impl Zeroable for PhantomPinned {}
unsafe impl<T: Zeroable> Zeroable for ManuallyDrop<T> {}

unsafe impl<T: Zeroable> Zeroable for core::cell::UnsafeCell<T> {}
unsafe impl<T: Zeroable> Zeroable for core::cell::Cell<T> {}
unsafe impl<T: Zeroable> Zeroable for Wrapping<T> {}
unsafe impl<T: Zeroable> Zeroable for core::cmp::Reverse<T> {}

#[cfg(target_has_atomic = "8")]
unsafe impl Zeroable for core::sync::atomic::AtomicI8 {}
#[cfg(target_has_atomic = "8")]
unsafe impl Zeroable for core::sync::atomic::AtomicU8 {}
#[cfg(target_has_atomic = "16")]
unsafe impl Zeroable for core::sync::atomic::AtomicI16 {}
#[cfg(target_has_atomic = "16")]
unsafe impl Zeroable for core::sync::atomic::AtomicU16 {}
#[cfg(target_has_atomic = "32")]
unsafe impl Zeroable for core::sync::atomic::AtomicI32 {}
#[cfg(target_has_atomic = "32")]
unsafe impl Zeroable for core::sync::atomic::AtomicU32 {}
#[cfg(target_has_atomic = "64")]
unsafe impl Zeroable for core::sync::atomic::AtomicI64 {}
#[cfg(target_has_atomic = "64")]
unsafe impl Zeroable for core::sync::atomic::AtomicU64 {}
#[cfg(target_has_atomic = "128")]
unsafe impl Zeroable for core::sync::atomic::AtomicI128 {}
#[cfg(target_has_atomic = "128")]
unsafe impl Zeroable for core::sync::atomic::AtomicU128 {}
#[cfg(target_has_atomic = "ptr")]
unsafe impl Zeroable for core::sync::atomic::AtomicIsize {}
#[cfg(target_has_atomic = "ptr")]
unsafe impl Zeroable for core::sync::atomic::AtomicUsize {}
#[cfg(target_has_atomic = "ptr")]
unsafe impl<T> Zeroable for core::sync::atomic::AtomicPtr<T> {}

unsafe impl<T> Zeroable for *mut T {}
unsafe impl<T> Zeroable for *const T {}

unsafe impl<T> Zeroable for core::mem::MaybeUninit<T> {}

unsafe impl<A: Zeroable> Zeroable for (A,) {}
unsafe impl<A: Zeroable, B: Zeroable> Zeroable for (A, B) {}
unsafe impl<A: Zeroable, B: Zeroable, C: Zeroable> Zeroable for (A, B, C) {}
unsafe impl<A: Zeroable, B: Zeroable, C: Zeroable, D: Zeroable> Zeroable
  for (A, B, C, D)
{
}
unsafe impl<A: Zeroable, B: Zeroable, C: Zeroable, D: Zeroable, E: Zeroable>
  Zeroable for (A, B, C, D, E)
{
}
unsafe impl<
    A: Zeroable,
    B: Zeroable,
    C: Zeroable,
    D: Zeroable,
    E: Zeroable,
    F: Zeroable,
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
    G: Zeroable,
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
    H: Zeroable,
  > Zeroable for (A, B, C, D, E, F, G, H)
{
}

unsafe impl<T, const N: usize> Zeroable for [T; N] where T: Zeroable {}

#[cfg(target_arch = "wasm32")]
simd_impls!(
    unsafe impl Zeroable for wasm32::{v128}
);

#[cfg(target_arch = "aarch64")]
simd_impls!(
    unsafe impl Zeroable for aarch64::{
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

#[cfg(target_arch = "x86")]
simd_impls!(
    unsafe impl Zeroable for x86::{
        __m128i, __m128, __m128d,
        __m256i, __m256, __m256d,
    }
);

#[cfg(target_arch = "x86_64")]
simd_impls!(
    unsafe impl Zeroable for x86_64::{
        __m128i, __m128, __m128d,
        __m256i, __m256, __m256d,
    }
);

#[cfg(feature = "nightly_portable_simd")]
unsafe impl<T, const N: usize> Zeroable for core::simd::Simd<T, N>
where
  T: core::simd::SimdElement + Zeroable,
  core::simd::LaneCount<N>: core::simd::SupportedLaneCount,
{
}

use core::{
  marker::{PhantomData, PhantomPinned},
  mem::ManuallyDrop,
  num::Wrapping,
};

use crate::Zeroable;

/// Marker trait for "plain old data" types that are valid for any bit pattern.
///
/// The requirements for this is very similar to [`Pod`],
/// except that the type can allow uninit (or padding) bytes.
/// This limits what you can do with a type of this kind, but also broadens the
/// included types to `repr(C)` `struct`s that contain padding as well as
/// `union`s. Notably, you can only cast *immutable* references and *owned*
/// values into [`AnyBitPattern`] types, not *mutable* references.
///
/// [`Pod`] is a subset of [`AnyBitPattern`], meaning that any `T: Pod` is also
/// [`AnyBitPattern`] but any `T: AnyBitPattern` is not necessarily [`Pod`].
///
/// [`AnyBitPattern`] is a subset of [`Zeroable`], meaning that any `T:
/// AnyBitPattern` is also [`Zeroable`], but any `T: Zeroable` is not
/// necessarily [`AnyBitPattern`]
///
/// # Derive
///
/// A `#[derive(AnyBitPattern)]` macro is provided under the `derive` feature
/// flag which will automatically validate the requirements of this trait and
/// implement the trait for you for both structs and enums. This is the
/// recommended method for implementing the trait, however it's also possible to
/// do manually. If you implement it manually, you *must* carefully follow the
/// below safety rules.
///
/// * *NOTE: even `C-style`, fieldless enums are intentionally **excluded** from
/// this trait, since it is **unsound** for an enum to have a discriminant value
/// that is not one of its defined variants.
///
/// # Safety
///
/// Similar to [`Pod`] except we disregard the rule about it must not contain
/// uninit bytes. Still, this is a quite strong guarantee about a type, so *be
/// careful* when implementing it manually.
///
/// * The type must be inhabited (eg: no
///   [Infallible](core::convert::Infallible)).
/// * The type must be valid for any bit pattern of its backing memory.
/// * Structs need to have all fields also be `AnyBitPattern`.
/// * It is disallowed for types to contain pointer types, `Cell`, `UnsafeCell`,
///   atomics, and any other forms of interior mutability.
/// * More precisely: A shared reference to the type must allow reads, and
///   *only* reads. RustBelt's separation logic is based on the notion that a
///   type is allowed to define a sharing predicate, its own invariant that must
///   hold for shared references, and this predicate is the reasoning that allow
///   it to deal with atomic and cells etc. We require the sharing predicate to
///   be trivial and permit only read-only access.
/// * There's probably more, don't mess it up (I mean it).
pub unsafe trait AnyBitPattern: Zeroable {}

unsafe impl<T: AnyBitPattern> AnyBitPattern for [T] {}

unsafe impl AnyBitPattern for () {}
unsafe impl AnyBitPattern for u8 {}
unsafe impl AnyBitPattern for i8 {}
unsafe impl AnyBitPattern for u16 {}
unsafe impl AnyBitPattern for i16 {}
unsafe impl AnyBitPattern for u32 {}
unsafe impl AnyBitPattern for i32 {}
unsafe impl AnyBitPattern for u64 {}
unsafe impl AnyBitPattern for i64 {}
unsafe impl AnyBitPattern for usize {}
unsafe impl AnyBitPattern for isize {}
unsafe impl AnyBitPattern for u128 {}
unsafe impl AnyBitPattern for i128 {}
unsafe impl AnyBitPattern for f32 {}
unsafe impl AnyBitPattern for f64 {}
unsafe impl<T: AnyBitPattern> AnyBitPattern for Wrapping<T> {}
unsafe impl<T: AnyBitPattern> AnyBitPattern for core::cmp::Reverse<T> {}

// Note: we can't implement this for all `T: ?Sized` types because it would
// reinterpret the metadata which may not be AnyBitPattern..
// Maybe one day this could be changed to be implemented for
// `T: ?Sized where <T as core::ptr::Pointee>::Metadata: AnyBitPattern`.
#[cfg(feature = "unstable_pod_pointers")]
#[cfg_attr(
  feature = "nightly_docs",
  doc(cfg(feature = "unstable_pod_pointers"))
)]
mod pointer_impls {
  use crate::{AnyBitPattern, AnyBitPatternInOption};
  use core::ptr::NonNull;

  /// Note that transmuting to a pointer produces a pointer with no provenance.
  unsafe impl<T> AnyBitPattern for *mut T {}
  /// Note that transmuting to a pointer produces a pointer with no provenance.
  unsafe impl<T> AnyBitPattern for *const T {}
  /// Note that transmuting to a pointer produces a pointer with no provenance.
  unsafe impl<T> AnyBitPattern for *mut [T] {}
  /// Note that transmuting to a pointer produces a pointer with no provenance.
  unsafe impl<T> AnyBitPattern for *const [T] {}
  /// Note that transmuting to a pointer produces a pointer with no provenance.
  unsafe impl AnyBitPattern for *mut str {}
  /// Note that transmuting to a pointer produces a pointer with no provenance.
  unsafe impl AnyBitPattern for *const str {}
  /// Note that transmuting to a pointer produces a pointer with no provenance.
  unsafe impl<T> AnyBitPatternInOption for NonNull<T> {}
  /// Note that transmuting to a pointer produces a pointer with no provenance.
  unsafe impl<T> AnyBitPatternInOption for NonNull<[T]> {}
  /// Note that transmuting to a pointer produces a pointer with no provenance.
  unsafe impl AnyBitPatternInOption for NonNull<str> {}
}

unsafe impl<T: ?Sized> AnyBitPattern for PhantomData<T> {}
unsafe impl AnyBitPattern for PhantomPinned {}

// Don't need to override `write_zero`, since ManuallyDrop doesn't drop anyway
unsafe impl<T: AnyBitPattern + ?Sized> AnyBitPattern for ManuallyDrop<T> {}
unsafe impl<T: AnyBitPattern + ?Sized> AnyBitPattern
  for core::cell::UnsafeCell<T>
{
}
unsafe impl<T: AnyBitPattern + ?Sized> AnyBitPattern for core::cell::Cell<T> {}

mod atomic_impls {
  use super::AnyBitPattern;

  #[cfg(target_has_atomic = "8")]
  #[cfg_attr(feature = "nightly_docs", doc(cfg(target_has_atomic = "8")))]
  unsafe impl AnyBitPattern for core::sync::atomic::AtomicBool {}
  #[cfg(target_has_atomic = "8")]
  #[cfg_attr(feature = "nightly_docs", doc(cfg(target_has_atomic = "8")))]
  unsafe impl AnyBitPattern for core::sync::atomic::AtomicU8 {}
  #[cfg(target_has_atomic = "8")]
  #[cfg_attr(feature = "nightly_docs", doc(cfg(target_has_atomic = "8")))]
  unsafe impl AnyBitPattern for core::sync::atomic::AtomicI8 {}

  #[cfg(target_has_atomic = "16")]
  #[cfg_attr(feature = "nightly_docs", doc(cfg(target_has_atomic = "16")))]
  unsafe impl AnyBitPattern for core::sync::atomic::AtomicU16 {}
  #[cfg(target_has_atomic = "16")]
  #[cfg_attr(feature = "nightly_docs", doc(cfg(target_has_atomic = "16")))]
  unsafe impl AnyBitPattern for core::sync::atomic::AtomicI16 {}

  #[cfg(target_has_atomic = "32")]
  #[cfg_attr(feature = "nightly_docs", doc(cfg(target_has_atomic = "32")))]
  unsafe impl AnyBitPattern for core::sync::atomic::AtomicU32 {}
  #[cfg(target_has_atomic = "32")]
  #[cfg_attr(feature = "nightly_docs", doc(cfg(target_has_atomic = "32")))]
  unsafe impl AnyBitPattern for core::sync::atomic::AtomicI32 {}

  #[cfg(target_has_atomic = "64")]
  #[cfg_attr(feature = "nightly_docs", doc(cfg(target_has_atomic = "64")))]
  unsafe impl AnyBitPattern for core::sync::atomic::AtomicU64 {}
  #[cfg(target_has_atomic = "64")]
  #[cfg_attr(feature = "nightly_docs", doc(cfg(target_has_atomic = "64")))]
  unsafe impl AnyBitPattern for core::sync::atomic::AtomicI64 {}

  #[cfg(target_has_atomic = "ptr")]
  #[cfg_attr(feature = "nightly_docs", doc(cfg(target_has_atomic = "ptr")))]
  unsafe impl AnyBitPattern for core::sync::atomic::AtomicUsize {}
  #[cfg(target_has_atomic = "ptr")]
  #[cfg_attr(feature = "nightly_docs", doc(cfg(target_has_atomic = "ptr")))]
  unsafe impl AnyBitPattern for core::sync::atomic::AtomicIsize {}

  #[cfg(target_has_atomic = "ptr")]
  #[cfg_attr(feature = "nightly_docs", doc(cfg(target_has_atomic = "ptr")))]
  unsafe impl<T> AnyBitPattern for core::sync::atomic::AtomicPtr<T> {}

  #[cfg(target_has_atomic = "128")]
  #[cfg_attr(feature = "nightly_docs", doc(cfg(target_has_atomic = "128")))]
  unsafe impl AnyBitPattern for core::sync::atomic::AtomicU128 {}
  #[cfg(target_has_atomic = "128")]
  #[cfg_attr(feature = "nightly_docs", doc(cfg(target_has_atomic = "128")))]
  unsafe impl AnyBitPattern for core::sync::atomic::AtomicI128 {}
}

unsafe impl<T> AnyBitPattern for core::mem::MaybeUninit<T> {}

unsafe impl<A: AnyBitPattern + ?Sized> AnyBitPattern for (A,) {}
unsafe impl<A: AnyBitPattern, B: AnyBitPattern + ?Sized> AnyBitPattern
  for (A, B)
{
}
unsafe impl<A: AnyBitPattern, B: AnyBitPattern, C: AnyBitPattern + ?Sized>
  AnyBitPattern for (A, B, C)
{
}
unsafe impl<
    A: AnyBitPattern,
    B: AnyBitPattern,
    C: AnyBitPattern,
    D: AnyBitPattern + ?Sized,
  > AnyBitPattern for (A, B, C, D)
{
}
unsafe impl<
    A: AnyBitPattern,
    B: AnyBitPattern,
    C: AnyBitPattern,
    D: AnyBitPattern,
    E: AnyBitPattern + ?Sized,
  > AnyBitPattern for (A, B, C, D, E)
{
}
unsafe impl<
    A: AnyBitPattern,
    B: AnyBitPattern,
    C: AnyBitPattern,
    D: AnyBitPattern,
    E: AnyBitPattern,
    F: AnyBitPattern + ?Sized,
  > AnyBitPattern for (A, B, C, D, E, F)
{
}
unsafe impl<
    A: AnyBitPattern,
    B: AnyBitPattern,
    C: AnyBitPattern,
    D: AnyBitPattern,
    E: AnyBitPattern,
    F: AnyBitPattern,
    G: AnyBitPattern + ?Sized,
  > AnyBitPattern for (A, B, C, D, E, F, G)
{
}
unsafe impl<
    A: AnyBitPattern,
    B: AnyBitPattern,
    C: AnyBitPattern,
    D: AnyBitPattern,
    E: AnyBitPattern,
    F: AnyBitPattern,
    G: AnyBitPattern,
    H: AnyBitPattern + ?Sized,
  > AnyBitPattern for (A, B, C, D, E, F, G, H)
{
}

unsafe impl<T, const N: usize> AnyBitPattern for [T; N] where T: AnyBitPattern {}

impl_unsafe_marker_for_simd!(
  #[cfg(target_arch = "wasm32")]
  unsafe impl AnyBitPattern for core::arch::wasm32::{v128}
);

impl_unsafe_marker_for_simd!(
  #[cfg(target_arch = "aarch64")]
  unsafe impl AnyBitPattern for core::arch::aarch64::{
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
  unsafe impl AnyBitPattern for core::arch::x86::{
    __m128i, __m128, __m128d,
    __m256i, __m256, __m256d,
  }
);

impl_unsafe_marker_for_simd!(
  #[cfg(target_arch = "x86_64")]
    unsafe impl AnyBitPattern for core::arch::x86_64::{
        __m128i, __m128, __m128d,
        __m256i, __m256, __m256d,
    }
);

#[cfg(feature = "nightly_portable_simd")]
#[cfg_attr(
  feature = "nightly_docs",
  doc(cfg(feature = "nightly_portable_simd"))
)]
unsafe impl<T, const N: usize> AnyBitPattern for core::simd::Simd<T, N>
where
  T: core::simd::SimdElement + AnyBitPattern,
  core::simd::LaneCount<N>: core::simd::SupportedLaneCount,
{
}

impl_unsafe_marker_for_simd!(
  #[cfg(all(target_arch = "x86", feature = "nightly_stdsimd"))]
  unsafe impl AnyBitPattern for core::arch::x86::{
    __m128bh, __m256bh, __m512,
    __m512bh, __m512d, __m512i,
  }
);

impl_unsafe_marker_for_simd!(
  #[cfg(all(target_arch = "x86_64", feature = "nightly_stdsimd"))]
  unsafe impl AnyBitPattern for core::arch::x86_64::{
    __m128bh, __m256bh, __m512,
    __m512bh, __m512d, __m512i,
  }
);

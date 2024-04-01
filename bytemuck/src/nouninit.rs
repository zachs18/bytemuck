use core::{
  marker::{PhantomData, PhantomPinned},
  mem::ManuallyDrop,
  num::{
    NonZeroI128, NonZeroI16, NonZeroI32, NonZeroI64, NonZeroI8, NonZeroIsize,
    NonZeroU128, NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU8, NonZeroUsize,
    Wrapping,
  },
};

/// Marker trait for "plain old data" types with no uninit (or padding) bytes.
///
/// The requirements for this is very similar to [`Pod`],
/// except that it doesn't require that all bit patterns of the type are valid,
/// i.e. it does not require the type to be [`Zeroable`][crate::Zeroable].
/// This limits what you can do with a type of this kind, but also broadens the
/// included types to things like C-style enums. Notably, you can only cast from
/// *immutable* references to a [`NoUninit`] type into *immutable* references of
/// any other type, no casting of mutable references or mutable references to
/// slices etc.
///
/// [`Pod`] is a subset of [`NoUninit`], meaning that any `T: Pod` is also
/// [`NoUninit`] but any `T: NoUninit` is not necessarily [`Pod`]. If possible,
/// prefer deriving [`Pod`] directly. To get more [`Pod`]-like functionality
/// for a type that is only [`NoUninit`], consider also implementing
/// [`CheckedBitPattern`][crate::CheckedBitPattern].
///
/// # Derive
///
/// A `#[derive(NoUninit)]` macro is provided under the `derive` feature flag
/// which will automatically validate the requirements of this trait and
/// implement the trait for you for both enums and structs. This is the
/// recommended method for implementing the trait, however it's also possible to
/// do manually. If you implement it manually, you *must* carefully follow the
/// below safety rules.
///
/// # Safety
///
/// The same as [`Pod`] except we disregard the rule about it must
/// allow any bit pattern (i.e. it does not need to be
/// [`Zeroable`][crate::Zeroable]). Still, this is a quite strong guarantee
/// about a type, so *be careful* whem implementing it manually.
///
/// * The type must not contain any uninit (or padding) bytes, either in the
///   middle or on the end (eg: no `#[repr(C)] struct Foo(u8, u16)`, which has
///   padding in the middle, and also no `#[repr(C)] struct Foo(u16, u8)`, which
///   has padding on the end).
/// * Structs need to have all fields also be `NoUninit`.
/// * Structs need to be `repr(C)` or `repr(transparent)`. In the case of
///   `repr(C)`, the `packed` and `align` repr modifiers can be used as long as
///   all other rules end up being followed.
/// * Enums need to have an explicit `#[repr(Int)]`
/// * Enums must have only fieldless variants (FIXME(zachs18): update this)
/// * There's probably more, don't mess it up (I mean it).
pub unsafe trait NoUninit {}

unsafe impl NoUninit for char {}

unsafe impl NoUninit for bool {}

unsafe impl NoUninit for NonZeroU8 {}
unsafe impl NoUninit for NonZeroI8 {}
unsafe impl NoUninit for NonZeroU16 {}
unsafe impl NoUninit for NonZeroI16 {}
unsafe impl NoUninit for NonZeroU32 {}
unsafe impl NoUninit for NonZeroI32 {}
unsafe impl NoUninit for NonZeroU64 {}
unsafe impl NoUninit for NonZeroI64 {}
unsafe impl NoUninit for NonZeroU128 {}
unsafe impl NoUninit for NonZeroI128 {}
unsafe impl NoUninit for NonZeroUsize {}
unsafe impl NoUninit for NonZeroIsize {}

unsafe impl NoUninit for () {}
unsafe impl NoUninit for u8 {}
unsafe impl NoUninit for i8 {}
unsafe impl NoUninit for u16 {}
unsafe impl NoUninit for i16 {}
unsafe impl NoUninit for u32 {}
unsafe impl NoUninit for i32 {}
unsafe impl NoUninit for u64 {}
unsafe impl NoUninit for i64 {}
unsafe impl NoUninit for usize {}
unsafe impl NoUninit for isize {}
unsafe impl NoUninit for u128 {}
unsafe impl NoUninit for i128 {}
unsafe impl NoUninit for f32 {}
unsafe impl NoUninit for f64 {}
unsafe impl<T: NoUninit> NoUninit for Wrapping<T> {}

// Note: we can't implement this for all `T: ?Sized` types because it would
// reinterpret the metadata which may not be NoUninit.
// Maybe one day this could be changed to be implemented for
// `T: ?Sized where <T as core::ptr::Pointee>::Metadata: NoUninit`.
#[cfg(feature = "unstable_pod_pointers")]
#[cfg_attr(
  feature = "nightly_docs",
  doc(cfg(feature = "unstable_pod_pointers"))
)]
mod pointer_impls {
  use crate::{NoUninit, NoUninitInOption};
  use core::ptr::NonNull;

  /// Note that transmuting from pointers discards provenance.
  unsafe impl<T> NoUninit for *const T {}
  /// Note that transmuting from pointers discards provenance.
  unsafe impl<T> NoUninit for *mut T {}
  /// Note that transmuting from pointers discards provenance.
  unsafe impl<T> NoUninit for *const [T] {}
  /// Note that transmuting from pointers discards provenance.
  unsafe impl<T> NoUninit for *mut [T] {}
  /// Note that transmuting from pointers discards provenance.
  unsafe impl NoUninit for *const str {}
  /// Note that transmuting from pointers discards provenance.
  unsafe impl NoUninit for *mut str {}
  /// Note that transmuting from pointers discards provenance.
  unsafe impl<T> NoUninitInOption for NonNull<T> {}

  // Note that `NoNull<T: ?Sized>` is NOT NoUninitInOption, since `None` leaves
  // the metadata uninit.
}

unsafe impl<T: ?Sized + 'static> NoUninit for PhantomData<T> {}
unsafe impl NoUninit for PhantomPinned {}
unsafe impl<T: NoUninit + ?Sized> NoUninit for ManuallyDrop<T> {}

// Note: MaybeUninit can NEVER be NoUninit.

unsafe impl<T, const N: usize> NoUninit for [T; N] where T: NoUninit {}

impl_unsafe_marker_for_simd!(
  #[cfg(all(target_arch = "wasm32", feature = "wasm_simd"))]
  unsafe impl NoUninit for core::arch::wasm32::{v128}
);

impl_unsafe_marker_for_simd!(
  #[cfg(all(target_arch = "aarch64", feature = "aarch64_simd"))]
  unsafe impl NoUninit for core::arch::aarch64::{
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
  unsafe impl NoUninit for core::arch::x86::{
    __m128i, __m128, __m128d,
    __m256i, __m256, __m256d,
  }
);

impl_unsafe_marker_for_simd!(
  #[cfg(target_arch = "x86_64")]
  unsafe impl NoUninit for core::arch::x86_64::{
    __m128i, __m128, __m128d,
    __m256i, __m256, __m256d,
  }
);

#[cfg(feature = "nightly_portable_simd")]
#[cfg_attr(
  feature = "nightly_docs",
  doc(cfg(feature = "nightly_portable_simd"))
)]
unsafe impl<T, const N: usize> NoUninit for core::simd::Simd<T, N>
where
  T: core::simd::SimdElement + NoUninit,
  core::simd::LaneCount<N>: core::simd::SupportedLaneCount,
{
}

impl_unsafe_marker_for_simd!(
  #[cfg(all(target_arch = "x86", feature = "nightly_stdsimd"))]
  unsafe impl NoUninit for core::arch::x86::{
    __m128bh, __m256bh, __m512,
    __m512bh, __m512d, __m512i,
  }
);

impl_unsafe_marker_for_simd!(
  #[cfg(all(target_arch = "x86_64", feature = "nightly_stdsimd"))]
  unsafe impl NoUninit for core::arch::x86_64::{
    __m128bh, __m256bh, __m512,
    __m512bh, __m512d, __m512i,
  }
);

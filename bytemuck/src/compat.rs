//! Stuff to allow some interoperability with version 1 of `bytemuck`
//!
//! * You must enable the `compat` feature of `bytemuck` v2 or you will not be
//!   able to use this module! This is generally done by adding the feature to
//!   the dependency in Cargo.toml like so:
//!
//!   `bytemuck = { version = "2", features = ["compat"] }`
//! * Generally you only need to use this module if you are interacting with
//!   APIs which expect types to implement `bytemuck` v1's traits, or you are
//!   using external types which only implement `bytemuck` v1's traits. For your
//!   own code, you do not need to use `bytemuck` v1, as no functionality has
//!   been removed.

use core::marker::Freeze;

/// Compatibility wrapper to allow using types that only implement `bytemuck`
/// 1.0's traits with `bytemuck` 2.0's functions, or vice versa.
///
/// It implements `crate::TransparentWrapper` to allow you to freely wrap and
/// peel it from types.
///
/// Note that this type does not support `Pod` (v1) or `CheckedBitPattern` (v1
/// or v2) due to trait coherence rules.
#[repr(transparent)]
#[derive(Debug, Clone, Copy)]
pub struct CompatWrapper<T: ?Sized>(pub T);

unsafe impl<T: ?Sized> crate::TransparentWrapper<T> for CompatWrapper<T> {}
unsafe impl<T: ?Sized> bytemuck1::TransparentWrapper<T> for CompatWrapper<T> {}

// SAFETY: every bytemuck1::Zeroable type is bytemuck2::Zeroable, since the
// bounds were relaxed only.
unsafe impl<T: bytemuck1::Zeroable> crate::Zeroable for CompatWrapper<T> {}
// SAFETY: slices of every bytemuck1::Zeroable type is bytemuck2::Zeroable,
// since the bounds were relaxed to allow ?Sized types.
unsafe impl<T: bytemuck1::Zeroable> crate::Zeroable for CompatWrapper<[T]> {}
// SAFETY: every crate::Zeroable + Sized type is bytemuck1::Zeroable, since the
// only relaxation was ?Sized.
unsafe impl<T: crate::Zeroable> bytemuck1::Zeroable for CompatWrapper<T> {}

// SAFETY: every bytemuck1::AnyBitPattern type is bytemuck2::AnyBitPattern,
// since the bounds were relaxed only.
unsafe impl<T: bytemuck1::AnyBitPattern> crate::AnyBitPattern
  for CompatWrapper<T>
{
}
// SAFETY: slices of every bytemuck1::AnyBitPattern type is
// bytemuck2::AnyBitPattern, since the bounds were relaxed to allow ?Sized
// types.
unsafe impl<T: bytemuck1::AnyBitPattern> crate::AnyBitPattern
  for CompatWrapper<[T]>
{
}
// SAFETY: every crate::AnyBitPattern + Sized + Copy + Freeze + 'static type is
// bytemuck1::AnyBitPattern, since this re-adds all the relaxations added in
// bytemuck2.
unsafe impl<T: crate::AnyBitPattern + Copy + Freeze + 'static>
  bytemuck1::AnyBitPattern for CompatWrapper<T>
{
}

// SAFETY: every bytemuck1::NoUninit type is bytemuck2::NoUninit,
// since the bounds were relaxed only.
unsafe impl<T: bytemuck1::NoUninit> crate::NoUninit for CompatWrapper<T> {}
// SAFETY: slices of every bytemuck1::NoUninit type is
// bytemuck2::NoUninit, since the bounds were relaxed to allow ?Sized
// types.
unsafe impl<T: bytemuck1::NoUninit> crate::NoUninit for CompatWrapper<[T]> {}

// SAFETY: every crate::NoUninit + Sized + Copy + Freeze + 'static type is
// bytemuck1::NoUninit, since this re-adds all the relaxations added in
// bytemuck2.
unsafe impl<T: crate::NoUninit + Copy + Freeze + 'static> bytemuck1::NoUninit
  for CompatWrapper<T>
{
}

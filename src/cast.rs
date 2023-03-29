//! Safe conversion of a container's item type.
//!
//! The implementation uses several traits to deconstruct, cast, and reconstruct
//! the container.
//! * `Ctor` is the type constructor for a container. This handles changing the
//!   item type, and defining the data pointer and metadata types. Examples
//!   include: `&'a _`, `&'a [_]`, `Box<_>` and `Vec<_>`
//! * `Container` is the concrete type created by giving an item type to `Ctor`.
//!   This handles splitting the data pointer and metadata, and combining the
//!   two back together. Examples include: `&'a u8`, `&'a [i32]`, `Box<String>`
//!   and `Vec<f32>`
//! * `CastPtr` implements casting the data pointer from one type to another.
//!   Currently there are three implementations:
//!   * `SharedBorrowingPtr` indicates that either the source value will not be
//!     read after the conversion, or the target type cannot be written two.
//!   * `UniqueBorrowingPtr` indicates that the source value may be read after
//!     the conversion, and the target type can be written to.
//!   * `OwningPtr` indicates that either the source value will not be read
//!     after the conversion (e.g. `Box`), or the target type cannot be written
//!     to until such time as the source value will not be read anymore (e.g.
//!     `Rc`).
//! * `CastMetadata` implements casting anything other than the data pointer.
//!   e.g. the length conversion of a slice.
//! * `CastContainer` implements any additional constraints applied by a
//!   container class. e.g. `Box<_>` requires both the size and alignment of the
//!   allocation to match.
//! * `CastInPlace` is the exported trait providing the safe cast function.
//!
//! This uses post-monomorphization errors to check for various size and
//! alignment constraints. This is done by panicking during the evaluation of
//! associated constants.

use core::{
  marker::{PhantomData, Unpin},
  mem::{align_of, size_of},
  ops::Deref,
  pin::Pin,
  ptr::{self, NonNull},
  slice,
  sync::atomic::AtomicPtr,
};

use alloc::sync::Arc;
#[cfg(feature = "extern_crate_alloc")]
use alloc::{
  boxed::Box,
  rc::Rc,
  //  borrow::{Cow, ToOwned},
  vec::Vec,
};
#[cfg(feature = "extern_crate_alloc")]
use core::mem::ManuallyDrop;

use crate::{AnyBitPattern, NoUninit, PodCastError};

/// A type constructor for a container type.
///
/// # Safety
/// `Self::Pointer<T>` must be `*mut T` if the original value can be read
/// afterwards and writing to the target type is possible.
pub unsafe trait Ctor<'a> {
  /// Creates the container type for the given item type.
  type Create<T: 'a>;
  /// The pointer to the item(s) contained within the container.
  type Pointer<T: 'a>: Copy;
  /// The metadata required to recreate the contained with the data pointer.
  type Metadata: Copy;
}

pub struct RefT<'a>(PhantomData<&'a ()>);
// SAFETY: Writing through an immutable reference is not safe, so
// `SharedBorrowingPtr<T>` is ok.
unsafe impl<'a> Ctor<'a> for RefT<'a> {
  type Create<T: 'a> = &'a T;
  type Pointer<T: 'a> = SharedBorrowingPtr<T>;
  type Metadata = ();
}

pub struct MutT<'a>(PhantomData<&'a mut ()>);
// SAFETY: Using `*mut T` is always safe.
unsafe impl<'a> Ctor<'a> for MutT<'a> {
  type Create<T: 'a> = &'a mut T;
  type Pointer<T: 'a> = UniqueBorrowingPtr<T>;
  type Metadata = ();
}

pub struct RefSliceT<'a>(PhantomData<&'a ()>);
// SAFETY: Writing through an immutable reference is not safe, so
// `SharedBorrowingPtr<T>` is ok.
unsafe impl<'a> Ctor<'a> for RefSliceT<'a> {
  type Create<T: 'a> = &'a [T];
  type Pointer<T: 'a> = SharedBorrowingPtr<T>;
  type Metadata = usize;
}

pub struct MutSliceT<'a>(PhantomData<&'a mut ()>);
// SAFETY: Using `*mut T` is always safe.
unsafe impl<'a> Ctor<'a> for MutSliceT<'a> {
  type Create<T: 'a> = &'a mut [T];
  type Pointer<T: 'a> = UniqueBorrowingPtr<T>;
  type Metadata = usize;
}

pub struct ConstPtrT;
// SAFETY: Writing through a const pointer is not safe, so
// `SharedBorrowingPtr<T>` is ok.
unsafe impl<'a> Ctor<'a> for ConstPtrT {
  type Create<T: 'a> = *const T;
  type Pointer<T: 'a> = SharedBorrowingPtr<T>;
  type Metadata = ();
}

pub struct MutPtrT;
// SAFETY: Using `*mut T` is always safe.
unsafe impl<'a> Ctor<'a> for MutPtrT {
  type Create<T: 'a> = *mut T;
  type Pointer<T: 'a> = UniqueBorrowingPtr<T>;
  type Metadata = ();
}

pub struct ConstSlicePtrT;
// SAFETY: Writing through a const pointer is not safe, so
// `SharedBorrowingPtr<T>` is ok.
unsafe impl<'a> Ctor<'a> for ConstSlicePtrT {
  type Create<T: 'a> = *const [T];
  type Pointer<T: 'a> = SharedBorrowingPtr<T>;
  type Metadata = usize;
}

pub struct MutSlicePtrT;
// SAFETY: Using `*mut T` is always safe.
unsafe impl<'a> Ctor<'a> for MutSlicePtrT {
  type Create<T: 'a> = *mut [T];
  type Pointer<T: 'a> = UniqueBorrowingPtr<T>;
  type Metadata = usize;
}

pub struct NonNullT;
// SAFETY: Using `*mut T` is always safe.
unsafe impl<'a> Ctor<'a> for NonNullT {
  type Create<T: 'a> = NonNull<T>;
  type Pointer<T: 'a> = UniqueBorrowingPtr<T>;
  type Metadata = ();
}

pub struct NonNullSliceT;
// SAFETY: Using `*mut T` is always safe.
unsafe impl<'a> Ctor<'a> for NonNullSliceT {
  type Create<T: 'a> = NonNull<[T]>;
  type Pointer<T: 'a> = UniqueBorrowingPtr<T>;
  type Metadata = usize;
}

pub struct AtomicPtrT;
// SAFETY: Using `*mut T` is always safe.
unsafe impl<'a> Ctor<'a> for AtomicPtrT {
  type Create<T: 'a> = AtomicPtr<T>;
  type Pointer<T: 'a> = UniqueBorrowingPtr<T>;
  type Metadata = ();
}

pub struct PinT<'a, C: Ctor<'a>>(PhantomData<(C, &'a ())>);
// SAFETY: `Pin` only allows whatever access the wrapped pointer has.
unsafe impl<'a, C: Ctor<'a>> Ctor<'a> for PinT<'a, C> {
  type Create<T: 'a> = Pin<<C as Ctor<'a>>::Create<T>>;
  type Pointer<T: 'a> = <C as Ctor<'a>>::Pointer<T>;
  type Metadata = <C as Ctor<'a>>::Metadata;
}

pub struct OptionT<'a, C: Ctor<'a>>(PhantomData<(C, &'a ())>);
unsafe impl<'a, C: Ctor<'a>> Ctor<'a> for OptionT<'a, C> {
  type Create<T: 'a> = Option<<C as Ctor<'a>>::Create<T>>;
  type Pointer<T: 'a> = Option<<C as Ctor<'a>>::Pointer<T>>;
  type Metadata = Option<<C as Ctor<'a>>::Metadata>;
}

#[cfg(feature = "extern_crate_alloc")]
pub struct VecT(PhantomData<Vec<()>>);
#[cfg(feature = "extern_crate_alloc")]
unsafe impl<'a> Ctor<'a> for VecT {
  type Create<T: 'a> = Vec<T>;
  // We do not need to be able to read as the original type.
  type Pointer<T: 'a> = OwningPtr<T>;
  type Metadata = VecMetadata;
}

#[cfg(feature = "extern_crate_alloc")]
#[derive(Clone, Copy)]
pub struct VecMetadata {
  length: usize,
  capacity: usize,
}

#[cfg(feature = "extern_crate_alloc")]
pub struct BoxT(PhantomData<Box<()>>);
#[cfg(feature = "extern_crate_alloc")]
unsafe impl<'a> Ctor<'a> for BoxT {
  type Create<T: 'a> = Box<T>;
  // We do not need to be able to read as the original type.
  type Pointer<T: 'a> = OwningPtr<T>;
  type Metadata = ();
}

#[cfg(feature = "extern_crate_alloc")]
pub struct BoxSliceT(PhantomData<Box<[()]>>);
#[cfg(feature = "extern_crate_alloc")]
unsafe impl<'a> Ctor<'a> for BoxSliceT {
  type Create<T: 'a> = Box<[T]>;
  // We do not need to be able to read as the original type.
  type Pointer<T: 'a> = OwningPtr<T>;
  type Metadata = usize;
}

#[cfg(feature = "extern_crate_alloc")]
pub struct RcT(PhantomData<Rc<()>>);
#[cfg(feature = "extern_crate_alloc")]
unsafe impl<'a> Ctor<'a> for RcT {
  type Create<T: 'a> = Rc<T>;
  // Either we do need to be able to read as the original type but no writes are
  // possible, or writes are possible but we don't need to be able to read as
  // the original type.
  type Pointer<T: 'a> = OwningPtr<T>;
  type Metadata = ();
}

#[cfg(feature = "extern_crate_alloc")]
pub struct RcSliceT(PhantomData<Rc<[()]>>);
#[cfg(feature = "extern_crate_alloc")]
unsafe impl<'a> Ctor<'a> for RcSliceT {
  type Create<T: 'a> = Rc<[T]>;
  // Either we do need to be able to read as the original type but no writes are
  // possible, or writes are possible but we don't need to be able to read as
  // the original type.
  type Pointer<T: 'a> = OwningPtr<T>;
  type Metadata = usize;
}

#[cfg(feature = "extern_crate_alloc")]
#[cfg(target_has_atomic = "ptr")]
pub struct ArcT(PhantomData<Arc<()>>);
#[cfg(target_has_atomic = "ptr")]
#[cfg(feature = "extern_crate_alloc")]
unsafe impl<'a> Ctor<'a> for ArcT {
  type Create<T: 'a> = Arc<T>;
  // Either we do need to be able to read as the original type but no writes are
  // possible, or writes are possible but we don't need to be able to read as
  // the original type.
  type Pointer<T: 'a> = OwningPtr<T>;
  type Metadata = ();
}

#[cfg(target_has_atomic = "ptr")]
#[cfg(feature = "extern_crate_alloc")]
pub struct ArcSliceT(PhantomData<Arc<[()]>>);
#[cfg(target_has_atomic = "ptr")]
#[cfg(feature = "extern_crate_alloc")]
unsafe impl<'a> Ctor<'a> for ArcSliceT {
  type Create<T: 'a> = Arc<[T]>;
  // Either we do need to be able to read as the original type but no writes are
  // possible, or writes are possible but we don't need to be able to read as
  // the original type.
  type Pointer<T: 'a> = OwningPtr<T>;
  type Metadata = usize;
}

//#[cfg(feature = "extern_crate_alloc")]
//pub struct CowSliceT<'a>(PhantomData<Cow<'a, [()]>>);
//#[cfg(feature = "extern_crate_alloc")]
//unsafe impl<'a> Ctor<'a> for CowSliceT<'a> {
//  type Create<T: 'a> = Cow<'a, [T]>;
//  type Pointer<T: 'a> = *const T;
//  type Metadata = CowSliceMetadata;
//}
//
//#[cfg(feature = "extern_crate_alloc")]
//#[derive(Clone, Copy)]
//pub enum CowSliceMetadata {
//  Borrowed(usize),
//  Owned(VecMetadata),
//}

/// A concrete container type. e.g `&'a T` or `Box<T>`
///
/// # Safety
/// `Self::Item` must match the contained item type.
/// `into_parts` must be the inverse of `from_parts`, even if the item type
/// changes.
pub unsafe trait Container<'a> {
  /// The type constructor for this container.
  type Ctor: Ctor<'a, Create<Self::Item> = Self>;
  /// The item type held within this container.
  type Item: 'a;

  /// Converts the container into it's data pointer and associated metadata.
  fn into_parts(
    self,
  ) -> (
    <Self::Ctor as Ctor<'a>>::Pointer<Self::Item>,
    <Self::Ctor as Ctor<'a>>::Metadata,
  );

  /// Assembles the container from it's data pointer and associated metadata.
  ///
  /// # Safety
  /// The values must have to come from `into_parts` of the same container
  /// class. Casting to a different item type must meet the following
  /// constraints:
  /// * Casting between zero-sized types and non-zero-sized types is forbidden.
  /// * The data pointer's alignment must meet the alignment constraints of it's
  ///   item type.
  /// * Size and alignment requirements of the container class must be met.
  /// * The metadata must be adjusted for the new type.
  unsafe fn from_parts(
    item: <Self::Ctor as Ctor<'a>>::Pointer<Self::Item>,
    metadata: <Self::Ctor as Ctor<'a>>::Metadata,
  ) -> Self;

  /// The error type of a cast, possibly returning the original container.
  type Err: 'a;
  /// Combines the error value with original container value if it cannot be
  /// copied.
  fn with_error(self, err: PodCastError) -> Self::Err;
}

unsafe impl<'a, T: 'a> Container<'a> for &'a T {
  type Ctor = RefT<'a>;
  type Item = T;
  fn into_parts(self) -> (SharedBorrowingPtr<T>, ()) {
    (SharedBorrowingPtr(self), ())
  }
  unsafe fn from_parts(ptr: SharedBorrowingPtr<T>, _: ()) -> Self {
    &*ptr.0
  }

  type Err = PodCastError;
  fn with_error(self, err: PodCastError) -> Self::Err {
    err
  }
}

unsafe impl<'a, T: 'a> Container<'a> for &'a mut T {
  type Ctor = MutT<'a>;
  type Item = T;
  fn into_parts(self) -> (UniqueBorrowingPtr<T>, ()) {
    (UniqueBorrowingPtr(self), ())
  }
  unsafe fn from_parts(ptr: UniqueBorrowingPtr<T>, _: ()) -> Self {
    &mut *ptr.0
  }

  type Err = PodCastError;
  fn with_error(self, err: PodCastError) -> Self::Err {
    err
  }
}

unsafe impl<'a, T: 'a> Container<'a> for &'a [T] {
  type Ctor = RefSliceT<'a>;
  type Item = T;
  fn into_parts(self) -> (SharedBorrowingPtr<T>, usize) {
    (SharedBorrowingPtr(self.as_ptr()), self.len())
  }
  unsafe fn from_parts(data: SharedBorrowingPtr<T>, len: usize) -> Self {
    slice::from_raw_parts(data.0, len)
  }

  type Err = PodCastError;
  fn with_error(self, err: PodCastError) -> Self::Err {
    err
  }
}

unsafe impl<'a, T: 'a> Container<'a> for &'a mut [T] {
  type Ctor = MutSliceT<'a>;
  type Item = T;
  fn into_parts(self) -> (UniqueBorrowingPtr<T>, usize) {
    (UniqueBorrowingPtr(self.as_mut_ptr()), self.len())
  }
  unsafe fn from_parts(data: UniqueBorrowingPtr<T>, len: usize) -> Self {
    slice::from_raw_parts_mut(data.0, len)
  }

  type Err = PodCastError;
  fn with_error(self, err: PodCastError) -> Self::Err {
    err
  }
}

unsafe impl<'a, T: 'a> Container<'a> for *const T {
  type Ctor = ConstPtrT;
  type Item = T;
  fn into_parts(self) -> (SharedBorrowingPtr<T>, ()) {
    (SharedBorrowingPtr(self), ())
  }
  unsafe fn from_parts(ptr: SharedBorrowingPtr<T>, _: ()) -> Self {
    ptr.0
  }

  type Err = PodCastError;
  fn with_error(self, err: PodCastError) -> Self::Err {
    err
  }
}

unsafe impl<'a, T: 'a> Container<'a> for *mut T {
  type Ctor = MutPtrT;
  type Item = T;
  fn into_parts(self) -> (UniqueBorrowingPtr<T>, ()) {
    (UniqueBorrowingPtr(self), ())
  }
  unsafe fn from_parts(ptr: UniqueBorrowingPtr<T>, _: ()) -> Self {
    ptr.0
  }

  type Err = PodCastError;
  fn with_error(self, err: PodCastError) -> Self::Err {
    err
  }
}

fn get_slice_ptr_length<T>(ptr: *const [T]) -> usize {
  #[cfg(feature = "nightly_slice_ptr_len")]
  return ptr.len();
  #[cfg(not(feature = "nightly_slice_ptr_len"))]
  return NonNull::new(ptr as *mut [T])
    .expect("cannot cast null slice pointers until pointer::len is stable")
    .len();
}

unsafe impl<'a, T: 'a> Container<'a> for *const [T] {
  type Ctor = ConstSlicePtrT;
  type Item = T;
  fn into_parts(self) -> (SharedBorrowingPtr<T>, usize) {
    (SharedBorrowingPtr(self as *const T), get_slice_ptr_length(self))
  }
  unsafe fn from_parts(ptr: SharedBorrowingPtr<T>, metadata: usize) -> Self {
    core::ptr::slice_from_raw_parts(ptr.0, metadata)
  }

  type Err = PodCastError;
  fn with_error(self, err: PodCastError) -> Self::Err {
    err
  }
}

unsafe impl<'a, T: 'a> Container<'a> for *mut [T] {
  type Ctor = MutSlicePtrT;
  type Item = T;
  fn into_parts(self) -> (UniqueBorrowingPtr<T>, usize) {
    (UniqueBorrowingPtr(self as *mut T), get_slice_ptr_length(self))
  }
  unsafe fn from_parts(ptr: UniqueBorrowingPtr<T>, metadata: usize) -> Self {
    core::ptr::slice_from_raw_parts_mut(ptr.0, metadata)
  }

  type Err = PodCastError;
  fn with_error(self, err: PodCastError) -> Self::Err {
    err
  }
}

unsafe impl<'a, T: 'a> Container<'a> for NonNull<T> {
  type Ctor = NonNullT;
  type Item = T;
  fn into_parts(self) -> (UniqueBorrowingPtr<T>, ()) {
    (UniqueBorrowingPtr(self.as_ptr()), ())
  }
  unsafe fn from_parts(ptr: UniqueBorrowingPtr<T>, _: ()) -> Self {
    NonNull::new_unchecked(ptr.0)
  }

  type Err = PodCastError;
  fn with_error(self, err: PodCastError) -> Self::Err {
    err
  }
}

unsafe impl<'a, T: 'a> Container<'a> for NonNull<[T]> {
  type Ctor = NonNullSliceT;
  type Item = T;
  fn into_parts(self) -> (UniqueBorrowingPtr<T>, usize) {
    (UniqueBorrowingPtr(self.as_ptr() as *mut T), self.len())
  }
  unsafe fn from_parts(data: UniqueBorrowingPtr<T>, len: usize) -> Self {
    NonNull::new_unchecked(ptr::slice_from_raw_parts_mut(data.0, len))
  }

  type Err = PodCastError;
  fn with_error(self, err: PodCastError) -> Self::Err {
    err
  }
}

unsafe impl<'a, T: 'a> Container<'a> for AtomicPtr<T> {
  type Ctor = AtomicPtrT;
  type Item = T;
  fn into_parts(self) -> (UniqueBorrowingPtr<T>, ()) {
    (UniqueBorrowingPtr(self.into_inner()), ())
  }
  unsafe fn from_parts(ptr: UniqueBorrowingPtr<T>, _: ()) -> Self {
    Self::new(ptr.0)
  }

  type Err = PodCastError;
  fn with_error(self, err: PodCastError) -> Self::Err {
    err
  }
}

// SAFETY: `Pin` has no safety requirements for types which deref to an `Unpin`
// type.
unsafe impl<'a, C> Container<'a> for Pin<C>
where
  C: Container<'a> + Deref + 'a,
  <C as Deref>::Target: Unpin,
  C::Item: Unpin,
{
  type Ctor = PinT<'a, C::Ctor>;
  type Item = C::Item;
  fn into_parts(
    self,
  ) -> (
    <Self::Ctor as Ctor<'a>>::Pointer<Self::Item>,
    <Self::Ctor as Ctor<'a>>::Metadata,
  ) {
    Self::into_inner(self).into_parts()
  }
  unsafe fn from_parts(
    ptr: <Self::Ctor as Ctor<'a>>::Pointer<Self::Item>,
    metadata: <Self::Ctor as Ctor<'a>>::Metadata,
  ) -> Self {
    Self::new(C::from_parts(ptr, metadata))
  }

  type Err = (Self, PodCastError);
  fn with_error(self, err: PodCastError) -> Self::Err {
    (self, err)
  }
}

unsafe impl<'a, C> Container<'a> for Option<C>
where
  C: Container<'a> + 'a,
{
  type Ctor = OptionT<'a, C::Ctor>;
  type Item = C::Item;
  fn into_parts(
    self,
  ) -> (
    <Self::Ctor as Ctor<'a>>::Pointer<Self::Item>,
    <Self::Ctor as Ctor<'a>>::Metadata,
  ) {
    match self {
      Some(inner) => {
        let (ptr, metadata) = inner.into_parts();
        (Some(ptr), Some(metadata))
      }
      None => (None, None),
    }
  }
  unsafe fn from_parts(
    ptr: <Self::Ctor as Ctor<'a>>::Pointer<Self::Item>,
    metadata: <Self::Ctor as Ctor<'a>>::Metadata,
  ) -> Self {
    match (ptr, metadata) {
      (Some(ptr), Some(metadata)) => Some(C::from_parts(ptr, metadata)),
      #[cfg(debug_assertions)]
      (None, Some(_)) | (Some(_), None) => {
        unreachable!("ptr and metadata should both be Some or both be None")
      }
      _ => None,
    }
  }

  type Err = (Self, PodCastError);
  fn with_error(self, err: PodCastError) -> Self::Err {
    (self, err)
  }
}

#[cfg(feature = "extern_crate_alloc")]
unsafe impl<'a, T: 'a> Container<'a> for Vec<T> {
  type Ctor = VecT;
  type Item = T;
  fn into_parts(
    self,
  ) -> (
    <Self::Ctor as Ctor<'a>>::Pointer<Self::Item>,
    <Self::Ctor as Ctor<'a>>::Metadata,
  ) {
    let mut this = ManuallyDrop::new(self);
    let ptr = this.as_mut_ptr();
    let length = this.len();
    let capacity = this.capacity();

    (OwningPtr(ptr), VecMetadata { length, capacity })
  }
  unsafe fn from_parts(
    ptr: <Self::Ctor as Ctor<'a>>::Pointer<Self::Item>,
    metadata: <Self::Ctor as Ctor<'a>>::Metadata,
  ) -> Self {
    Vec::from_raw_parts(ptr.0, metadata.length, metadata.capacity)
  }

  type Err = (Self, PodCastError);
  fn with_error(self, err: PodCastError) -> Self::Err {
    (self, err)
  }
}

#[cfg(feature = "extern_crate_alloc")]
unsafe impl<'a, T: 'a> Container<'a> for Box<T> {
  type Ctor = BoxT;
  type Item = T;
  fn into_parts(
    self,
  ) -> (
    <Self::Ctor as Ctor<'a>>::Pointer<Self::Item>,
    <Self::Ctor as Ctor<'a>>::Metadata,
  ) {
    (OwningPtr(Box::into_raw(self)), ())
  }
  unsafe fn from_parts(
    ptr: <Self::Ctor as Ctor<'a>>::Pointer<Self::Item>,
    _metadata: <Self::Ctor as Ctor<'a>>::Metadata,
  ) -> Self {
    Box::from_raw(ptr.0)
  }

  type Err = (Self, PodCastError);
  fn with_error(self, err: PodCastError) -> Self::Err {
    (self, err)
  }
}

#[cfg(feature = "extern_crate_alloc")]
unsafe impl<'a, T: 'a> Container<'a> for Box<[T]> {
  type Ctor = BoxSliceT;
  type Item = T;
  fn into_parts(
    self,
  ) -> (
    <Self::Ctor as Ctor<'a>>::Pointer<Self::Item>,
    <Self::Ctor as Ctor<'a>>::Metadata,
  ) {
    let this = Box::into_raw(self);
    (OwningPtr(this as *mut T), get_slice_ptr_length(this))
  }
  unsafe fn from_parts(
    ptr: <Self::Ctor as Ctor<'a>>::Pointer<Self::Item>,
    metadata: <Self::Ctor as Ctor<'a>>::Metadata,
  ) -> Self {
    let ptr = core::ptr::slice_from_raw_parts_mut(ptr.0, metadata);
    Box::from_raw(ptr)
  }

  type Err = (Self, PodCastError);
  fn with_error(self, err: PodCastError) -> Self::Err {
    (self, err)
  }
}

#[cfg(feature = "extern_crate_alloc")]
unsafe impl<'a, T: 'a> Container<'a> for Rc<T> {
  type Ctor = RcT;
  type Item = T;
  fn into_parts(
    self,
  ) -> (
    <Self::Ctor as Ctor<'a>>::Pointer<Self::Item>,
    <Self::Ctor as Ctor<'a>>::Metadata,
  ) {
    (OwningPtr(Rc::into_raw(self) as *mut T), ())
  }
  unsafe fn from_parts(
    ptr: <Self::Ctor as Ctor<'a>>::Pointer<Self::Item>,
    _metadata: <Self::Ctor as Ctor<'a>>::Metadata,
  ) -> Self {
    Rc::from_raw(ptr.0)
  }

  type Err = (Self, PodCastError);
  fn with_error(self, err: PodCastError) -> Self::Err {
    (self, err)
  }
}

#[cfg(feature = "extern_crate_alloc")]
unsafe impl<'a, T: 'a> Container<'a> for Rc<[T]> {
  type Ctor = RcSliceT;
  type Item = T;
  fn into_parts(
    self,
  ) -> (
    <Self::Ctor as Ctor<'a>>::Pointer<Self::Item>,
    <Self::Ctor as Ctor<'a>>::Metadata,
  ) {
    let length = self.len();
    let ptr = Rc::into_raw(self) as *const T as *mut T;
    (OwningPtr(ptr), length)
  }
  unsafe fn from_parts(
    ptr: <Self::Ctor as Ctor<'a>>::Pointer<Self::Item>,
    metadata: <Self::Ctor as Ctor<'a>>::Metadata,
  ) -> Self {
    let ptr = core::ptr::slice_from_raw_parts(ptr.0, metadata);
    Rc::from_raw(ptr)
  }

  type Err = (Self, PodCastError);
  fn with_error(self, err: PodCastError) -> Self::Err {
    (self, err)
  }
}

#[cfg(feature = "extern_crate_alloc")]
#[cfg(target_has_atomic = "ptr")]
unsafe impl<'a, T: 'a> Container<'a> for Arc<T> {
  type Ctor = ArcT;
  type Item = T;
  fn into_parts(
    self,
  ) -> (
    <Self::Ctor as Ctor<'a>>::Pointer<Self::Item>,
    <Self::Ctor as Ctor<'a>>::Metadata,
  ) {
    (OwningPtr(Arc::into_raw(self) as *mut T), ())
  }
  unsafe fn from_parts(
    ptr: <Self::Ctor as Ctor<'a>>::Pointer<Self::Item>,
    _metadata: <Self::Ctor as Ctor<'a>>::Metadata,
  ) -> Self {
    Arc::from_raw(ptr.0)
  }

  type Err = (Self, PodCastError);
  fn with_error(self, err: PodCastError) -> Self::Err {
    (self, err)
  }
}

#[cfg(feature = "extern_crate_alloc")]
#[cfg(target_has_atomic = "ptr")]
unsafe impl<'a, T: 'a> Container<'a> for Arc<[T]> {
  type Ctor = ArcSliceT;
  type Item = T;
  fn into_parts(
    self,
  ) -> (
    <Self::Ctor as Ctor<'a>>::Pointer<Self::Item>,
    <Self::Ctor as Ctor<'a>>::Metadata,
  ) {
    let length = self.len();
    let ptr = Arc::into_raw(self) as *const T as *mut T;
    (OwningPtr(ptr), length)
  }
  unsafe fn from_parts(
    ptr: <Self::Ctor as Ctor<'a>>::Pointer<Self::Item>,
    metadata: <Self::Ctor as Ctor<'a>>::Metadata,
  ) -> Self {
    let ptr = core::ptr::slice_from_raw_parts(ptr.0, metadata);
    Arc::from_raw(ptr)
  }

  type Err = (Self, PodCastError);
  fn with_error(self, err: PodCastError) -> Self::Err {
    (self, err)
  }
}

/// Casts the data pointer portion of a container.
///
/// SAFETY:
/// * The returned pointer must have the same address.
/// * The returned pointer must be suitably aligned.
/// * For mutable pointers, it must be safe to read from the original pointer
///   once the new pointer has been written through.
unsafe trait CastPtr<T> {
  /// Perform the cast. Will return `None` if the input is not suitably aligned
  /// for the target type.
  fn cast_ptr(self) -> Option<T>;
}

/// This Ptr indicates that the container borrows the casted data non-uniquely.
///
/// Therefore, casting the Ptr only requires that the source type is `NoUninit`
/// and the destination type is `AnyBitPattern, since no data can be written as
/// the destination type.
///
/// Casting this pointer can change alignment, as long as the actual pointer
/// value is aligned for the destination type.
pub struct SharedBorrowingPtr<T>(*const T);

/// This Ptr indicates that the container borrows the casted data uniquely.
///
/// Therefore, casting the Ptr requires that the source type is `NoUninit +
/// AnyBitPattern` and the destination type is `NoUninit + AnyBitPattern`, since
/// data written as destination type may be later read as the source type.
///
/// Casting this pointer can change alignment, as long as the actual pointer
/// value is aligned for the destination type.
pub struct UniqueBorrowingPtr<T>(*mut T);

/// This Ptr indicates that the container owns the casted data, either
/// uniquely (e.g. `Box<T>`), or shared (e.g. `Rc<T>`).
///
/// Therefore, casting the Ptr requires that the source type is `NoUninit` and
/// the destination type is `AnyBitPattern`, since no data can be written as the
/// destination type. This is true because any changes made
/// as the destination type cannot be observed by as source type, either because
/// unique ownership has been given, or because changes cannot be made due to
/// shared ownership.
///
/// Casting this pointer must ensure that alignments of the source and
/// destination type are exactly the same, since owning containers require
/// deallocating their buffer with the same alignment that it was allocated
/// with.
pub struct OwningPtr<T>(*mut T);

impl<T> Clone for SharedBorrowingPtr<T> {
  fn clone(&self) -> Self {
    *self
  }
}
impl<T> Copy for SharedBorrowingPtr<T> {}
impl<T> Clone for UniqueBorrowingPtr<T> {
  fn clone(&self) -> Self {
    *self
  }
}
impl<T> Copy for UniqueBorrowingPtr<T> {}
impl<T> Clone for OwningPtr<T> {
  fn clone(&self) -> Self {
    *self
  }
}
impl<T> Copy for OwningPtr<T> {}

// SAFETY: `SharedBorrowingPtr` indicates that the original value cannot be used
// to read anything written through the target type, so the source type only
// requires `NoUninit`, and the destination type only requires `AnyBitPattern`.
unsafe impl<T, U> CastPtr<SharedBorrowingPtr<U>> for SharedBorrowingPtr<T>
where
  T: NoUninit,
  U: AnyBitPattern,
{
  fn cast_ptr(self) -> Option<SharedBorrowingPtr<U>> {
    if align_of::<T>() >= align_of::<U>() {
      Some(SharedBorrowingPtr(self.0 as *const U))
    } else if self.0 as usize % align_of::<U>() != 0 {
      None
    } else {
      Some(SharedBorrowingPtr(self.0 as *const U))
    }
  }
}

// SAFETY: `UniqueBorrowingPtr` indicates that the original value can be used to
// read something written through the target type, so `NoUninit + AnyBitPattern`
// is required on both types.
unsafe impl<T, U> CastPtr<UniqueBorrowingPtr<U>> for UniqueBorrowingPtr<T>
where
  T: NoUninit + AnyBitPattern,
  U: NoUninit + AnyBitPattern,
{
  fn cast_ptr(self) -> Option<UniqueBorrowingPtr<U>> {
    if align_of::<T>() >= align_of::<U>() {
      Some(UniqueBorrowingPtr(self.0 as *mut U))
    } else if self.0 as usize % align_of::<U>() != 0 {
      None
    } else {
      Some(UniqueBorrowingPtr(self.0 as *mut U))
    }
  }
}

// SAFETY: `OwningPtr` indicates that the original value cannot be used to read
// something written through the target type, so the source type only requires
// `NoUninit`, and the destination type only requires `AnyBitPattern`.
unsafe impl<T, U> CastPtr<OwningPtr<U>> for OwningPtr<T>
where
  T: NoUninit,
  U: AnyBitPattern,
{
  fn cast_ptr(self) -> Option<OwningPtr<U>> {
    if align_of::<T>() == align_of::<U>() {
      Some(OwningPtr(self.0 as *mut U))
    } else {
      None
    }
  }
}

unsafe impl<T, U> CastPtr<Option<U>> for Option<T>
where
  T: CastPtr<U>,
{
  /// `None` represents failure, `Some(None)` represents a successful cast of a
  /// `None` self
  fn cast_ptr(self) -> Option<Option<U>> {
    match self.map(T::cast_ptr) {
      Some(Some(inner)) => Some(Some(inner)),
      Some(None) => None,
      None => Some(None),
    }
  }
}

/// Checks any constraints the container requires when casting between types.
trait CastContainer<T, U> {
  const _COND: () = ();
}
impl<'a, T, U> CastContainer<T, U> for RefT<'a> {
  const _COND: () = {
    if size_of::<T>() != size_of::<U>() {
      panic!("Attempt to cast between two values with different sizes");
    }
  };
}
impl<'a, T, U> CastContainer<T, U> for MutT<'a> {
  const _COND: () = <RefT as CastContainer<T, U>>::_COND;
}
impl<'a, T, U> CastContainer<T, U> for RefSliceT<'a> {}
impl<'a, T, U> CastContainer<T, U> for MutSliceT<'a> {}
impl<T, U> CastContainer<T, U> for ConstPtrT {
  const _COND: () = <RefT as CastContainer<T, U>>::_COND;
}
impl<T, U> CastContainer<T, U> for MutPtrT {
  const _COND: () = <RefT as CastContainer<T, U>>::_COND;
}
impl<T, U> CastContainer<T, U> for ConstSlicePtrT {}
impl<T, U> CastContainer<T, U> for MutSlicePtrT {}
impl<T, U> CastContainer<T, U> for NonNullT {
  const _COND: () = <RefT as CastContainer<T, U>>::_COND;
}
impl<T, U> CastContainer<T, U> for AtomicPtrT {
  const _COND: () = <RefT as CastContainer<T, U>>::_COND;
}
impl<'a, T, U> CastContainer<T, U> for NonNullSliceT {}
impl<'a, T, U, C> CastContainer<T, U> for PinT<'a, C>
where
  C: Ctor<'a> + CastContainer<T, U>,
{
  const _COND: () = C::_COND;
}
impl<'a, T, U, C> CastContainer<T, U> for OptionT<'a, C>
where
  C: Ctor<'a> + CastContainer<T, U>,
{
  const _COND: () = C::_COND;
}
#[cfg(feature = "extern_crate_alloc")]
impl<T, U> CastContainer<T, U> for VecT {}
#[cfg(feature = "extern_crate_alloc")]
impl<T, U> CastContainer<T, U> for BoxT {
  const _COND: () = <RefT as CastContainer<T, U>>::_COND;
}
#[cfg(feature = "extern_crate_alloc")]
impl<T, U> CastContainer<T, U> for BoxSliceT {}
#[cfg(feature = "extern_crate_alloc")]
impl<T, U> CastContainer<T, U> for RcT {
  const _COND: () = <RefT as CastContainer<T, U>>::_COND;
}
#[cfg(feature = "extern_crate_alloc")]
impl<T, U> CastContainer<T, U> for RcSliceT {}
#[cfg(feature = "extern_crate_alloc")]
#[cfg(target_has_atomic = "ptr")]
impl<T, U> CastContainer<T, U> for ArcT {
  const _COND: () = <RefT as CastContainer<T, U>>::_COND;
}
#[cfg(feature = "extern_crate_alloc")]
#[cfg(target_has_atomic = "ptr")]
impl<T, U> CastContainer<T, U> for ArcSliceT {}

/// Casts the metadata portion of a container.
trait CastMetadata<T, U>: Sized {
  fn cast_metadata(self) -> Result<Self, PodCastError>;
}

impl<T, U> CastMetadata<T, U> for () {
  fn cast_metadata(self) -> Result<Self, PodCastError> {
    Ok(())
  }
}

impl<T, U> CastMetadata<T, U> for usize {
  fn cast_metadata(self) -> Result<Self, PodCastError> {
    if size_of::<T>() == size_of::<U>() {
      Ok(self)
    } else {
      let byte_len = self * size_of::<T>();
      if byte_len % size_of::<U>() == 0 {
        Ok(byte_len / size_of::<U>())
      } else {
        Err(PodCastError::SizeMismatch)
      }
    }
  }
}

impl<M, T, U> CastMetadata<T, U> for Option<M>
where
  M: CastMetadata<T, U>,
{
  fn cast_metadata(self) -> Result<Self, PodCastError> {
    self.map(M::cast_metadata).transpose()
  }
}

#[cfg(feature = "extern_crate_alloc")]
impl<T, U> CastMetadata<T, U> for VecMetadata {
  fn cast_metadata(self) -> Result<Self, PodCastError> {
    if size_of::<T>() == size_of::<U>() {
      Ok(self)
    } else {
      let byte_len = self.length * size_of::<T>();
      let byte_cap = self.capacity * size_of::<T>();
      if byte_len % size_of::<U>() == 0 && byte_cap % size_of::<U>() == 0 {
        Ok(VecMetadata {
          length: byte_len / size_of::<U>(),
          capacity: byte_cap / size_of::<U>(),
        })
      } else {
        Err(PodCastError::SizeMismatch)
      }
    }
  }
}

/// Safely reinterprets a value or group af values in place.
///
/// This currently supports the following pointer/reference/container types:
/// * `&'a T`
/// * `*const T`
/// * `NonNull<T>`
/// * `AtomicPtr<T>`
/// * `Pin<T>` for any supported pointer type.
///
/// All applicable mutable and slice variants are also supported.
pub trait CastInPlace<'a, T>: Sized + Container<'a> {
  const _COND: ();
  /// Perform the cast.
  fn cast_in_place(self) -> Result<T, Self::Err>;
}

impl<'a, T, U> CastInPlace<'a, U> for T
where
  T: Container<'a, Ctor = U::Ctor>,
  U: Container<'a>,
  T::Ctor: CastContainer<T::Item, U::Item>,
  <T::Ctor as Ctor<'a>>::Pointer<T::Item>:
    CastPtr<<U::Ctor as Ctor<'a>>::Pointer<U::Item>>,
  <T::Ctor as Ctor<'a>>::Metadata: CastMetadata<T::Item, U::Item>,
{
  const _COND: () = {
    if (size_of::<T::Item>() == 0) != (size_of::<U::Item>() == 0) {
      panic!(
        "Attempt to cast between a zero-sized type and a non-zero-sized type"
      );
    }
  };

  #[allow(path_statements)]
  fn cast_in_place(self) -> Result<U, Self::Err> {
    <T::Ctor as CastContainer<T::Item, U::Item>>::_COND;

    let (ptr, metadata) = self.into_parts();
    let Some(new_ptr) = ptr.cast_ptr() else {
        return Err(unsafe {
            T::from_parts(ptr, metadata)
                .with_error(PodCastError::TargetAlignmentGreaterAndInputNotAligned)
        });
    };
    match metadata.cast_metadata() {
      Ok(metadata) => Ok(unsafe { U::from_parts(new_ptr, metadata) }),
      Err(e) => {
        return Err(unsafe { T::from_parts(ptr, metadata).with_error(e) })
      }
    }
  }
}

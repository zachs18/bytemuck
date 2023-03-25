use core::{
  marker::{PhantomData, Unpin},
  mem::{align_of, size_of},
  ops::Deref,
  pin::Pin,
  ptr::{self, NonNull},
  slice,
  sync::atomic::AtomicPtr,
};

use crate::{AnyBitPattern, NoUninit, PodCastError};

/// A type constructor for a container type. e.g. `&'a _`, `Box<[_]>`, `Vec<_>`
///
/// # Safety
/// `Self::Pointer<T>` must be `*mut T` if writing to the new type is both possible
/// and that value can be read as the old type.
pub unsafe trait Ctor<'a> {
  /// Creates the container type for the given item type.
  type Create<T: 'a>;
  /// The pointer to the item(s) contained within the container.
  type Pointer<T: 'a>: Copy;
  /// The metadata required to recreate the contained with the data pointer.
  type Metadata: Copy;
}

pub struct RefT<'a>(PhantomData<&'a ()>);
// SAFETY: Writing through an immutable reference is not safe, so `*const T` is ok.
unsafe impl<'a> Ctor<'a> for RefT<'a> {
  type Create<T: 'a> = &'a T;
  type Pointer<T: 'a> = *const T;
  type Metadata = ();
}

pub struct MutT<'a>(PhantomData<&'a mut ()>);
// SAFETY: Using `*mut T` is always safe.
unsafe impl<'a> Ctor<'a> for MutT<'a> {
  type Create<T: 'a> = &'a mut T;
  type Pointer<T: 'a> = *mut T;
  type Metadata = ();
}

pub struct RefSliceT<'a>(PhantomData<&'a ()>);
// SAFETY: Writing through an immutable reference is not safe, so `*const T` is ok.
unsafe impl<'a> Ctor<'a> for RefSliceT<'a> {
  type Create<T: 'a> = &'a [T];
  type Pointer<T: 'a> = *const T;
  type Metadata = usize;
}

pub struct MutSliceT<'a>(PhantomData<&'a mut ()>);
// SAFETY: Using `*mut T` is always safe.
unsafe impl<'a> Ctor<'a> for MutSliceT<'a> {
  type Create<T: 'a> = &'a mut [T];
  type Pointer<T: 'a> = *mut T;
  type Metadata = usize;
}

pub struct ConstPtrT;
// SAFETY: Writing through a const pointer is not safe, so `*const T` is ok.
unsafe impl<'a> Ctor<'a> for ConstPtrT {
  type Create<T: 'a> = *const T;
  type Pointer<T: 'a> = *const T;
  type Metadata = ();
}

pub struct MutPtrT;
// SAFETY: Using `*mut T` is always safe.
unsafe impl<'a> Ctor<'a> for MutPtrT {
  type Create<T: 'a> = *mut T;
  type Pointer<T: 'a> = *mut T;
  type Metadata = ();
}

pub struct ConstSlicePtrT;
// SAFETY: Writing through a const pointer is not safe, so `*const T` is ok.
unsafe impl<'a> Ctor<'a> for ConstSlicePtrT {
  type Create<T: 'a> = *const [T];
  type Pointer<T: 'a> = *const T;
  type Metadata = usize;
}

pub struct MutSlicePtrT;
// SAFETY: Using `*mut T` is always safe.
unsafe impl<'a> Ctor<'a> for MutSlicePtrT {
  type Create<T: 'a> = *mut [T];
  type Pointer<T: 'a> = *mut T;
  type Metadata = usize;
}

pub struct NonNullT;
// SAFETY: Using `*mut T` is always safe.
unsafe impl<'a> Ctor<'a> for NonNullT {
  type Create<T: 'a> = NonNull<T>;
  type Pointer<T: 'a> = *mut T;
  type Metadata = ();
}

pub struct NonNullSliceT;
// SAFETY: Using `*mut T` is always safe.
unsafe impl<'a> Ctor<'a> for NonNullSliceT {
  type Create<T: 'a> = NonNull<[T]>;
  type Pointer<T: 'a> = *mut T;
  type Metadata = usize;
}

pub struct AtomicPtrT;
// SAFETY: Using `*mut T` is always safe.
unsafe impl<'a> Ctor<'a> for AtomicPtrT {
  type Create<T: 'a> = AtomicPtr<T>;
  type Pointer<T: 'a> = *mut T;
  type Metadata = ();
}

pub struct PinT<'a, C: Ctor<'a>>(PhantomData<(C, &'a ())>);
// SAFETY: `Pin` is a thin wrapper
unsafe impl<'a, C: Ctor<'a>> Ctor<'a> for PinT<'a, C> {
  type Create<T: 'a> = Pin<<C as Ctor<'a>>::Create<T>>;
  type Pointer<T: 'a> = <C as Ctor<'a>>::Pointer<T>;
  type Metadata = <C as Ctor<'a>>::Metadata;
}

/// A concrete container type. e.g `&'a T` or `Box<T>`
///
/// # Safety
/// `Self::Item` must match the contained item type.
/// `into_parts` and `from_parts` must be a matching pair.
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
  /// The values must have come from `into_parts` of the same container class.
  /// Casting to a different item type must meet the following constraints:
  /// * Casting between zero-sized types and non-zero-sized types is forbidden.
  /// * The data pointers alignment must meet the alignment constraints of it's item type.
  /// * Size and alignment requirements of the container class must be met.
  /// * The metadata must be adjusted for the new type.
  unsafe fn from_parts(
    item: <Self::Ctor as Ctor<'a>>::Pointer<Self::Item>,
    metadata: <Self::Ctor as Ctor<'a>>::Metadata,
  ) -> Self;

  /// The error type of a cast, possibly returning the original container.
  type Err: 'a;
  /// Combines the error value with original container value if it cannot be copied.
  fn with_error(self, err: PodCastError) -> Self::Err;
}

unsafe impl<'a, T: 'a> Container<'a> for &'a T {
  type Ctor = RefT<'a>;
  type Item = T;
  fn into_parts(self) -> (*const T, ()) {
    (self, ())
  }
  unsafe fn from_parts(ptr: *const T, _: ()) -> Self {
    &*ptr
  }

  type Err = PodCastError;
  fn with_error(self, err: PodCastError) -> Self::Err {
    err
  }
}

unsafe impl<'a, T: 'a> Container<'a> for &'a mut T {
  type Ctor = MutT<'a>;
  type Item = T;
  fn into_parts(self) -> (*mut T, ()) {
    (self, ())
  }
  unsafe fn from_parts(ptr: *mut T, _: ()) -> Self {
    &mut *ptr
  }

  type Err = PodCastError;
  fn with_error(self, err: PodCastError) -> Self::Err {
    err
  }
}

unsafe impl<'a, T: 'a> Container<'a> for &'a [T] {
  type Ctor = RefSliceT<'a>;
  type Item = T;
  fn into_parts(self) -> (*const T, usize) {
    (self.as_ptr(), self.len())
  }
  unsafe fn from_parts(data: *const T, len: usize) -> Self {
    slice::from_raw_parts(data, len)
  }

  type Err = PodCastError;
  fn with_error(self, err: PodCastError) -> Self::Err {
    err
  }
}

unsafe impl<'a, T: 'a> Container<'a> for &'a mut [T] {
  type Ctor = MutSliceT<'a>;
  type Item = T;
  fn into_parts(self) -> (*mut T, usize) {
    (self.as_mut_ptr(), self.len())
  }
  unsafe fn from_parts(data: *mut T, len: usize) -> Self {
    slice::from_raw_parts_mut(data, len)
  }

  type Err = PodCastError;
  fn with_error(self, err: PodCastError) -> Self::Err {
    err
  }
}

unsafe impl<'a, T: 'a> Container<'a> for *const T {
  type Ctor = ConstPtrT;
  type Item = T;
  fn into_parts(self) -> (*const T, ()) {
    (self, ())
  }
  unsafe fn from_parts(ptr: *const T, _: ()) -> Self {
    ptr
  }

  type Err = PodCastError;
  fn with_error(self, err: PodCastError) -> Self::Err {
    err
  }
}

unsafe impl<'a, T: 'a> Container<'a> for *mut T {
  type Ctor = MutPtrT;
  type Item = T;
  fn into_parts(self) -> (*mut T, ()) {
    (self, ())
  }
  unsafe fn from_parts(ptr: *mut T, _: ()) -> Self {
    ptr
  }

  type Err = PodCastError;
  fn with_error(self, err: PodCastError) -> Self::Err {
    err
  }
}

unsafe impl<'a, T: 'a> Container<'a> for NonNull<T> {
  type Ctor = NonNullT;
  type Item = T;
  fn into_parts(self) -> (*mut T, ()) {
    (self.as_ptr(), ())
  }
  unsafe fn from_parts(ptr: *mut T, _: ()) -> Self {
    NonNull::new_unchecked(ptr)
  }

  type Err = PodCastError;
  fn with_error(self, err: PodCastError) -> Self::Err {
    err
  }
}

unsafe impl<'a, T: 'a> Container<'a> for NonNull<[T]> {
  type Ctor = NonNullSliceT;
  type Item = T;
  fn into_parts(self) -> (*mut T, usize) {
    (self.as_ptr() as *mut T, self.len())
  }
  unsafe fn from_parts(data: *mut T, len: usize) -> Self {
    NonNull::new_unchecked(ptr::slice_from_raw_parts_mut(data, len))
  }

  type Err = PodCastError;
  fn with_error(self, err: PodCastError) -> Self::Err {
    err
  }
}

unsafe impl<'a, T: 'a> Container<'a> for AtomicPtr<T> {
  type Ctor = AtomicPtrT;
  type Item = T;
  fn into_parts(self) -> (*mut T, ()) {
    (self.into_inner(), ())
  }
  unsafe fn from_parts(ptr: *mut T, _: ()) -> Self {
    Self::new(ptr)
  }

  type Err = PodCastError;
  fn with_error(self, err: PodCastError) -> Self::Err {
    err
  }
}

unsafe impl<'a, C> Container<'a> for Pin<C>
where
  C: Container<'a> + Deref<Target = C::Item>,
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

  type Err = PodCastError;
  fn with_error(self, err: PodCastError) -> Self::Err {
    err
  }
}

/// Casts the data pointer portion of a container.
trait CastPtr<T> {
  /// Perform the cast. Will return `None` if the input is not suitably aligne
  /// for the target type.
  fn cast_ptr(self) -> Option<T>;
}

impl<T, U> CastPtr<*const U> for *const T
where
  T: NoUninit,
  U: AnyBitPattern,
{
  fn cast_ptr(self) -> Option<*const U> {
    if align_of::<T>() >= align_of::<U>() {
      Some(self as *const U)
    } else if self as usize % align_of::<U>() != 0 {
      None
    } else {
      Some(self as *const U)
    }
  }
}

impl<T, U> CastPtr<*mut U> for *mut T
where
  T: NoUninit + AnyBitPattern,
  U: NoUninit + AnyBitPattern,
{
  fn cast_ptr(self) -> Option<*mut U> {
    if align_of::<T>() >= align_of::<U>() {
      Some(self as *mut U)
    } else if self as usize % align_of::<U>() != 0 {
      None
    } else {
      Some(self as *mut U)
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

pub trait CastInPlace<'a, T>: Sized + Container<'a> {
  const _COND: ();
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

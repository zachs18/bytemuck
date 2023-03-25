//! Safe byte-wise conversion between types.
//!
//! The public interface consist of a few traits:
//! * `Reinterpret` and `TryReinterpret` implement by-value conversion.
//! * `ReinterpretInner` and `TryReinterpretInner` implement in-place conversion
//!   for various container types.
//!
//! `ReinterpretInner` is backed by several helper traits:
//! * `Container` is a concrete container with a pointer to zero or more items.
//!   This trait handles several things:
//!   * Holding a tag type representing the containers type class. This prevents
//!     casts between incompatible containers and allows any additional
//!     constraints required by the container not handled by it's raw
//!     representation.
//!   * Conversion to and from a container's raw form. This allows the actual
//!     cast implementation to be shared between multiple containers.
//!   * Whether the original value should be returned in case of an error. This
//!     allows simplifying the return type of `try_reinterpret_inner` for `Copy`
//!     types.
//!   Examples of containers include references, raw pointers, `Box<T>` and
//!   `Vec<T>`.
//! * `AssertClassContraints` handles any additional constraints a container
//!   places on its items.
//! * `CastRaw` implements the conversion between a container's raw form. This
//!   is responsible for verifying that the container's item types are
//!   compatible and any size/alignment constraints are met.
//! * `TryCastRaw` is the falliable form of `CastRaw`

use core::{
  marker::{PhantomData, Unpin},
  mem::{align_of, size_of, ManuallyDrop},
  ops::Deref,
  pin::Pin,
  ptr::NonNull,
  slice,
  sync::atomic::AtomicPtr,
};

#[cfg(feature = "extern_crate_alloc")]
use alloc::{
  borrow::{Cow, ToOwned},
  boxed::Box,
  rc::{Rc, Weak as RcWeak},
  sync::{Arc, Weak as ArcWeak},
  vec::Vec,
};

use crate::{
  static_assert::*, AnyBitPattern, CheckedBitPattern, NoUninit, PodCastError,
};

/// Safe byte-wise conversion of a value.
pub trait Reinterpret<T>: Sized {
  /// Performs the conversion.
  fn reinterpret(self) -> T;
}
impl<T, U> Reinterpret<U> for T
where
  T: NoUninit,
  U: AnyBitPattern,
{
  fn reinterpret(self) -> U {
    static_assert!(AssertSameSize(T, U));
    // SAFETY:
    // There are no uninitialized bytes in the source type.
    // All bit patterns are accepted by the target type.
    // Both types have the same size.
    unsafe { (&ManuallyDrop::new(self) as *const _ as *const U).read() }
  }
}

/// Same as `Reinterpret`, but for casts which may fail due to invalid bit patterns.
pub trait TryReinterpret<T>: Sized {
  /// Perform the cast.
  fn try_reinterpret(self) -> Option<T>;
}
impl<T, U> TryReinterpret<U> for T
where
  T: NoUninit,
  U: CheckedBitPattern,
{
  fn try_reinterpret(self) -> Option<U> {
    static_assert!(AssertSameSize(T, U));
    let bits: U::Bits = self.reinterpret();
    if U::is_valid_bit_pattern(&bits) {
      // SAFETY:
      // There are no uninitialized bytes in the source type.
      // The value has been confirmed to be a valid bit pattern for the target type.
      // Both types have the same size.
      Some(unsafe { (&ManuallyDrop::new(self) as *const _ as *const U).read() })
    } else {
      None
    }
  }
}

// Container classes.
pub struct RefT;
pub struct PtrT;
pub struct NonNullT;
pub struct AtomicPtrT;
pub struct OptionT<C>(PhantomData<C>);
pub struct PinT<C>(PhantomData<C>);
#[cfg(feature = "extern_crate_alloc")]
pub struct BoxT;
#[cfg(feature = "extern_crate_alloc")]
pub struct CowT;
#[cfg(feature = "extern_crate_alloc")]
pub struct RcT;
#[cfg(feature = "extern_crate_alloc")]
pub struct RcWeakT;
#[cfg(feature = "extern_crate_alloc")]
pub struct ArcT;
#[cfg(feature = "extern_crate_alloc")]
pub struct ArcWeakT;
#[cfg(feature = "extern_crate_alloc")]
pub struct VecT;

/// Policy trait for whether the original value should be returned with the
/// error.
pub trait CastErrWithValue<T> {
  /// The error type returned.
  type Err;
  /// Combines the original value with the error.
  fn cast_error_with_value(value: T, err: PodCastError) -> Self::Err;
}
/// Return the error without the original value.
pub struct OnlyErr;
impl<T> CastErrWithValue<T> for OnlyErr {
  type Err = PodCastError;
  fn cast_error_with_value(_: T, err: PodCastError) -> Self::Err {
    err
  }
}
/// Return both the error and the original value.
pub struct ErrWithValue;
impl<T> CastErrWithValue<T> for ErrWithValue {
  type Err = (T, PodCastError);
  fn cast_error_with_value(value: T, err: PodCastError) -> Self::Err {
    (value, err)
  }
}

/// A concrete container type. e.g `&'a T` or `Box<T>`
///
/// # Safety
/// * `Class` must be set such that calling `CastRaw` on this containers raw
///   form is valid.
/// * `Item` must match the contained item type.
/// * `into_raw` -> `CastRaw`/`TryCastRaw` -> `from_raw` must be valid.
pub unsafe trait Container<'a>: Sized {
  /// The type class of this container. Used to limit which raw casts should be
  type Class: AssertClassContraints<Self::Item, Self::Item>;
  /// The item type held within this container.
  type Item: 'a;
  /// The 'raw' form of this container. Used to allow different containers to
  /// share the same `CastRaw` and `TryCastRaw` impls.
  type Raw: 'a + Copy;
  /// Whether the cast should return the original value along with the error.
  type CastErr: CastErrWithValue<Self>;

  /// Converts the container into it's raw form.
  fn into_raw(self) -> Self::Raw;

  /// Reconstructs the container from it's raw form.
  ///
  /// # Safety
  /// The values must have to come from `into_parts` of the same container
  /// class. Casting to a different item type must meet the following
  /// constraints:
  /// * Casting between zero-sized types and non-zero-sized types is forbidden.
  /// * The data pointer's alignment must meet the alignment constraints of it's
  ///   item type.
  /// * Size and alignment requirements of the container class must be met.
  /// * The additional data must be adjusted for the new type.
  unsafe fn from_raw(raw: Self::Raw) -> Self;
}

unsafe impl<'a, T: 'a> Container<'a> for &'a T {
  type Class = RefT;
  type Item = T;
  type Raw = *const T;
  type CastErr = OnlyErr;

  fn into_raw(self) -> Self::Raw {
    self
  }
  unsafe fn from_raw(data: Self::Raw) -> Self {
    &*data
  }
}

unsafe impl<'a, T: 'a> Container<'a> for &'a mut T {
  type Class = RefT;
  type Item = T;
  type Raw = *mut T;
  type CastErr = OnlyErr;

  fn into_raw(self) -> Self::Raw {
    self
  }
  unsafe fn from_raw(data: Self::Raw) -> Self {
    &mut *data
  }
}

unsafe impl<'a, T: 'a> Container<'a> for &'a [T] {
  type Class = RefT;
  type Item = T;
  type Raw = (*const T, usize);
  type CastErr = OnlyErr;

  fn into_raw(self) -> Self::Raw {
    (self.as_ptr(), self.len())
  }
  unsafe fn from_raw((data, len): Self::Raw) -> Self {
    slice::from_raw_parts(data, len)
  }
}

unsafe impl<'a, T: 'a> Container<'a> for &'a mut [T] {
  type Class = RefT;
  type Item = T;
  type Raw = (*mut T, usize);
  type CastErr = OnlyErr;

  fn into_raw(self) -> Self::Raw {
    (self.as_mut_ptr(), self.len())
  }
  unsafe fn from_raw((data, len): Self::Raw) -> Self {
    slice::from_raw_parts_mut(data, len)
  }
}

unsafe impl<'a, T: 'a> Container<'a> for *const T {
  type Class = PtrT;
  type Item = T;
  type Raw = Self;
  type CastErr = OnlyErr;

  fn into_raw(self) -> Self::Raw {
    self
  }
  unsafe fn from_raw(ptr: Self::Raw) -> Self {
    ptr
  }
}

unsafe impl<'a, T: 'a> Container<'a> for *mut T {
  type Class = PtrT;
  type Item = T;
  type Raw = Self;
  type CastErr = OnlyErr;

  fn into_raw(self) -> Self::Raw {
    self
  }
  unsafe fn from_raw(ptr: Self::Raw) -> Self {
    ptr
  }
}

unsafe impl<'a, T: 'a> Container<'a> for NonNull<T> {
  type Class = NonNullT;
  type Item = T;
  type Raw = *mut T;
  type CastErr = OnlyErr;

  fn into_raw(self) -> Self::Raw {
    self.as_ptr()
  }
  unsafe fn from_raw(ptr: Self::Raw) -> Self {
    NonNull::new_unchecked(ptr)
  }
}

#[cfg(feature = "non_null_slice_cast")]
unsafe impl<'a, T: 'a> Container<'a> for NonNull<[T]> {
  type Class = NonNullT;
  type Item = T;
  type Raw = (*mut T, usize);
  type CastErr = OnlyErr;

  fn into_raw(self) -> Self::Raw {
    (self.as_ptr() as *mut T, self.len())
  }
  unsafe fn from_raw((data, len): Self::Raw) -> Self {
    NonNull::new_unchecked(core::ptr::slice_from_raw_parts_mut(data, len))
  }
}

unsafe impl<'a, T: 'a> Container<'a> for AtomicPtr<T> {
  type Class = AtomicPtrT;
  type Item = T;
  type Raw = *mut T;
  type CastErr = OnlyErr;

  fn into_raw(self) -> Self::Raw {
    self.into_inner()
  }
  unsafe fn from_raw(ptr: Self::Raw) -> Self {
    Self::new(ptr)
  }
}

unsafe impl<'a, C> Container<'a> for Option<C>
where
  C: Container<'a>,
  C::CastErr: CastErrWithValue<Self>,
{
  type Class = OptionT<C::Class>;
  type Item = C::Item;
  type Raw = Option<C::Raw>;
  type CastErr = C::CastErr;

  fn into_raw(self) -> Self::Raw {
    self.map(|x| x.into_raw())
  }
  unsafe fn from_raw(raw: Self::Raw) -> Self {
    raw.map(|raw| C::from_raw(raw))
  }
}

// SAFETY: `Pin` has no safety requirements for types which deref to an `Unpin` type.
unsafe impl<'a, C> Container<'a> for Pin<C>
where
  C: Container<'a> + Deref<Target = <C as Container<'a>>::Item>,
  C::Item: Unpin,
  C::CastErr: CastErrWithValue<Self>,
{
  type Class = PinT<C::Class>;
  type Item = C::Item;
  type Raw = C::Raw;
  type CastErr = C::CastErr;

  fn into_raw(self) -> Self::Raw {
    Self::into_inner(self).into_raw()
  }
  unsafe fn from_raw(ptr: Self::Raw) -> Self {
    Self::new(C::from_raw(ptr))
  }
}

#[cfg(feature = "extern_crate_alloc")]
unsafe impl<'a, T: 'a> Container<'a> for Box<T> {
  type Class = BoxT;
  type Item = T;
  type Raw = *const T;
  type CastErr = ErrWithValue;

  fn into_raw(self) -> Self::Raw {
    Self::into_raw(self)
  }
  unsafe fn from_raw(ptr: Self::Raw) -> Self {
    Self::from_raw(ptr as *mut T)
  }
}

#[cfg(feature = "extern_crate_alloc")]
unsafe impl<'a, T: 'a> Container<'a> for Box<[T]> {
  type Class = BoxT;
  type Item = T;
  type Raw = (*const T, usize);
  type CastErr = ErrWithValue;

  fn into_raw(self) -> Self::Raw {
    let len = self.len();
    (Self::into_raw(self) as *mut T, len)
  }
  unsafe fn from_raw((data, len): Self::Raw) -> Self {
    Self::from_raw(core::ptr::slice_from_raw_parts_mut(data as *mut T, len))
  }
}

#[cfg(feature = "extern_crate_alloc")]
#[derive(Clone, Copy)]
pub enum RawCow<B: Copy, O: Copy> {
  Borrowed(B),
  Owned(O),
}
#[cfg(feature = "extern_crate_alloc")]
unsafe impl<'a, T: 'a + Copy> Container<'a> for Cow<'a, T> {
  type Class = CowT;
  type Item = T;
  type Raw = RawCow<*const T, T>;
  type CastErr = ErrWithValue;

  fn into_raw(self) -> Self::Raw {
    match self {
      Self::Borrowed(x) => RawCow::Borrowed(x as *const T),
      Self::Owned(x) => RawCow::Owned(x),
    }
  }
  unsafe fn from_raw(raw: Self::Raw) -> Self {
    match raw {
      RawCow::Borrowed(x) => Self::Borrowed(&*x),
      RawCow::Owned(x) => Self::Owned(x),
    }
  }
}
#[cfg(feature = "extern_crate_alloc")]
unsafe impl<'a, T: 'a + Copy> Container<'a> for Cow<'a, [T]> {
  type Class = CowT;
  type Item = T;
  type Raw = RawCow<(*const T, usize), (*const T, usize, usize)>;
  type CastErr = ErrWithValue;

  fn into_raw(self) -> Self::Raw {
    match self {
      Self::Borrowed(x) => RawCow::Borrowed(x.into_raw()),
      Self::Owned(x) => RawCow::Owned(x.into_raw()),
    }
  }
  unsafe fn from_raw(raw: Self::Raw) -> Self {
    match raw {
      RawCow::Borrowed(x) => Self::Borrowed(Container::from_raw(x)),
      RawCow::Owned(x) => Self::Owned(Container::from_raw(x)),
    }
  }
}

#[cfg(feature = "extern_crate_alloc")]
unsafe impl<'a, T: 'a> Container<'a> for Rc<T> {
  type Class = RcT;
  type Item = T;
  type Raw = *mut T;
  type CastErr = ErrWithValue;

  fn into_raw(self) -> Self::Raw {
    Self::into_raw(self) as *mut T
  }
  unsafe fn from_raw(raw: Self::Raw) -> Self {
    Self::from_raw(raw)
  }
}

#[cfg(feature = "extern_crate_alloc")]
unsafe impl<'a, T: 'a> Container<'a> for Rc<[T]> {
  type Class = RcT;
  type Item = T;
  type Raw = (*mut T, usize);
  type CastErr = ErrWithValue;

  fn into_raw(self) -> Self::Raw {
    let len = self.len();
    (Self::into_raw(self) as *mut T, len)
  }
  unsafe fn from_raw((data, len): Self::Raw) -> Self {
    Self::from_raw(core::ptr::slice_from_raw_parts(data, len))
  }
}

#[cfg(feature = "extern_crate_alloc")]
unsafe impl<'a, T: 'a> Container<'a> for RcWeak<T> {
  type Class = RcWeakT;
  type Item = T;
  type Raw = *mut T;
  type CastErr = ErrWithValue;

  fn into_raw(self) -> Self::Raw {
    Self::into_raw(self) as *mut T
  }
  unsafe fn from_raw(raw: Self::Raw) -> Self {
    Self::from_raw(raw)
  }
}

#[cfg(feature = "extern_crate_alloc")]
unsafe impl<'a, T: 'a> Container<'a> for Arc<T> {
  type Class = ArcT;
  type Item = T;
  type Raw = *mut T;
  type CastErr = ErrWithValue;

  fn into_raw(self) -> Self::Raw {
    Self::into_raw(self) as *mut T
  }
  unsafe fn from_raw(raw: Self::Raw) -> Self {
    Self::from_raw(raw)
  }
}

#[cfg(feature = "extern_crate_alloc")]
unsafe impl<'a, T: 'a> Container<'a> for Arc<[T]> {
  type Class = ArcT;
  type Item = T;
  type Raw = (*mut T, usize);
  type CastErr = ErrWithValue;

  fn into_raw(self) -> Self::Raw {
    let len = self.len();
    (Self::into_raw(self) as *mut T, len)
  }
  unsafe fn from_raw((data, len): Self::Raw) -> Self {
    Self::from_raw(core::ptr::slice_from_raw_parts(data, len))
  }
}

#[cfg(feature = "extern_crate_alloc")]
unsafe impl<'a, T: 'a> Container<'a> for ArcWeak<T> {
  type Class = ArcWeakT;
  type Item = T;
  type Raw = *mut T;
  type CastErr = ErrWithValue;

  fn into_raw(self) -> Self::Raw {
    Self::into_raw(self) as *mut T
  }
  unsafe fn from_raw(raw: Self::Raw) -> Self {
    Self::from_raw(raw)
  }
}

#[cfg(feature = "extern_crate_alloc")]
unsafe impl<'a, T: 'a> Container<'a> for Vec<T> {
  type Class = VecT;
  type Item = T;
  type Raw = (*const T, usize, usize);
  type CastErr = ErrWithValue;

  fn into_raw(self) -> Self::Raw {
    let mut x = ManuallyDrop::new(self);
    (x.as_mut_ptr() as *const T, x.len(), x.capacity())
  }
  unsafe fn from_raw((data, len, cap): Self::Raw) -> Self {
    Self::from_raw_parts(data as *mut T, len, cap)
  }
}

fn check_alignment<T, U>(ptr: *const T) -> Result<(), PodCastError> {
  if align_of::<T>() >= align_of::<U>() || ptr as usize % align_of::<U>() == 0 {
    Ok(())
  } else {
    Err(PodCastError::AlignmentMismatch)
  }
}

fn cast_len<T, U>(size: usize) -> Result<usize, PodCastError> {
  if size_of::<T>() == size_of::<U>() {
    Ok(size)
  } else {
    let d = if size_of::<U>() == 0 { 1 } else { size_of::<U>() };
    let byte_size = size * size_of::<T>();
    if byte_size % d == 0 {
      Ok(byte_size / d)
    } else {
      Err(PodCastError::OutputSliceWouldHaveSlop)
    }
  }
}

pub unsafe trait CastRaw<T: Copy>: Copy {
  fn cast_raw(self) -> T;
}

unsafe impl<T, U> CastRaw<*const U> for *const T
where
  T: NoUninit,
  U: AnyBitPattern,
{
  fn cast_raw(self) -> *const U {
    static_assert!(AssertSameSize(T, U));
    static_assert!(AssertMinAlign(T, U));
    self as *const U
  }
}
unsafe impl<T, U> CastRaw<*const U> for *mut T
where
  T: NoUninit,
  U: AnyBitPattern,
{
  fn cast_raw(self) -> *const U {
    (self as *const T).cast_raw()
  }
}
unsafe impl<T, U> CastRaw<*mut U> for *mut T
where
  T: NoUninit + AnyBitPattern,
  U: NoUninit + AnyBitPattern,
{
  fn cast_raw(self) -> *mut U {
    static_assert!(AssertSameSize(T, U));
    static_assert!(AssertMinAlign(T, U));
    self as *mut U
  }
}

unsafe impl<T, U> CastRaw<(*const U, usize)> for (*const T, usize)
where
  T: NoUninit,
  U: AnyBitPattern,
{
  fn cast_raw(self) -> (*const U, usize) {
    static_assert!(AssertSizeMultipleOf(T, U));
    static_assert!(AssertMinAlign(T, U));
    let m =
      if size_of::<T>() == 0 { 1 } else { size_of::<T>() / size_of::<U>() };
    (self.0 as *const U, self.1 * m)
  }
}
unsafe impl<T, U> CastRaw<(*const U, usize)> for (*mut T, usize)
where
  T: NoUninit,
  U: AnyBitPattern,
{
  fn cast_raw(self) -> (*const U, usize) {
    (self.0 as *const T, self.1).cast_raw()
  }
}
unsafe impl<T, U> CastRaw<(*mut U, usize)> for (*mut T, usize)
where
  T: NoUninit + AnyBitPattern,
  U: NoUninit + AnyBitPattern,
{
  fn cast_raw(self) -> (*mut U, usize) {
    static_assert!(AssertSizeMultipleOf(T, U));
    static_assert!(AssertMinAlign(T, U));
    let m =
      if size_of::<T>() == 0 { 1 } else { size_of::<T>() / size_of::<U>() };
    (self.0 as *mut U, self.1 * m)
  }
}

#[cfg(feature = "extern_crate_alloc")]
unsafe impl<T, U> CastRaw<RawCow<*const U, U>> for RawCow<*const T, T>
where
  T: NoUninit,
  U: AnyBitPattern,
{
  fn cast_raw(self) -> RawCow<*const U, U> {
    match self {
      Self::Borrowed(x) => RawCow::Borrowed(x.cast_raw()),
      Self::Owned(x) => RawCow::Owned(x.reinterpret()),
    }
  }
}
#[cfg(feature = "extern_crate_alloc")]
unsafe impl<T, U> CastRaw<RawCow<(*const U, usize), (*const U, usize, usize)>>
  for RawCow<(*const T, usize), (*const T, usize, usize)>
where
  T: NoUninit,
  U: AnyBitPattern,
{
  fn cast_raw(self) -> RawCow<(*const U, usize), (*const U, usize, usize)> {
    match self {
      Self::Borrowed(x) => RawCow::Borrowed(x.cast_raw()),
      Self::Owned(x) => RawCow::Owned(x.cast_raw()),
    }
  }
}

#[cfg(feature = "extern_crate_alloc")]
unsafe impl<T, U> CastRaw<(*const U, usize, usize)> for (*const T, usize, usize)
where
  T: NoUninit,
  U: AnyBitPattern,
{
  fn cast_raw(self) -> (*const U, usize, usize) {
    static_assert!(AssertSizeMultipleOf(T, U));
    static_assert!(AssertMinAlign(T, U));
    let m =
      if size_of::<T>() == 0 { 1 } else { size_of::<T>() / size_of::<U>() };
    (self.0 as *const U, self.1 * m, self.2 * m)
  }
}

/// Casts the raw representation of a container, without regard for any
/// constraints the container would apply.
pub unsafe trait TryCastRaw<T: Copy>: Copy {
  /// Perform the cast.
  fn try_cast_raw(self) -> Result<T, PodCastError>;
}

unsafe impl<T, U> TryCastRaw<*const U> for *const T
where
  T: NoUninit,
  U: AnyBitPattern,
{
  fn try_cast_raw(self) -> Result<*const U, PodCastError> {
    static_assert!(AssertSameSize(T, U));
    check_alignment::<_, U>(self)?;
    Ok(self as *const U)
  }
}
unsafe impl<T, U> TryCastRaw<*const U> for *mut T
where
  T: NoUninit,
  U: AnyBitPattern,
{
  fn try_cast_raw(self) -> Result<*const U, PodCastError> {
    (self as *const T).try_cast_raw()
  }
}
unsafe impl<T, U> TryCastRaw<*mut U> for *mut T
where
  T: NoUninit + AnyBitPattern,
  U: NoUninit + AnyBitPattern,
{
  fn try_cast_raw(self) -> Result<*mut U, PodCastError> {
    static_assert!(AssertSameSize(T, U));
    check_alignment::<_, U>(self)?;
    Ok(self as *mut U)
  }
}

unsafe impl<T, U> TryCastRaw<(*const U, usize)> for (*const T, usize)
where
  T: NoUninit,
  U: AnyBitPattern,
{
  fn try_cast_raw(self) -> Result<(*const U, usize), PodCastError> {
    check_alignment::<T, U>(self.0)?;
    let len = cast_len::<T, U>(self.1)?;
    Ok((self.0 as *const U, len))
  }
}
unsafe impl<T, U> TryCastRaw<(*const U, usize)> for (*mut T, usize)
where
  T: NoUninit,
  U: AnyBitPattern,
{
  fn try_cast_raw(self) -> Result<(*const U, usize), PodCastError> {
    (self.0 as *const T, self.1).try_cast_raw()
  }
}
unsafe impl<T, U> TryCastRaw<(*mut U, usize)> for (*mut T, usize)
where
  T: NoUninit + AnyBitPattern,
  U: NoUninit + AnyBitPattern,
{
  fn try_cast_raw(self) -> Result<(*mut U, usize), PodCastError> {
    check_alignment::<T, U>(self.0)?;
    let len = cast_len::<T, U>(self.1)?;
    Ok((self.0 as *mut U, len))
  }
}

unsafe impl<T, U> TryCastRaw<*const U> for (*const T, usize)
where
  T: NoUninit,
  U: AnyBitPattern,
{
  fn try_cast_raw(self) -> Result<*const U, PodCastError> {
    static_assert!(AssertMaxSize(T, U));
    check_alignment::<T, U>(self.0)?;
    if self.1 * size_of::<T>() == size_of::<U>() {
      Ok(self.0 as *const U)
    } else {
      Err(PodCastError::SizeMismatch)
    }
  }
}
unsafe impl<T, U> TryCastRaw<*const U> for (*mut T, usize)
where
  T: NoUninit,
  U: AnyBitPattern,
{
  fn try_cast_raw(self) -> Result<*const U, PodCastError> {
    (self.0 as *const T, self.1).try_cast_raw()
  }
}
unsafe impl<T, U> TryCastRaw<*mut U> for (*mut T, usize)
where
  T: NoUninit + AnyBitPattern,
  U: NoUninit + AnyBitPattern,
{
  fn try_cast_raw(self) -> Result<*mut U, PodCastError> {
    static_assert!(AssertMaxSize(T, U));
    check_alignment::<T, U>(self.0)?;
    if self.1 * size_of::<T>() == size_of::<U>() {
      Ok(self.0 as *mut U)
    } else {
      Err(PodCastError::SizeMismatch)
    }
  }
}

unsafe impl<T, U> TryCastRaw<(*const U, usize)> for *const T
where
  T: NoUninit,
  U: AnyBitPattern,
{
  fn try_cast_raw(self) -> Result<(*const U, usize), PodCastError> {
    static_assert!(AssertSizeMultipleOf(T, U));
    static_assert!(AssertNonZeroSize(T));
    static_assert!(AssertNonZeroSize(U));
    check_alignment::<T, U>(self)?;
    Ok((self as *const U, size_of::<T>() / size_of::<U>()))
  }
}
unsafe impl<T, U> TryCastRaw<(*const U, usize)> for *mut T
where
  T: NoUninit,
  U: AnyBitPattern,
{
  fn try_cast_raw(self) -> Result<(*const U, usize), PodCastError> {
    (self as *const T).try_cast_raw()
  }
}
unsafe impl<T, U> TryCastRaw<(*mut U, usize)> for *mut T
where
  T: NoUninit + AnyBitPattern,
  U: NoUninit + AnyBitPattern,
{
  fn try_cast_raw(self) -> Result<(*mut U, usize), PodCastError> {
    static_assert!(AssertSizeMultipleOf(T, U));
    static_assert!(AssertNonZeroSize(T));
    static_assert!(AssertNonZeroSize(U));
    check_alignment::<T, U>(self)?;
    Ok((self as *mut U, size_of::<T>() / size_of::<U>()))
  }
}

#[cfg(feature = "extern_crate_alloc")]
unsafe impl<T, U> TryCastRaw<RawCow<*const U, U>> for RawCow<*const T, T>
where
  T: NoUninit,
  U: AnyBitPattern,
{
  fn try_cast_raw(self) -> Result<RawCow<*const U, U>, PodCastError> {
    Ok(match self {
      Self::Borrowed(x) => RawCow::Borrowed(x.try_cast_raw()?),
      Self::Owned(x) => RawCow::Owned(x.reinterpret()),
    })
  }
}
#[cfg(feature = "extern_crate_alloc")]
unsafe impl<T, U> TryCastRaw<(*const U, usize, usize)>
  for (*const T, usize, usize)
where
  T: NoUninit,
  U: AnyBitPattern,
{
  fn try_cast_raw(self) -> Result<(*const U, usize, usize), PodCastError> {
    let len = cast_len::<T, U>(self.1)?;
    let cap = cast_len::<T, U>(self.2)?;
    Ok((self.0 as *const U, len, cap))
  }
}

#[cfg(feature = "extern_crate_alloc")]
unsafe impl<T, U>
  TryCastRaw<RawCow<(*const U, usize), (*const U, usize, usize)>>
  for RawCow<(*const T, usize), (*const T, usize, usize)>
where
  T: NoUninit,
  U: AnyBitPattern,
{
  fn try_cast_raw(
    self,
  ) -> Result<RawCow<(*const U, usize), (*const U, usize, usize)>, PodCastError>
  {
    static_assert!(AssertSameAlign(T, U));
    Ok(match self {
      Self::Borrowed(x) => RawCow::Borrowed(x.try_cast_raw()?),
      Self::Owned(x) => RawCow::Owned(x.try_cast_raw()?),
    })
  }
}

/// Checks any constraints the container requires when casting between types.
pub trait AssertClassContraints<T, U> {
  const ASSERT: () = ();
}
impl<T, U> AssertClassContraints<T, U> for RefT {}
impl<T, U> AssertClassContraints<T, U> for PtrT {}
impl<T, U> AssertClassContraints<T, U> for NonNullT {}
impl<T, U> AssertClassContraints<T, U> for AtomicPtrT {}
impl<'a, C, T, U> AssertClassContraints<T, U> for OptionT<C>
where
  C: AssertClassContraints<T, U>,
{
  const ASSERT: () = C::ASSERT;
}
impl<'a, C, T, U> AssertClassContraints<T, U> for PinT<C>
where
  C: AssertClassContraints<T, U>,
{
  const ASSERT: () = C::ASSERT;
}
#[cfg(feature = "extern_crate_alloc")]
impl<T, U> AssertClassContraints<T, U> for BoxT {
  const ASSERT: () = static_assert!(AssertSameAlign(T, U));
}
#[cfg(feature = "extern_crate_alloc")]
impl<T, U> AssertClassContraints<T, U> for RcT {
  const ASSERT: () = static_assert!(AssertSameAlign(T, U));
}
#[cfg(feature = "extern_crate_alloc")]
impl<T, U> AssertClassContraints<T, U> for RcWeakT {
  const ASSERT: () = static_assert!(AssertSameAlign(T, U));
}
#[cfg(feature = "extern_crate_alloc")]
impl<T, U> AssertClassContraints<T, U> for ArcT {
  const ASSERT: () = static_assert!(AssertSameAlign(T, U));
}
#[cfg(feature = "extern_crate_alloc")]
impl<T, U> AssertClassContraints<T, U> for ArcWeakT {
  const ASSERT: () = static_assert!(AssertSameAlign(T, U));
}
#[cfg(feature = "extern_crate_alloc")]
impl<T, U> AssertClassContraints<T, U> for VecT {
  const ASSERT: () = static_assert!(AssertSameAlign(T, U));
}
#[cfg(feature = "extern_crate_alloc")]
impl<T: ToOwned, U: ToOwned> AssertClassContraints<T, U> for CowT {}

/// Safe byte-wise conversion between two values which contain some number of
/// values without allocation. This conversion should not fail for any reason.
pub trait ReinterpretInner<'a, T: 'a>: 'a + Sized {
  /// Performs the conversion.
  fn reinterpret_inner(self) -> T;
}
impl<'a, T: 'a, U: 'a> ReinterpretInner<'a, U> for T
where
  T: Container<'a, Class = U::Class>,
  U: Container<'a>,
  T::Class: AssertClassContraints<T::Item, U::Item>,
  T::Raw: CastRaw<U::Raw>,
{
  fn reinterpret_inner(self) -> U {
    static_assert!(AssertClassContraints(T::Class, T::Item, U::Item));
    unsafe { U::from_raw(self.into_raw().cast_raw()) }
  }
}

/// Attempt at a safe byte-wise conversion between two values which contain some
/// number of values. This conversion may fail due runtime
/// conditions such as size and alignment errors.
pub trait TryReinterpretInner<'a, T: 'a>: 'a + Sized {
  /// The type returned in the event of a conversion error.
  type Error;
  /// Perform the conversion.
  fn try_reinterpret_inner(self) -> Result<T, Self::Error>;
}
impl<'a, T: 'a, U: 'a> TryReinterpretInner<'a, U> for T
where
  T: Container<'a, Class = U::Class>,
  U: Container<'a>,
  T::Class: AssertClassContraints<T::Item, U::Item>,
  T::Raw: TryCastRaw<U::Raw>,
{
  type Error = <T::CastErr as CastErrWithValue<T>>::Err;
  fn try_reinterpret_inner(self) -> Result<U, Self::Error> {
    static_assert!(AssertNonMixedZeroSize(T::Item, U::Item));
    static_assert!(AssertClassContraints(T::Class, T::Item, U::Item));
    let raw = self.into_raw();
    match raw.try_cast_raw() {
      Ok(raw) => Ok(unsafe { U::from_raw(raw) }),
      Err(e) => {
        Err(<T::CastErr as CastErrWithValue<T>>::cast_error_with_value(
          unsafe { T::from_raw(raw) },
          e,
        ))
      }
    }
  }
}

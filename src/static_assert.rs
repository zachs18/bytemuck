//! Various type assertions used to raise compile errors. These are implemented
//! as panics during the evaluation of associated constants which will be
//! converted to compile time errors when the evaluation is forced.
//!
//! These can be used through the helper macro. e.g.
//! ```rust,ignore
//! static_assert!(AssertSameSize(u32, i32));
//! ```

use core::mem::{align_of, size_of};

pub trait AssertNonMixedZeroSize<T: Sized>: Sized {
  const ASSERT: () = {
    if (size_of::<Self>() == 0) != (size_of::<T>() == 0) {
      panic!(
        "Attempt to cast between a zero-sized type and a non-zero-sized type"
      );
    }
  };
}
impl<T, U> AssertNonMixedZeroSize<U> for T {}

pub trait AssertNonZeroSize: Sized {
  const ASSERT: () = {
    if size_of::<Self>() == 0 {
      panic!("Attempt to cast a zero-sized type");
    }
  };
}
impl<T> AssertNonZeroSize for T {}

pub trait AssertSameSize<T>: Sized {
  const ASSERT: () = {
    if size_of::<Self>() != size_of::<T>() {
      panic!("Attempt to cast between two types with different sizes");
    }
  };
}
impl<T, U> AssertSameSize<U> for T {}

pub trait AssertMaxSize<T>: Sized {
  const ASSERT: () = {
    if size_of::<Self>() > size_of::<T>() {
      panic!("Attempt to cast to a type of a smaller size");
    }
  };
}
impl<T, U> AssertMaxSize<U> for T {}

pub trait AssertSizeMultipleOf<T>: Sized {
  const ASSERT: () = {
    if size_of::<Self>() != size_of::<T>()
      && size_of::<Self>() % size_of::<T>() != 0
    {
      panic!("Attempt to cast from a type which is not a multiple of the target's size");
    }
  };
}
impl<T, U> AssertSizeMultipleOf<U> for T {}

pub trait AssertSameAlign<T>: Sized {
  const ASSERT: () = {
    if align_of::<Self>() != align_of::<T>() {
      panic!("Attempt to cast between two types with different alignments");
    }
  };
}
impl<T, U> AssertSameAlign<U> for T {}

pub trait AssertMinAlign<T>: Sized {
  const ASSERT: () = {
    if align_of::<Self>() < align_of::<T>() {
      panic!("Attempt to cast to a type with a larger alignment");
    }
  };
}
impl<T, U> AssertMinAlign<U> for T {}

macro_rules! static_assert {
    ($assertion:ident($ty:ty $(, $($args:tt)*)?)) => {{
        #[allow(path_statements)]
        { <$ty as $assertion<$($($args)*)?>>::ASSERT; }
        ()
    }}
}

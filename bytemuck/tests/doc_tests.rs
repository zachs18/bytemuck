#![allow(clippy::disallowed_names)]
#![allow(dead_code)]

//! Cargo miri doesn't run doctests yet, so we duplicate these here. It's
//! probably not that important to sweat keeping these perfectly up to date, but
//! we should try to catch the cases where the primary tests are doctests.
use bytemuck::*;

// Miri doesn't run on doctests, so... copypaste to the rescue.
#[test]
fn test_transparent_slice() {
  #[repr(transparent)]
  struct Slice<T>([T]);

  unsafe impl<T> TransparentWrapper<[T]> for Slice<T> {}

  let s = Slice::wrap_ref(&[1u32, 2, 3]);
  assert_eq!(&s.0, &[1, 2, 3]);

  let mut buf = [1, 2, 3u8];
  let _sm = Slice::wrap_mut(&mut buf);
}

#[test]
fn test_transparent_basic() {
  #[derive(Default)]
  struct SomeStruct(u32);

  #[repr(transparent)]
  struct MyWrapper(SomeStruct);

  unsafe impl TransparentWrapper<SomeStruct> for MyWrapper {}

  // interpret a reference to &SomeStruct as a &MyWrapper
  let thing = SomeStruct::default();
  let wrapped_ref: &MyWrapper = MyWrapper::wrap_ref(&thing);

  // Works with &mut too.
  let mut mut_thing = SomeStruct::default();
  let wrapped_mut: &mut MyWrapper = MyWrapper::wrap_mut(&mut mut_thing);
  let _ = (wrapped_ref, wrapped_mut);
}

// Work around miri not running doctests
#[test]
fn test_contiguous_doc() {
  #[repr(u8)]
  #[derive(Debug, Copy, Clone, PartialEq)]
  enum Foo {
    A = 0,
    B = 1,
    C = 2,
    D = 3,
    E = 4,
  }
  unsafe impl Contiguous for Foo {
    type Int = u8;
    const MIN_VALUE: u8 = Foo::A as u8;
    const MAX_VALUE: u8 = Foo::E as u8;
  }

  assert_eq!(Foo::from_integer(3).unwrap(), Foo::D);
  assert_eq!(Foo::from_integer(8), None);
  assert_eq!(Foo::C.into_integer(), 2);
  assert_eq!(Foo::B.into_integer(), Foo::B as u8);
}

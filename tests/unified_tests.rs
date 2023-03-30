#![allow(clippy::uninlined_format_args)]
#![cfg(feature = "unified_cast")]
use bytemuck::*;

#[test]
fn test_refs() {
  let x: &u32 = &42;
  let y: &[u8; 4] = x.reinterpret_inner();
  let z: &[u8; 4] = bytemuck::cast_ref(x);
  assert_eq!(y, z);
  #[cfg(target_endian = "little")]
  assert_eq!(*y, [42, 0, 0, 0]);
  #[cfg(target_endian = "big")]
  assert_eq!(*y, [0, 0, 0, 42]);
}

#[test]
#[cfg(any())]
fn test_option() {
  let x: Option<&u32> = Some(&42);
  let y: Option<&[u8; 4]> = x.reinterpret_inner();
  let z: Option<&[u8; 4]> = x.map(bytemuck::cast_ref);
  assert_eq!(y, z);
  #[cfg(target_endian = "little")]
  assert_eq!(*y.unwrap(), [42, 0, 0, 0]);
  #[cfg(target_endian = "big")]
  assert_eq!(*y.unwrap(), [0, 0, 0, 42]);
}

#[test]
#[cfg(feature = "extern_crate_alloc")]
fn test_vec() {
  extern crate alloc;
  use alloc::{vec, vec::Vec};
//  // This is caught at compile-time now
//  let x: Vec<u32> = vec![42];
//  let y: Result<Vec<u8>, _> = x.try_reinterpret_inner();
//  y.unwrap_err();

  let x: Vec<bool> = vec![true, false, true, false];
  let y: Vec<u8> = x.reinterpret_inner();
  assert_eq!(*y, [1, 0, 1, 0]);
}

#[test]
#[cfg(feature = "extern_crate_alloc")]
fn test_box_slice() {
  extern crate alloc;
  use alloc::{boxed::Box, vec};
//  // This is caught at compile-time now
//  let x: Box<[u32]> = vec![42].into();
//  let y: Result<Box<[u8]>, _> = x.try_reinterpret_inner();
//  y.unwrap_err();

  let x: Box<[bool]> = vec![true, false, true, false].into_boxed_slice();
  let y: Box<[u8]> = x.reinterpret_inner();
  assert_eq!(*y, [1, 0, 1, 0]);
}

#[test]
#[cfg(feature = "extern_crate_alloc")]
#[cfg(any())]
fn test_rc() {
  extern crate alloc;
  use alloc::{rc::Rc, vec};
//  // This is caught at compile-time now
//  let x: Rc<u32> = Rc::new(42);
//  let y: Result<Rc<[u8; 4]>, _> = x.try_reinterpret_inner();
//  y.unwrap_err();

  let x: Rc<[u32]> = vec![42].into();
  let y: Result<Rc<[u8]>, _> = x.try_reinterpret_inner();
  y.unwrap_err();

  let x: Rc<[bool]> = vec![true, false, true, false].into();
  let y: Rc<[u8]> = x.reinterpret_inner();
  assert_eq!(*y, [1, 0, 1, 0]);

  let x: Rc<bool> = Rc::new(true);
  let y: Rc<u8> = x.reinterpret_inner();
  assert_eq!(*y, 1);
}

#[test]
#[cfg(feature = "extern_crate_alloc")]
#[cfg(target_has_atomic = "ptr")]
#[cfg(any())]
fn test_arc() {
  extern crate alloc;
  use alloc::{sync::Arc, vec};
//  // This is caught at compile-time now
//  let x: Arc<[u32]> = vec![42].into();
//  let y: Result<Arc<[u8]>, _> = x.try_reinterpret_inner();
//  y.unwrap_err();

  let x: Arc<[bool]> = vec![true, false, true, false].into();
  let y: Arc<[u8]> = x.reinterpret_inner();
  assert_eq!(*y, [1, 0, 1, 0]);

  let x: Arc<bool> = Arc::new(true);
  let y: Arc<u8> = x.reinterpret_inner();
  assert_eq!(*y, 1);
}

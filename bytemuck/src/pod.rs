use super::*;

/// Marker trait for "plain old data".
///
/// The point of this trait is that once something is marked "plain old data"
/// you can really go to town with the bit fiddling and bit casting. Therefore,
/// it's a relatively strong claim to make about a type. Do not add this to your
/// type casually.
///
/// **Reminder:** The results of casting around bytes between data types are
/// _endian dependant_. Little-endian machines are the most common, but
/// big-endian machines do exist (and big-endian is also used for "network
/// order" bytes).
///
/// ## Safety
///
/// * The type must implement [`AnyBitPattern`] and [`NoUninit`], adhering to
///   all of their safety requirements.
pub unsafe trait Pod: NoUninit + AnyBitPattern {}

// No other impls needed
unsafe impl<T: NoUninit + AnyBitPattern + ?Sized> Pod for T {}

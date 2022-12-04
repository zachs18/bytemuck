use super::*;

/// Trait for types which are [Pod](Pod) when wrapped in
/// [Option](core::option::Option). This type is automatically implemented for
/// all types that are [AnyBitPatternInOption] and [NoUninitInOption].
///
/// This can be used as a trait bound, but it is not actually used for anything,
/// since `AnyBitPatternInOption` and `NoUninitInOption` already imply that
/// `Option<Self>` is `Pod`.
pub unsafe trait PodInOption:
  AnyBitPatternInOption + NoUninitInOption + Copy + 'static
{
}

unsafe impl<T: AnyBitPatternInOption + NoUninitInOption> PodInOption for T {}

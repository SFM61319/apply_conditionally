//! The trait [`IntoEither`] provides methods for converting a type `Self`, whose
//! size is constant and known at compile-time, into an [`either::Either`] variant.

/// Provides methods for converting a type `Self` into either a [`either::Either::Left`]
/// or a [`either::Either::Right`] variant of [`either::Either`].
///
/// The [`IntoEither::into_either`] method takes a [`bool`] to determine whether
/// to convert to [`either::Either::Left`] or [`either::Either::Right`].
///
/// The [`IntoEither::into_left`] and [`IntoEither::into_right`] methods directly
/// convert to the respective variant without needing a [`bool`].
pub trait IntoEither: Sized {
    /// Converts `self` into a [`either::Either::Left`] variant of [`either::Either`]
    /// if `into_left` is `true`.
    /// Converts `self` into a [`either::Either::Right`] variant of [`either::Either`]
    /// otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use either::Either::{Left, Right};
    /// use apply_conditionally::IntoEither;
    ///
    /// let x = usize::MIN;
    ///
    /// assert_eq!(x.into_either(true), Left(x));
    /// assert_eq!(x.into_either(false), Right(x));
    /// ```
    fn into_either(self, into_left: bool) -> either::Either<Self, Self> {
        if into_left {
            self.into_left()
        } else {
            self.into_right()
        }
    }

    /// Converts `self` into a [`either::Either::Left`] variant of [`either::Either`].
    ///
    /// # Examples
    ///
    /// ```
    /// use either::Either::Left;
    /// use apply_conditionally::IntoEither;
    ///
    /// let x = usize::MIN;
    /// assert_eq!(x.into_left(), Left(x));
    /// ```
    fn into_left(self) -> either::Either<Self, Self> {
        either::Either::Left(self)
    }

    /// Converts `self` into a [`either::Either::Right`] variant of [`either::Either`].
    ///
    /// # Examples
    ///
    /// ```
    /// use either::Either::Right;
    /// use apply_conditionally::IntoEither;
    ///
    /// let x = usize::MIN;
    /// assert_eq!(x.into_right(), Right(x));
    /// ```
    fn into_right(self) -> either::Either<Self, Self> {
        either::Either::Right(self)
    }
}

impl<T> IntoEither for T {}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Clone, Copy, Debug, Default, Hash, PartialEq, Eq, PartialOrd, Ord)]
    struct Test;

    #[test]
    fn test_into_either() {
        assert_eq!(Test.into_either(true), either::Either::Left(Test));
        assert_eq!(Test.into_either(false), either::Either::Right(Test));
    }

    #[test]
    fn test_into_left() {
        assert_eq!(Test.into_left(), either::Either::Left(Test));
    }

    #[test]
    fn test_into_right() {
        assert_eq!(Test.into_right(), either::Either::Right(Test));
    }
}

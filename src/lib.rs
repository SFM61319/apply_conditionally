//! # Apply Conditionally
//!
//! *Chain and apply methods on objects conditionally.*

#![no_std]

use either::IntoEither;

/// Provides methods for conditionally applying methods on a type `Self`,
/// whose size is constant and known at compile-time.
///
/// The [`ApplyConditionally::apply`] method always applies `f` on `self`.
///
/// The [`ApplyConditionally::apply_if`] method takes a [`bool`] to determine
/// whether to apply `f` on `self` or not.
///
/// The [`ApplyConditionally::apply_or_else`] method takes a [`bool`] to
/// determine whether to apply `f` or `g` on `self`.
pub trait ApplyConditionally: Sized {
    /// Applies `f` on `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use apply_conditionally::ApplyConditionally;
    ///
    /// fn add2(x: u32) -> u32 {
    ///     x + 2
    /// }
    ///
    /// fn mul2(x: u32) -> u32 {
    ///     x * 2
    /// }
    ///
    /// let x = 2;
    /// assert_eq!(x.apply(add2).apply(mul2), 8);
    /// ```
    ///
    /// is the same as doing:
    ///
    /// ```
    /// use apply_conditionally::ApplyConditionally;
    ///
    /// fn add2(x: u32) -> u32 {
    ///     x + 2
    /// }
    ///
    /// fn mul2(x: u32) -> u32 {
    ///     x * 2
    /// }
    ///
    /// let x = 2;
    /// assert_eq!(mul2(add2(x)), 8);
    /// ```
    #[inline]
    fn apply<T, F>(self, f: F) -> T
    where
        F: FnOnce(Self) -> T,
    {
        f(self)
    }

    /// Applies `f` on `self` if and only if `condition` is `true`.
    /// Does nothing otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use apply_conditionally::ApplyConditionally;
    ///
    /// fn u8_to_bools(value: u8, rtl: bool) -> [bool; 8] {
    ///     let mut result = [false; 8];
    ///     result
    ///         .iter_mut()
    ///         .apply_if(rtl, Iterator::rev)
    ///         .enumerate()
    ///         .for_each(|(i, b)| *b = ((value >> i) & 1) == 1);
    ///
    ///     result
    /// }
    ///
    /// assert_eq!(
    ///     u8_to_bools(0b00101101, false),
    ///     [true, false, true, true, false, true, false, false]
    /// );
    /// assert_eq!(
    ///     u8_to_bools(0b00101101, true),
    ///     [false, false, true, false, true, true, false, true]
    /// );
    /// ```
    ///
    /// is the same as doing:
    ///
    /// ```
    /// fn u8_to_bools(value: u8, rtl: bool) -> [bool; 8] {
    ///     let mut result = [false; 8];
    ///     if rtl {
    ///         result
    ///             .iter_mut()
    ///             .rev()
    ///             .enumerate()
    ///             .for_each(|(i, b)| *b = ((value >> i) & 1) == 1);
    ///     } else {
    ///         result
    ///             .iter_mut()
    ///             .enumerate()
    ///             .for_each(|(i, b)| *b = ((value >> i) & 1) == 1);
    ///     }
    ///
    ///     result
    /// }
    ///
    /// assert_eq!(
    ///     u8_to_bools(0b00101101, false),
    ///     [true, false, true, true, false, true, false, false]
    /// );
    /// assert_eq!(
    ///     u8_to_bools(0b00101101, true),
    ///     [false, false, true, false, true, true, false, true]
    /// );
    /// ```
    #[inline]
    fn apply_if<T, F>(self, condition: bool, f: F) -> either::Either<T, Self>
    where
        F: FnOnce(Self) -> T,
    {
        self.into_either(condition).map_left(f)
    }

    /// Applies `f` on `self` if `condition` is `true`.
    /// Applies `g` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use apply_conditionally::ApplyConditionally;
    ///
    /// fn get_pairs(bytes: &[u8], overlap: bool) -> Vec<(u8, u8)> {
    ///     bytes
    ///         .apply_or_else(overlap, |bytes| bytes.windows(2), |bytes| bytes.chunks(2))
    ///         .map(|w| (w[0], w[1]))
    ///         .collect()
    /// }
    ///
    /// assert_eq!(get_pairs(b"abcd", false), vec![(b'a', b'b'), (b'c', b'd')]);
    /// assert_eq!(
    ///     get_pairs(b"abcd", true),
    ///     vec![(b'a', b'b'), (b'b', b'c'), (b'c', b'd')]
    /// );
    /// ```
    ///
    /// is the same as doing:
    ///
    /// ```
    /// fn get_pairs(bytes: &[u8], overlap: bool) -> Vec<(u8, u8)> {
    ///     if overlap {
    ///         bytes.windows(2).map(|w| (w[0], w[1])).collect()
    ///     } else {
    ///         bytes.chunks(2).map(|w| (w[0], w[1])).collect()
    ///     }
    /// }
    ///
    /// assert_eq!(get_pairs(b"abcd", false), vec![(b'a', b'b'), (b'c', b'd')]);
    /// assert_eq!(
    ///     get_pairs(b"abcd", true),
    ///     vec![(b'a', b'b'), (b'b', b'c'), (b'c', b'd')]
    /// );
    /// ```
    #[inline]
    fn apply_or_else<L, R, F, G>(self, condition: bool, f: F, g: G) -> either::Either<L, R>
    where
        F: FnOnce(Self) -> L,
        G: FnOnce(Self) -> R,
    {
        self.into_either(condition).map_either(f, g)
    }
}

impl<T> ApplyConditionally for T {}

#[cfg(test)]
mod tests {
    use super::*;

    fn add2(x: usize) -> usize {
        x + 2
    }

    fn mul2(x: usize) -> usize {
        x * 2
    }

    #[test]
    fn test_apply() {
        let x = 2;

        assert_eq!(x.apply(add2), add2(x));
        assert_eq!(x.apply(add2).apply(|x| mul2(x)), mul2(add2(x)));
    }

    #[test]
    fn test_apply_if() {
        let x = 2;

        assert_eq!(
            x.apply_if(true, |x| x.apply(add2).apply(mul2)),
            either::Either::Left(x.apply(add2).apply(mul2))
        );
        assert_eq!(
            x.apply_if(false, |x| x.apply(add2).apply(mul2)),
            either::Either::Right(x)
        );
    }

    #[test]
    fn test_apply_or_else() {
        let x = 2;

        assert_eq!(
            x.apply_or_else(
                true,
                |x| x.apply(add2).apply(mul2),
                |x| x.apply(mul2).apply(add2)
            ),
            either::Either::Left(x.apply(add2).apply(mul2))
        );
        assert_eq!(
            x.apply_or_else(
                false,
                |x| x.apply(add2).apply(mul2),
                |x| x.apply(mul2).apply(add2)
            ),
            either::Either::Right(x.apply(mul2).apply(add2))
        );
    }
}

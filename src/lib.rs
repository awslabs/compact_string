#![allow(rustdoc::bare_urls)]
#![doc = include_str!("../README.md")]

use std::{
    alloc::{alloc, dealloc, handle_alloc_error, Layout},
    borrow::Borrow,
    cmp::Ordering,
    fmt::{self, Debug},
    hash::{Hash, Hasher},
    ops::Deref,
    ptr::{copy_nonoverlapping, NonNull},
    str::FromStr,
};

use serde::{Deserialize, Deserializer, Serialize, Serializer};
use thiserror::Error;

/// Representation for UTF-8 Strings that are immutable and less than 256 bytes in length.
/// See more in the crate-level documentation.
pub struct CompactString {
    /// NonNull is a wrapper around a pointer that tells the compiler the value
    /// must never be null. This lets the compiler apply layout optimization,
    /// such as representing `Option<CompactString>` with no more space than CompactString
    /// by using null value location as the enum discriminator of Option. Without this,
    /// and due to alignment, `Option<CompactString>` would be 16 bytes instead of 8.
    ///
    /// [See more](https://doc.rust-lang.org/std/ptr/struct.NonNull.html)
    ptr: NonNull<u8>,
}

#[derive(Error, Debug, PartialEq)]
#[error("Invalid string length: {0}")]
pub struct CompactStringLengthError(usize);

/// Errors that can occur when parsing `from_utf8`.
#[derive(Error, Debug, PartialEq)]
pub enum ParseCompactStringError {
    #[error(transparent)]
    LengthError(#[from] CompactStringLengthError),
    #[error(transparent)]
    Utf8Error(#[from] std::str::Utf8Error),
}

impl CompactString {
    /// Creates a new `CompactString` from a string slice.
    /// If the length of the string exceeds 255, it returns an error.
    ///
    /// # Examples
    ///
    /// ```
    /// use compact_string::CompactString;
    ///
    /// let s = CompactString::try_new("foo").unwrap();
    /// ```
    pub fn try_new(data: &str) -> Result<CompactString, CompactStringLengthError> {
        let data_len = data.len();

        if data_len > 255 {
            return Err(CompactStringLengthError(data_len));
        }

        let layout = Self::memory_layout(data_len);

        let ptr = unsafe {
            // SAFETY: `layout` is ensured to have non-zero size since a layout of size
            // data_len + 1 is created, and data_len cannot be negative.
            let alloc_ptr = alloc(layout);

            if alloc_ptr.is_null() {
                handle_alloc_error(layout);
            }

            // SAFETY: the resulting pointer is guaranteed to be in-bound in the allocated object
            *alloc_ptr.add(0) = data_len as u8;

            // SAFETY: `alloc_ptr.add(1)` is always in-bound or one byte past the allocated object.
            // `src` and `dst` have the same alignmnent and two regions cannot overlap because
            // `dst` region is newly allocated.
            copy_nonoverlapping(data.as_ptr(), alloc_ptr.add(1), data_len);

            // SAFETY: null pointer is checked in above logic.
            NonNull::new_unchecked(alloc_ptr)
        };

        Ok(CompactString { ptr })
    }

    /// Returns the length of this `CompactString`, in bytes, not [`char`]s or
    /// graphemes. In other words, it might not be what a human considers the
    /// length of the string.
    ///
    /// Maximum length of `CompactString` is 255.
    ///
    /// # Examples
    ///
    /// ```
    /// use compact_string::CompactString;
    ///
    /// let a = CompactString::try_new("foo").unwrap();
    /// assert_eq!(a.len(), 3);
    ///
    /// let fancy_f = CompactString::try_new("ƒoo").unwrap();
    /// assert_eq!(fancy_f.len(), 4);
    /// assert_eq!(fancy_f.chars().count(), 3);
    /// ```
    #[inline]
    pub fn len(&self) -> usize {
        // SAFETY: the pointer is guaranteed to be non-null and valid for reads.
        unsafe { *self.ptr.as_ptr() as usize }
    }

    /// Returns `true` if this `String` has a length of zero, and `false` otherwise.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Convert a slice of bytes into a `CompactString`.
    ///
    /// A `CompactString` is a contiguous collection of bytes (`u8`s) that is valid [`UTF-8`](https://en.wikipedia.org/wiki/UTF-8).
    /// This method converts from an arbitrary contiguous collection of bytes into a
    /// `CompactString`, failing if the provided bytes are not `UTF-8`.
    ///
    /// Note: this function would also fail if the length of bytes exceed the maximum `CompactString` limit.
    ///
    /// # Examples
    /// ### Valid UTF-8
    /// ```
    /// use compact_string::CompactString;
    ///
    /// let bytes = vec![240, 159, 166, 128, 240, 159, 146, 175];
    /// let compact = CompactString::from_utf8(bytes).expect("valid UTF-8");
    ///
    /// assert_eq!(compact, "🦀💯");
    /// ```
    ///
    /// ### Invalid UTF-8
    /// ```
    /// use compact_string::CompactString;
    ///
    /// let bytes = vec![255, 255, 255];
    /// let result = CompactString::from_utf8(bytes);
    ///
    /// assert!(result.is_err());
    /// ```
    #[inline]
    pub fn from_utf8<B: AsRef<[u8]>>(bytes: B) -> Result<Self, ParseCompactStringError> {
        let s = std::str::from_utf8(bytes.as_ref())?;
        Ok(Self::try_new(s)?)
    }

    /// Returns a byte slice of this `CompactString`'s contents.
    ///
    /// The inverse of this method is `from_utf8`.
    ///
    /// # Examples
    ///
    /// ```
    /// use compact_string::CompactString;
    ///
    /// let s = CompactString::try_new("hello").unwrap();
    ///
    /// assert_eq!(&[104, 101, 108, 108, 111], s.as_bytes());
    /// ```
    #[inline]
    pub fn as_bytes(&self) -> &[u8] {
        let data_len = self.len();

        // SAFETY: resulting pointer is always always in-bound or pointed one byte past the allocated
        // object, and it is guaranteed to have data_len number of bytes to read from `new`.
        unsafe { std::slice::from_raw_parts(self.ptr.as_ptr().add(1), data_len) }
    }

    /// Extracts a string slice containing the entire `CompactString`.
    ///
    /// # Examples
    ///
    /// ```
    /// use compact_string::CompactString;
    ///
    /// let s = CompactString::try_new("foo").unwrap();
    ///
    /// assert_eq!("foo", s.as_str());
    /// ```
    #[inline]
    pub fn as_str(&self) -> &str {
        // SAFETY: `CompactString` always contain valid utf-8
        unsafe { std::str::from_utf8_unchecked(self.as_bytes()) }
    }

    #[inline]
    fn memory_layout(data_len: usize) -> Layout {
        Layout::array::<u8>(data_len + 1).unwrap()
    }
}

impl Drop for CompactString {
    fn drop(&mut self) {
        let data_len = self.len();

        // SAFETY: ptr is non-null and save memory layout is reused in `new`
        unsafe {
            dealloc(self.ptr.as_ptr(), Self::memory_layout(data_len));
        }
    }
}

// SAFETY: No one besides us has the raw pointer, so we can safely transfer
// the CompactString to another thread.
unsafe impl Send for CompactString {}

// SAFETY: No mutable reference can be returned from CompactString, and
// CompactString itself does not use any interior mutability.
unsafe impl Sync for CompactString {}

impl Hash for CompactString {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.as_str().hash(state);
    }
}

impl Borrow<str> for CompactString {
    fn borrow(&self) -> &str {
        self.as_str()
    }
}

impl Clone for CompactString {
    #[inline]
    fn clone(&self) -> Self {
        CompactString::try_new(self.as_str()).unwrap()
    }
}

impl FromStr for CompactString {
    type Err = CompactStringLengthError;

    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        CompactString::try_new(s)
    }
}

impl TryFrom<String> for CompactString {
    type Error = CompactStringLengthError;

    #[inline]
    fn try_from(s: String) -> Result<Self, Self::Error> {
        CompactString::try_new(&s)
    }
}

impl AsRef<str> for CompactString {
    #[inline]
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl Deref for CompactString {
    type Target = str;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_str()
    }
}

impl fmt::Display for CompactString {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

impl Debug for CompactString {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

impl PartialEq<str> for CompactString {
    fn eq(&self, other: &str) -> bool {
        self.as_str() == other
    }
}

impl PartialEq<&'_ str> for CompactString {
    fn eq(&self, other: &&str) -> bool {
        self.as_str() == *other
    }
}

impl PartialEq<CompactString> for &'_ str {
    fn eq(&self, other: &CompactString) -> bool {
        other.eq(*self)
    }
}

impl PartialEq<CompactString> for str {
    fn eq(&self, other: &CompactString) -> bool {
        other.eq(self)
    }
}

impl PartialEq<CompactString> for CompactString {
    fn eq(&self, other: &CompactString) -> bool {
        self.ptr == other.ptr || self.as_bytes() == other.as_bytes()
    }
}

impl PartialEq<String> for CompactString {
    fn eq(&self, other: &String) -> bool {
        self.as_str() == other.as_str()
    }
}

impl PartialEq<CompactString> for String {
    fn eq(&self, other: &CompactString) -> bool {
        other.eq(self.as_str())
    }
}

impl Eq for CompactString {}

impl Serialize for CompactString {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(self.as_str())
    }
}

impl Ord for CompactString {
    fn cmp(&self, other: &Self) -> Ordering {
        self.as_str().cmp(other.as_str())
    }
}

impl PartialOrd for CompactString {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<'de> Deserialize<'de> for CompactString {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        let s = String::deserialize(d)?;
        Ok(CompactString::try_new(&s).unwrap())
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use rand::RngCore;
    use std::collections::HashMap;
    use std::hash::BuildHasher;
    use std::hash::RandomState;

    #[test]
    fn size_check() {
        assert_eq!(std::mem::size_of::<CompactString>(), 8);
    }

    #[test]
    fn conversions() {
        let s1: CompactString = "Hello world".parse::<CompactString>().unwrap();
        let s2: CompactString = s1.clone();
        assert_eq!(s1, s2);
        assert_eq!(s2.as_str(), "Hello world");
    }

    #[test]
    fn from_to_string() {
        let s = "This is a test str";
        let compact = CompactString::try_new(s).unwrap();
        assert_eq!(compact.as_str(), s);

        let s = String::from("This is a test string");
        let compact: CompactString = s.clone().parse::<CompactString>().unwrap();
        assert_eq!(compact.to_string(), s);
    }

    #[test]
    fn test_length() {
        let s: CompactString = "hello world!".parse::<CompactString>().unwrap();
        assert_eq!(s.len(), 12);
        let s: CompactString = "ABCDEFGHIZKLMNOPQRSTUVWXYZ12345678901234"
            .parse::<CompactString>()
            .unwrap();
        assert_eq!(s.len(), 40);
        let s: CompactString = "".parse::<CompactString>().unwrap();
        assert_eq!(s.len(), 0);
    }

    #[test]
    fn test_oversize_string() {
        let s: [char; 256] = ['k'; 256];
        let string = String::from_iter(s);
        assert_eq!(CompactString::try_new(&string).is_err(), true);
    }

    #[test]
    fn test_equal_to_str() {
        let s = CompactString::try_new("hello world!").unwrap();
        assert_eq!(s, "hello world!");
        assert_eq!("hello world!", s);
        assert_ne!(s, "foo");
        assert_ne!("foo", s);
    }

    #[test]
    fn test_equal_compact_string() {
        let s1 = CompactString::try_new("test").unwrap();
        let s2 = CompactString::try_new("test").unwrap();
        assert_eq!(s1, s1);
        assert_eq!(s1, s2);
        assert_eq!(s2, s1);
        let s3 = CompactString::try_new("foo").unwrap();
        assert_ne!(s1, s3);
        assert_ne!(s3, s1);
    }

    #[test]
    fn test_equal_to_string() {
        let s1 = CompactString::try_new("test").unwrap();
        let s2 = String::from("test");
        assert_eq!(s1, s2);
        assert_eq!(s2, s1);
    }

    #[test]
    fn test_ownership() {
        let s1 = CompactString::try_new("test").unwrap();
        let s2 = s1.clone();
        assert_eq!(s1, s2);
        drop(s1);
        assert_eq!(s2, "test");
    }

    #[test]
    fn test_serde() {
        let s = CompactString::try_new("Hello World").unwrap();
        let serialized = serde_json::to_string(&s).unwrap();
        assert_eq!(serialized, "\"Hello World\"");
        let deserialized: CompactString = serde_json::from_str(&serialized).unwrap();
        assert_eq!(deserialized, s);
    }

    #[test]
    fn test_hash() {
        let mut map = HashMap::new();
        let s1 = CompactString::try_new("test").unwrap();
        let s2 = CompactString::try_new("test").unwrap();
        map.insert(s1, 1);
        map.insert(s2, 2);
        assert_eq!(map.len(), 1);
    }

    #[test]
    fn test_mix_string_hash() {
        let s1 = CompactString::try_new("Test Hash").unwrap();
        let s2 = String::from("Test Hash");
        let hash_builder = RandomState::new();
        let hash1 = hash_builder.hash_one(s1);
        let hash2 = hash_builder.hash_one(s2);
        assert_eq!(hash1, hash2);
    }

    #[test]
    fn test_search_in_hashmap() {
        let mut map = HashMap::<CompactString, i32>::new();
        map.insert("aaa".parse::<CompactString>().unwrap(), 17);
        assert_eq!(
            17,
            *map.get(&"aaa".parse::<CompactString>().unwrap()).unwrap()
        );
    }

    #[test]
    fn test_search_in_hashmap_with_str() {
        let mut map = HashMap::<CompactString, i32>::new();
        map.insert("aaa".parse::<CompactString>().unwrap(), 17);
        assert_eq!(17, *map.get("aaa").unwrap());
    }

    #[test]
    fn test_debug() {
        let s = CompactString::try_new("test").unwrap();
        assert_eq!(format!("{:?}", s), "test");
    }

    #[test]
    fn test_asref() {
        let s = CompactString::try_new("test").unwrap();
        assert_eq!(s.as_ref(), "test");
    }

    #[test]
    fn test_deref() {
        let s = CompactString::try_new("test").unwrap();
        assert_eq!(&*s, "test");
    }

    #[test]
    fn test_edge_cases() {
        let s = CompactString::try_new("").unwrap();
        assert_eq!(s.len(), 0);
        assert_eq!(s.as_str(), "");
        assert_eq!(s.to_string(), "");
        assert_eq!(s, "");

        let ls = "123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345";
        let s = CompactString::try_new(ls).unwrap();
        assert_eq!(s.len(), 255);
        assert_eq!(s.as_str(), ls);
        assert_eq!(s.to_string(), ls);
        assert_eq!(&s, ls);
    }

    #[test]
    fn test_bytes_roundtrip() {
        let bytes = vec![240, 159, 166, 128, 240, 159, 146, 175];
        let compact = CompactString::from_utf8(bytes.clone()).unwrap();
        assert_eq!(compact.as_bytes(), &bytes);
    }

    #[test]
    fn fuzz_test() {
        let mut rng = rand::thread_rng();
        let mut bytes = vec![0; 255];
        for _ in 0..1000 {
            rng.fill_bytes(&mut bytes);
            let compact_str = CompactString::from_utf8(bytes.clone());
            let string = String::from_utf8(bytes.clone());

            match compact_str {
                Ok(compact) => assert_eq!(compact, string.unwrap()),
                Err(_) => assert!(string.is_err()),
            }
        }
    }

    #[test]
    fn test_error_type() {
        const INVALID_UTF8: &[u8] = b"\xC0\xAF";
        const INVALID_LENGTH_BYTES: &[u8] = &[b'0'; 256];

        let err = CompactString::from_utf8(INVALID_UTF8).unwrap_err();
        assert!(matches!(err, ParseCompactStringError::Utf8Error(_)));

        let err = CompactString::from_utf8(INVALID_LENGTH_BYTES).unwrap_err();
        assert_eq!(
            err,
            ParseCompactStringError::LengthError(CompactStringLengthError(256))
        );

        let invalid_string = "0".repeat(1000);
        let err = invalid_string.parse::<CompactString>().unwrap_err();
        assert_eq!(err, CompactStringLengthError(1000));
    }
}

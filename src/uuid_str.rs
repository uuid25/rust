#[cfg(not(feature = "std"))]
use core as std;
use std::{borrow, fmt, hash, ops, str};

/// Stack-allocated string that can be dereferenced as `str`.
///
/// This is a [`String`]-like type (but is immutable and stack-allocated) that can be handled
/// similarly to `String` through common traits such as `Display` and `Deref<Target = str>`.
#[derive(Copy, Clone, Eq, Ord, PartialOrd, Debug)]
pub struct UuidStr<const N: usize>([u8; N]);

impl<const N: usize> UuidStr<N> {
    /// Returns a string slice of the content.
    pub const fn as_str(&self) -> &str {
        debug_assert!(str::from_utf8(&self.0).is_ok());
        unsafe { str::from_utf8_unchecked(&self.0) }
    }

    /// Returns a lowercase copy of this value.
    pub const fn to_lower(self) -> Self {
        let mut buffer = self.0;
        let mut i = 0;
        while i < buffer.len() {
            buffer[i] = buffer[i].to_ascii_lowercase();
            i += 1;
        }
        Self(buffer)
    }

    /// Returns an uppercase copy of this value.
    pub const fn to_upper(self) -> Self {
        let mut buffer = self.0;
        let mut i = 0;
        while i < buffer.len() {
            buffer[i] = buffer[i].to_ascii_uppercase();
            i += 1;
        }
        Self(buffer)
    }

    pub(crate) const fn from_utf8(utf8_bytes: [u8; N]) -> Result<Self, str::Utf8Error> {
        match str::from_utf8(&utf8_bytes) {
            Ok(_) => Ok(Self(utf8_bytes)),
            Err(e) => Err(e),
        }
    }
}

impl<const N: usize> ops::Deref for UuidStr<N> {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        self.as_str()
    }
}

impl<const N: usize> fmt::Display for UuidStr<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self)
    }
}

impl<const N: usize> PartialEq for UuidStr<N> {
    fn eq(&self, other: &UuidStr<N>) -> bool {
        self.as_str().eq(other.as_str())
    }
}

impl<const N: usize> PartialEq<str> for UuidStr<N> {
    fn eq(&self, other: &str) -> bool {
        self.as_str().eq(other)
    }
}

impl<const N: usize> PartialEq<UuidStr<N>> for str {
    fn eq(&self, other: &UuidStr<N>) -> bool {
        other.eq(self)
    }
}

impl<const N: usize> PartialEq<&str> for UuidStr<N> {
    fn eq(&self, other: &&str) -> bool {
        self.as_str().eq(*other)
    }
}

impl<const N: usize> PartialEq<UuidStr<N>> for &str {
    fn eq(&self, other: &UuidStr<N>) -> bool {
        other.eq(self)
    }
}

impl<const N: usize> hash::Hash for UuidStr<N> {
    fn hash<H: hash::Hasher>(&self, hasher: &mut H) {
        self.as_str().hash(hasher)
    }
}

impl<const N: usize> borrow::Borrow<str> for UuidStr<N> {
    fn borrow(&self) -> &str {
        self.as_str()
    }
}

impl<const N: usize> AsRef<str> for UuidStr<N> {
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
mod std_ext {
    use super::UuidStr;

    impl<const N: usize> From<UuidStr<N>> for String {
        fn from(value: UuidStr<N>) -> Self {
            value.as_str().to_owned()
        }
    }

    impl<const N: usize> PartialEq<String> for UuidStr<N> {
        fn eq(&self, other: &String) -> bool {
            self.as_str().eq(other.as_str())
        }
    }

    impl<const N: usize> PartialEq<UuidStr<N>> for String {
        fn eq(&self, other: &UuidStr<N>) -> bool {
            other.eq(self)
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::UuidStr;

    /// Tests `PartialEq` implementations.
    #[test]
    fn eq() {
        let x = UuidStr::from_utf8(*b"hello").unwrap();

        assert_eq!(x, x);
        assert_eq!(&x, &x);
        assert_eq!(x, UuidStr::from_utf8(*b"hello").unwrap());
        assert_eq!(UuidStr::from_utf8(*b"hello").unwrap(), x);
        assert_eq!(&x, &UuidStr::from_utf8(*b"hello").unwrap());
        assert_eq!(&UuidStr::from_utf8(*b"hello").unwrap(), &x);

        assert_eq!(x, "hello");
        assert_eq!("hello", x);
        assert_eq!(&x, "hello");
        assert_eq!("hello", &x);
        assert_eq!(&x as &str, "hello");
        assert_eq!("hello", &x as &str);

        assert_ne!(x, UuidStr::from_utf8(*b"world").unwrap());
        assert_ne!(UuidStr::from_utf8(*b"world").unwrap(), x);
        assert_ne!(&x, &UuidStr::from_utf8(*b"world").unwrap());
        assert_ne!(&UuidStr::from_utf8(*b"world").unwrap(), &x);

        assert_ne!(x, "world");
        assert_ne!("world", x);
        assert_ne!(&x, "world");
        assert_ne!("world", &x);
        assert_ne!(&x as &str, "world");
        assert_ne!("world", &x as &str);

        #[cfg(feature = "std")]
        {
            assert_eq!(x, String::from("hello"));
            assert_eq!(String::from("hello"), x);

            assert_eq!(String::from(x), String::from("hello"));
            assert_eq!(String::from("hello"), String::from(x));

            assert_ne!(x, String::from("world"));
            assert_ne!(String::from("world"), x);

            assert_ne!(String::from(x), String::from("world"));
            assert_ne!(String::from("world"), String::from(x));

            assert_eq!(x.to_owned(), String::from("hello"));
            assert_eq!(x.to_string(), String::from("hello"));
        }
    }

    /// Tests `to_upper()` and `to_lower()` methods.
    #[test]
    fn to_upper_lower() {
        let x = UuidStr::from_utf8(*b"CamelCase_20").unwrap();
        assert_eq!(x.to_upper(), "CAMELCASE_20");
        assert_eq!(x.to_lower(), "camelcase_20");
    }

    /// Tests `Hash` and `Borrow` implementations using `HashSet`.
    #[cfg(feature = "std")]
    #[test]
    fn hash_borrow() {
        use std::collections::HashSet;

        let mut s = HashSet::new();
        s.insert(UuidStr::from_utf8(*b"crisis").unwrap());
        s.insert(UuidStr::from_utf8(*b"eating").unwrap());
        s.insert(UuidStr::from_utf8(*b"lucent").unwrap());

        assert!(s.contains("crisis"));
        assert!(s.contains("eating"));
        assert!(s.contains("lucent"));
        assert!(!s.contains("system"));
        assert!(!s.contains("unless"));
        assert!(!s.contains("yellow"));

        assert!(s.contains(&UuidStr::from_utf8(*b"crisis").unwrap()));
        assert!(s.contains(&UuidStr::from_utf8(*b"eating").unwrap()));
        assert!(s.contains(&UuidStr::from_utf8(*b"lucent").unwrap()));
        assert!(!s.contains(&UuidStr::from_utf8(*b"system").unwrap()));
        assert!(!s.contains(&UuidStr::from_utf8(*b"unless").unwrap()));
        assert!(!s.contains(&UuidStr::from_utf8(*b"yellow").unwrap()));
    }
}

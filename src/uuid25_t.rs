#[cfg(not(feature = "std"))]
use core as std;
use std::{array, borrow, fmt, hash, ops, str};

use crate::ParseError;
use fstr::FStr;
use util::{convert_base, decode_digit_chars};

/// Primary value type containing the Uuid25 representation of a UUID.
///
/// This type stores the 25-digit Base36 string representation in a stack-allocated byte array and
/// can be handled similarly to an immutable [`String`]-like type through common traits such as
/// `Display` and `Deref<Target = str>`.
///
/// # Examples
///
/// ```rust
/// use uuid25::Uuid25;
///
/// let x = Uuid25::parse("1c8f903b-42c8-4fbe-9c38-40c37de6f0b3")?;
/// assert_eq!(x, "1ovd57svlqb1pjqwdnzxh08mr");
/// assert_eq!(&x as &str, "1ovd57svlqb1pjqwdnzxh08mr"); // coerce to &str
/// assert_eq!(format!("{x}"), "1ovd57svlqb1pjqwdnzxh08mr"); // use Display trait
/// assert!(x.eq_ignore_ascii_case("1OVD57SVLQB1PJQWDNZXH08MR")); // call &str's method
/// # Ok::<(), uuid25::ParseError>(())
/// ```
#[derive(Copy, Clone, Eq, Ord, PartialOrd, Debug)]
pub struct Uuid25([u8; 25]);

impl Uuid25 {
    /// NIL UUID (`00000000-0000-0000-0000-000000000000`)
    pub const NIL: Self = Self::parse_unwrap("0000000000000000000000000");

    /// Creates an instance from an array of Base36 digit values.
    const fn try_from_digit_values(mut digit_values: [u8; 25]) -> Result<Self, ParseError> {
        const DIGITS: &[u8; 36] = b"0123456789abcdefghijklmnopqrstuvwxyz";
        const U128_MAX: &[u8; 25] = b"f5lxx1zz5pnorynqglhzmsp33"; // 2^128 - 1

        let mut i = 0;
        let mut maybe_too_large = true;
        while i < 25 {
            if digit_values[i] >= 36 {
                return Err(ParseError {
                    debug_message: "invalid digit value",
                });
            }
            digit_values[i] = DIGITS[digit_values[i] as usize];
            if maybe_too_large && digit_values[i] > U128_MAX[i] {
                return Err(ParseError {
                    debug_message: "128-bit overflow",
                });
            } else if digit_values[i] < U128_MAX[i] {
                maybe_too_large = false;
            }
            i += 1;
        }

        Ok(Self(digit_values))
    }

    /// Returns a string slice of the content.
    pub const fn as_str(&self) -> &str {
        debug_assert!(str::from_utf8(&self.0).is_ok());
        unsafe { str::from_utf8_unchecked(&self.0) }
    }

    /// Creates an instance from a 16-byte UUID binary representation.
    pub const fn from_bytes(uuid_bytes: [u8; 16]) -> Self {
        if let Ok(buffer) = convert_base::<25>(&uuid_bytes, 256, 36) {
            if let Ok(t) = Self::try_from_digit_values(buffer) {
                return t;
            }
        }
        unreachable!();
    }

    /// Converts this type into the 16-byte binary representation of a UUID.
    pub const fn to_bytes(self) -> [u8; 16] {
        if let Ok(src) = decode_digit_chars::<25>(self.as_str(), 36) {
            if let Ok(uuid_bytes) = convert_base(&src, 36, 256) {
                return uuid_bytes;
            }
        }
        unreachable!();
    }

    /// Creates an instance from a UUID string representation.
    ///
    /// This method accepts the following formats:
    ///
    /// - 25-digit Base36 Uuid25 format: `3ud3gtvgolimgu9lah6aie99o`
    /// - 32-digit hexadecimal format without hyphens: `40eb9860cf3e45e2a90eb82236ac806c`
    /// - 8-4-4-4-12 hyphenated format: `40eb9860-cf3e-45e2-a90e-b82236ac806c`
    /// - Hyphenated format with surrounding braces: `{40eb9860-cf3e-45e2-a90e-b82236ac806c}`
    /// - RFC 4122 URN format: `urn:uuid:40eb9860-cf3e-45e2-a90e-b82236ac806c`
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use uuid25::Uuid25;
    /// let x = "3ud3gtvgolimgu9lah6aie99o";
    /// assert_eq!(Uuid25::parse("3ud3gtvgolimgu9lah6aie99o")?, x);
    /// assert_eq!(Uuid25::parse("40eb9860cf3e45e2a90eb82236ac806c")?, x);
    /// assert_eq!(Uuid25::parse("40eb9860-cf3e-45e2-a90e-b82236ac806c")?, x);
    /// assert_eq!(Uuid25::parse("{40eb9860-cf3e-45e2-a90e-b82236ac806c}")?, x);
    /// assert_eq!(
    ///     Uuid25::parse("urn:uuid:40eb9860-cf3e-45e2-a90e-b82236ac806c")?,
    ///     x
    /// );
    /// # Ok::<(), uuid25::ParseError>(())
    /// ```
    pub const fn parse(uuid_string: &str) -> Result<Self, ParseError> {
        match uuid_string.len() {
            25 => Self::parse_uuid25(uuid_string),
            32 => Self::parse_hex(uuid_string),
            36 => Self::parse_hyphenated(uuid_string),
            38 => Self::parse_braced(uuid_string),
            45 => Self::parse_urn(uuid_string),
            _ => Err(ParseError {
                debug_message: "invalid length",
            }),
        }
    }

    /// A `const`-friendly equivalent of `Uuid25::parse(uuid_string).unwrap()`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use uuid25::Uuid25;
    /// const K: Uuid25 = Uuid25::parse_unwrap("da91f3ec-38ab-4dd7-abb6-93c902cc4877");
    /// assert_eq!(
    ///     K,
    ///     Uuid25::parse("da91f3ec-38ab-4dd7-abb6-93c902cc4877").unwrap()
    /// );
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the argument is not a valid UUID string representation.
    pub const fn parse_unwrap(uuid_string: &str) -> Self {
        match Self::parse(uuid_string) {
            Ok(t) => t,
            _ => panic!("could not parse a UUID string"),
        }
    }

    /// Creates an instance from the 25-digit Base36 Uuid25 format: `3ud3gtvgolimgu9lah6aie99o`.
    pub const fn parse_uuid25(uuid_string: &str) -> Result<Self, ParseError> {
        match decode_digit_chars::<25>(uuid_string, 36) {
            Err(debug_message) => Err(ParseError { debug_message }),
            Ok(buffer) => Self::try_from_digit_values(buffer),
        }
    }

    /// Creates an instance from the 32-digit hexadecimal format without hyphens:
    /// `40eb9860cf3e45e2a90eb82236ac806c`.
    pub const fn parse_hex(uuid_string: &str) -> Result<Self, ParseError> {
        match decode_digit_chars::<32>(uuid_string, 16) {
            Err(debug_message) => Err(ParseError { debug_message }),
            Ok(buffer) => match convert_base(&buffer, 16, 36) {
                Err(debug_message) => Err(ParseError { debug_message }),
                Ok(buffer) => Self::try_from_digit_values(buffer),
            },
        }
    }

    /// Creates an instance from the 8-4-4-4-12 hyphenated format:
    /// `40eb9860-cf3e-45e2-a90e-b82236ac806c`.
    pub const fn parse_hyphenated(uuid_string: &str) -> Result<Self, ParseError> {
        let src = uuid_string.as_bytes();
        if src.len() != 36
            || src[8] != b'-'
            || src[13] != b'-'
            || src[18] != b'-'
            || src[23] != b'-'
        {
            return Err(ParseError {
                debug_message: "invalid hyphenated format",
            });
        }

        let mut buffer = [0u8; 32];
        let (mut r, mut w) = (0, 0);
        while r < src.len() {
            if src[r] > 0x7f {
                return Err(ParseError {
                    debug_message: "non-ASCII digit",
                });
            }
            if r != 8 && r != 13 && r != 18 && r != 23 {
                buffer[w] = src[r];
                w += 1;
            }
            r += 1;
        }

        match str::from_utf8(&buffer) {
            Ok(t) => Self::parse_hex(t),
            _ => unreachable!(),
        }
    }

    /// Creates an instance from the hyphenated format with surrounding braces:
    /// `{40eb9860-cf3e-45e2-a90e-b82236ac806c}`.
    pub const fn parse_braced(uuid_string: &str) -> Result<Self, ParseError> {
        let src = uuid_string.as_bytes();
        if src.len() != 38 || src[0] != b'{' || src[37] != b'}' {
            return Err(ParseError {
                debug_message: "invalid braced format",
            });
        }

        let mut buffer = [0u8; 36];
        let (mut r, mut w) = (0, 0);
        while r < src.len() {
            if src[r] > 0x7f {
                return Err(ParseError {
                    debug_message: "non-ASCII digit",
                });
            }
            if r != 0 && r != 37 {
                buffer[w] = src[r];
                w += 1;
            }
            r += 1;
        }

        match str::from_utf8(&buffer) {
            Ok(t) => Self::parse_hyphenated(t),
            _ => unreachable!(),
        }
    }

    /// Creates an instance from the RFC 4122 URN format:
    /// `urn:uuid:40eb9860-cf3e-45e2-a90e-b82236ac806c`.
    pub const fn parse_urn(uuid_string: &str) -> Result<Self, ParseError> {
        let src = uuid_string.as_bytes();
        if src.len() != 45
            || (src[0] != b'U' && src[0] != b'u')
            || (src[1] != b'R' && src[1] != b'r')
            || (src[2] != b'N' && src[2] != b'n')
            || (src[3] != b':')
            || (src[4] != b'U' && src[4] != b'u')
            || (src[5] != b'U' && src[5] != b'u')
            || (src[6] != b'I' && src[6] != b'i')
            || (src[7] != b'D' && src[7] != b'd')
            || (src[8] != b':')
        {
            return Err(ParseError {
                debug_message: "invalid urn format",
            });
        }

        let mut buffer = [0u8; 36];
        let (mut r, mut w) = (0, 0);
        while r < src.len() {
            if src[r] > 0x7f {
                return Err(ParseError {
                    debug_message: "non-ASCII digit",
                });
            }
            if r > 8 {
                buffer[w] = src[r];
                w += 1;
            }
            r += 1;
        }

        match str::from_utf8(&buffer) {
            Ok(t) => Self::parse_hyphenated(t),
            _ => unreachable!(),
        }
    }

    /// Returns an uppercase copy of this value.
    ///
    /// This method returns a stack-allocated string-like type that can be handled like [`String`]
    /// through common traits.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use uuid25::Uuid25;
    /// let x = Uuid25::parse("3ud3gtvgolimgu9lah6aie99o")?;
    /// assert_eq!(x.to_upper(), "3UD3GTVGOLIMGU9LAH6AIE99O");
    /// # Ok::<(), uuid25::ParseError>(())
    /// ```
    pub const fn to_upper(self) -> FStr<25> {
        let mut buffer = self.0;
        let mut i = 0;
        while i < buffer.len() {
            buffer[i] = buffer[i].to_ascii_uppercase();
            i += 1;
        }

        match FStr::from_inner(buffer) {
            Ok(t) => t,
            _ => unreachable!(),
        }
    }

    /// Formats this type in the 32-digit hexadecimal format without hyphens:
    /// `40eb9860cf3e45e2a90eb82236ac806c`.
    ///
    /// This method returns a stack-allocated string-like type that can be handled like [`String`]
    /// through common traits.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use uuid25::Uuid25;
    /// let x = Uuid25::parse("3ud3gtvgolimgu9lah6aie99o")?;
    /// assert_eq!(x.to_hex(), "40eb9860cf3e45e2a90eb82236ac806c");
    /// # Ok::<(), uuid25::ParseError>(())
    /// ```
    pub const fn to_hex(self) -> FStr<32> {
        const DIGITS: &[u8; 16] = b"0123456789abcdef";

        let Ok(src) = decode_digit_chars::<25>(self.as_str(), 36) else {
            unreachable!();
        };
        let Ok(mut buffer) = convert_base(&src, 36, 16) else {
            unreachable!();
        };
        let mut i = 0;
        while i < 32 {
            buffer[i] = DIGITS[buffer[i] as usize];
            i += 1;
        }

        match FStr::from_inner(buffer) {
            Ok(t) => t,
            _ => unreachable!(),
        }
    }

    /// Formats this type in the 8-4-4-4-12 hyphenated format:
    /// `40eb9860-cf3e-45e2-a90e-b82236ac806c`.
    ///
    /// This method returns a stack-allocated string-like type that can be handled like [`String`]
    /// through common traits.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use uuid25::Uuid25;
    /// let x = Uuid25::parse("3ud3gtvgolimgu9lah6aie99o")?;
    /// assert_eq!(x.to_hyphenated(), "40eb9860-cf3e-45e2-a90e-b82236ac806c");
    /// # Ok::<(), uuid25::ParseError>(())
    /// ```
    pub const fn to_hyphenated(self) -> FStr<36> {
        let s = self.to_hex();
        let src = s.as_str().as_bytes();

        let mut buffer = [0u8; 36];
        let (mut r, mut w) = (0, 0);
        while w < buffer.len() {
            if w == 8 || w == 13 || w == 18 || w == 23 {
                buffer[w] = b'-';
            } else {
                buffer[w] = src[r];
                r += 1;
            }
            w += 1;
        }

        match FStr::from_inner(buffer) {
            Ok(t) => t,
            _ => unreachable!(),
        }
    }

    /// Formats this type in the hyphenated format with surrounding braces:
    /// `{40eb9860-cf3e-45e2-a90e-b82236ac806c}`.
    ///
    /// This method returns a stack-allocated string-like type that can be handled like [`String`]
    /// through common traits.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use uuid25::Uuid25;
    /// let x = Uuid25::parse("3ud3gtvgolimgu9lah6aie99o")?;
    /// assert_eq!(x.to_braced(), "{40eb9860-cf3e-45e2-a90e-b82236ac806c}");
    /// # Ok::<(), uuid25::ParseError>(())
    /// ```
    pub const fn to_braced(self) -> FStr<38> {
        let s = self.to_hyphenated();
        let src = s.as_str().as_bytes();

        let mut buffer = [0u8; 38];
        buffer[0] = b'{';
        let (mut r, mut w) = (0, 1);
        while w < buffer.len() - 1 {
            buffer[w] = src[r];
            r += 1;
            w += 1;
        }
        buffer[37] = b'}';

        match FStr::from_inner(buffer) {
            Ok(t) => t,
            _ => unreachable!(),
        }
    }

    /// Formats this type in the RFC 4122 URN format:
    /// `urn:uuid:40eb9860-cf3e-45e2-a90e-b82236ac806c`.
    ///
    /// This method returns a stack-allocated string-like type that can be handled like [`String`]
    /// through common traits.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use uuid25::Uuid25;
    /// let x = Uuid25::parse("3ud3gtvgolimgu9lah6aie99o")?;
    /// assert_eq!(x.to_urn(), "urn:uuid:40eb9860-cf3e-45e2-a90e-b82236ac806c");
    /// # Ok::<(), uuid25::ParseError>(())
    /// ```
    pub const fn to_urn(self) -> FStr<45> {
        let s = self.to_hyphenated();
        let src = s.as_str().as_bytes();

        let mut buffer = [0u8; 45];
        buffer[0] = b'u';
        buffer[1] = b'r';
        buffer[2] = b'n';
        buffer[3] = b':';
        buffer[4] = b'u';
        buffer[5] = b'u';
        buffer[6] = b'i';
        buffer[7] = b'd';
        buffer[8] = b':';
        let (mut r, mut w) = (0, 9);
        while w < buffer.len() {
            buffer[w] = src[r];
            r += 1;
            w += 1;
        }

        match FStr::from_inner(buffer) {
            Ok(t) => t,
            _ => unreachable!(),
        }
    }
}

impl Default for Uuid25 {
    fn default() -> Self {
        Self::NIL
    }
}

impl ops::Deref for Uuid25 {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        self.as_str()
    }
}

impl fmt::Display for Uuid25 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self)
    }
}

impl PartialEq for Uuid25 {
    fn eq(&self, other: &Uuid25) -> bool {
        self.as_str().eq(other.as_str())
    }
}

impl PartialEq<str> for Uuid25 {
    fn eq(&self, other: &str) -> bool {
        self.as_str().eq(other)
    }
}

impl PartialEq<Uuid25> for str {
    fn eq(&self, other: &Uuid25) -> bool {
        other.eq(self)
    }
}

impl PartialEq<&str> for Uuid25 {
    fn eq(&self, other: &&str) -> bool {
        self.as_str().eq(*other)
    }
}

impl PartialEq<Uuid25> for &str {
    fn eq(&self, other: &Uuid25) -> bool {
        other.eq(self)
    }
}

impl hash::Hash for Uuid25 {
    fn hash<H: hash::Hasher>(&self, hasher: &mut H) {
        self.as_str().hash(hasher)
    }
}

impl borrow::Borrow<str> for Uuid25 {
    fn borrow(&self) -> &str {
        self.as_str()
    }
}

impl AsRef<str> for Uuid25 {
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl From<Uuid25> for [u8; 16] {
    fn from(value: Uuid25) -> Self {
        value.to_bytes()
    }
}

impl From<[u8; 16]> for Uuid25 {
    fn from(value: [u8; 16]) -> Self {
        Self::from_bytes(value)
    }
}

impl TryFrom<&[u8]> for Uuid25 {
    type Error = array::TryFromSliceError;

    fn try_from(value: &[u8]) -> Result<Self, Self::Error> {
        <[u8; 16]>::try_from(value).map(Into::into)
    }
}

impl str::FromStr for Uuid25 {
    type Err = ParseError;

    /// Parses a string `s` to return a value of this type. See [`Uuid25::parse()`] for the
    /// supported formats.
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::parse(s)
    }
}

#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
mod std_ext {
    use super::{ParseError, Uuid25};

    impl From<Uuid25> for String {
        fn from(value: Uuid25) -> Self {
            value.as_str().to_owned()
        }
    }

    impl TryFrom<String> for Uuid25 {
        type Error = ParseError;

        fn try_from(s: String) -> Result<Self, Self::Error> {
            s.parse()
        }
    }

    impl PartialEq<String> for Uuid25 {
        fn eq(&self, other: &String) -> bool {
            self.as_str().eq(other.as_str())
        }
    }

    impl PartialEq<Uuid25> for String {
        fn eq(&self, other: &Uuid25) -> bool {
            other.eq(self)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Uuid25;
    use crate::test_cases::TEST_CASES;

    /// Tests `PartialEq` implementations.
    #[test]
    fn eq() {
        const A: &str = "1zxp64g50er0t3mxb1pdvt18k";
        const B: &str = "a5xna8fhjr1e0nz3cewxauo5l";

        let x = Uuid25::parse(A).unwrap();

        assert_eq!(x, x);
        assert_eq!(&x, &x);
        assert_eq!(x, Uuid25::parse(A).unwrap());
        assert_eq!(Uuid25::parse(A).unwrap(), x);
        assert_eq!(x, A.parse::<Uuid25>().unwrap());
        assert_eq!(A.parse::<Uuid25>().unwrap(), x);
        assert_eq!(&x, &Uuid25::parse(A).unwrap());
        assert_eq!(&Uuid25::parse(A).unwrap(), &x);

        assert_eq!(x, A);
        assert_eq!(A, x);
        assert_eq!(&x, A);
        assert_eq!(A, &x);
        assert_eq!(&x as &str, A);
        assert_eq!(A, &x as &str);

        assert_ne!(x, Uuid25::parse(B).unwrap());
        assert_ne!(Uuid25::parse(B).unwrap(), x);
        assert_ne!(x, B.parse::<Uuid25>().unwrap());
        assert_ne!(B.parse::<Uuid25>().unwrap(), x);
        assert_ne!(&x, &Uuid25::parse(B).unwrap());
        assert_ne!(&Uuid25::parse(B).unwrap(), &x);

        assert_ne!(x, B);
        assert_ne!(B, x);
        assert_ne!(&x, B);
        assert_ne!(B, &x);
        assert_ne!(&x as &str, B);
        assert_ne!(B, &x as &str);

        #[cfg(feature = "std")]
        {
            assert_eq!(x, String::from(A));
            assert_eq!(String::from(A), x);

            assert_eq!(x, Uuid25::try_from(String::from(A)).unwrap());
            assert_eq!(Uuid25::try_from(String::from(A)).unwrap(), x);

            assert_eq!(String::from(x), String::from(A));
            assert_eq!(String::from(A), String::from(x));

            assert_ne!(x, String::from(B));
            assert_ne!(String::from(B), x);

            assert_ne!(x, Uuid25::try_from(String::from(B)).unwrap());
            assert_ne!(Uuid25::try_from(String::from(B)).unwrap(), x);

            assert_ne!(String::from(x), String::from(B));
            assert_ne!(String::from(B), String::from(x));

            assert_eq!(x.to_owned(), String::from(A));
            assert_eq!(x.to_string(), String::from(A));
        }
    }

    /// Tests `Hash` and `Borrow` implementations using `HashSet`.
    #[cfg(feature = "std")]
    #[test]
    fn hash_borrow() {
        use std::collections::HashSet;

        const A: &str = "e56ib2nq5r4xc5s1m3ra7tgn5";
        const B: &str = "021dqro063u0taj7l442f625s";
        const C: &str = "39yf1dk3bobxkselkuibw01dv";
        const D: &str = "co6p485732iprk9ih1x208hvo";
        const E: &str = "bd5lnb5mncp14mpqhah063zi9";
        const F: &str = "7hoo4kemx18f7628fieegto0l";
        const G: &str = "375850bf-c24a-b932-09e8-bb3e5b3bd303"; // C == G

        let mut s = HashSet::new();
        s.insert(Uuid25::parse(A).unwrap());
        s.insert(Uuid25::parse(B).unwrap());
        s.insert(Uuid25::parse(C).unwrap());
        assert_eq!(s.len(), 3);

        assert!(s.contains(A));
        assert!(s.contains(B));
        assert!(s.contains(C));
        assert!(!s.contains(D));
        assert!(!s.contains(E));
        assert!(!s.contains(F));

        assert!(s.contains(&Uuid25::parse(A).unwrap()));
        assert!(s.contains(&Uuid25::parse(B).unwrap()));
        assert!(s.contains(&Uuid25::parse(C).unwrap()));
        assert!(!s.contains(&Uuid25::parse(D).unwrap()));
        assert!(!s.contains(&Uuid25::parse(E).unwrap()));
        assert!(!s.contains(&Uuid25::parse(F).unwrap()));

        assert!(!s.contains(G));
        assert!(s.contains(&Uuid25::parse(G).unwrap()));
    }

    /// Creates values from 128-bit random numbers and compares the textual encoding results with
    /// those from Rust's `u128` implementations.
    #[test]
    fn from_to_random_bytes() {
        use rand::RngCore;
        let mut buffer = [0u8; 16];
        for _ in 0..0xff {
            rand::rngs::OsRng.fill_bytes(&mut buffer);
            let x = Uuid25::from_bytes(buffer);

            assert!(x.is_ascii());
            assert_eq!(x.len(), 25);
            assert_eq!(
                Ok(u128::from_be_bytes(buffer)),
                u128::from_str_radix(&x, 36)
            );
            assert_eq!(
                Ok(u128::from_be_bytes(buffer)),
                u128::from_str_radix(&x.to_hex(), 16)
            );

            assert_eq!(x, Uuid25::from(buffer));
            assert_eq!(x, Uuid25::try_from(buffer.as_ref()).unwrap());
            assert_eq!(x.to_bytes(), buffer);
            assert_eq!(<[u8; 16]>::from(x), buffer);
        }
    }

    /// Tests conversions from/to byte arrays using manually prepared cases.
    #[test]
    fn from_to_prepared_bytes() {
        for e in TEST_CASES {
            let x = Uuid25::parse_unwrap(e.uuid25);
            assert_eq!(x, Uuid25::from_bytes(*e.bytes));
            assert_eq!(x, Uuid25::from(*e.bytes));
            assert_eq!(x, Uuid25::try_from(e.bytes as &[u8]).unwrap());

            assert_eq!(x.to_bytes(), *e.bytes);
            assert_eq!(<[u8; 16]>::from(x), *e.bytes);
        }
    }

    /// Examines parsing results against manually prepared cases.
    #[test]
    fn parse() {
        for e in TEST_CASES {
            let x = e.uuid25;
            assert_eq!(x, Uuid25::parse(e.uuid25).unwrap());
            assert_eq!(x, Uuid25::parse(e.hex).unwrap());
            assert_eq!(x, Uuid25::parse(e.hyphenated).unwrap());
            assert_eq!(x, Uuid25::parse(e.braced).unwrap());
            assert_eq!(x, Uuid25::parse(e.urn).unwrap());

            assert_eq!(x, e.uuid25.parse::<Uuid25>().unwrap());
            assert_eq!(x, e.hex.parse::<Uuid25>().unwrap());
            assert_eq!(x, e.hyphenated.parse::<Uuid25>().unwrap());
            assert_eq!(x, e.braced.parse::<Uuid25>().unwrap());
            assert_eq!(x, e.urn.parse::<Uuid25>().unwrap());

            assert_eq!(x, Uuid25::parse_uuid25(e.uuid25).unwrap());
            assert_eq!(x, Uuid25::parse_hex(e.hex).unwrap());
            assert_eq!(x, Uuid25::parse_hyphenated(e.hyphenated).unwrap());
            assert_eq!(x, Uuid25::parse_braced(e.braced).unwrap());
            assert_eq!(x, Uuid25::parse_urn(e.urn).unwrap());

            assert!(Uuid25::parse_uuid25(e.hex).is_err());
            assert!(Uuid25::parse_uuid25(e.hyphenated).is_err());
            assert!(Uuid25::parse_uuid25(e.braced).is_err());
            assert!(Uuid25::parse_uuid25(e.urn).is_err());

            assert!(Uuid25::parse_hex(e.uuid25).is_err());
            assert!(Uuid25::parse_hex(e.hyphenated).is_err());
            assert!(Uuid25::parse_hex(e.braced).is_err());
            assert!(Uuid25::parse_hex(e.urn).is_err());

            assert!(Uuid25::parse_hyphenated(e.uuid25).is_err());
            assert!(Uuid25::parse_hyphenated(e.hex).is_err());
            assert!(Uuid25::parse_hyphenated(e.braced).is_err());
            assert!(Uuid25::parse_hyphenated(e.urn).is_err());

            assert!(Uuid25::parse_braced(e.uuid25).is_err());
            assert!(Uuid25::parse_braced(e.hex).is_err());
            assert!(Uuid25::parse_braced(e.hyphenated).is_err());
            assert!(Uuid25::parse_braced(e.urn).is_err());

            assert!(Uuid25::parse_urn(e.uuid25).is_err());
            assert!(Uuid25::parse_urn(e.hex).is_err());
            assert!(Uuid25::parse_urn(e.hyphenated).is_err());
            assert!(Uuid25::parse_urn(e.braced).is_err());

            #[cfg(feature = "std")]
            {
                assert_eq!(x, Uuid25::parse(&e.uuid25.to_uppercase()).unwrap());
                assert_eq!(x, Uuid25::parse(&e.hex.to_uppercase()).unwrap());
                assert_eq!(x, Uuid25::parse(&e.hyphenated.to_uppercase()).unwrap());
                assert_eq!(x, Uuid25::parse(&e.braced.to_uppercase()).unwrap());
                assert_eq!(x, Uuid25::parse(&e.urn.to_uppercase()).unwrap());
            }
        }
    }

    /// Examines conversion-to results against manually prepared cases.
    #[test]
    fn to_other_formats() {
        for e in TEST_CASES {
            let x = Uuid25::parse_unwrap(e.uuid25);
            assert_eq!(x, e.uuid25);
            assert_eq!(x.to_hex(), e.hex);
            assert_eq!(x.to_hyphenated(), e.hyphenated);
            assert_eq!(x.to_braced(), e.braced);
            assert_eq!(x.to_urn(), e.urn);

            #[cfg(feature = "std")]
            assert_eq!(x.to_upper(), e.uuid25.to_uppercase());
        }
    }

    /// Tests if parsing methods return `Err` on invalid inputs.
    #[test]
    fn parse_err() {
        let cases = [
            "",
            "0",
            "f5lxx1zz5pnorynqglhzmsp34",
            "zzzzzzzzzzzzzzzzzzzzzzzzz",
            " 65xe2jcp3zjc704bvftqjzbiw",
            "65xe2jcp3zjc704bvftqjzbiw ",
            " 65xe2jcp3zjc704bvftqjzbiw ",
            "{65xe2jcp3zjc704bvftqjzbiw}",
            "-65xe2jcp3zjc704bvftqjzbiw",
            "65xe2jcp-3zjc704bvftqjzbiw",
            "5xe2jcp3zjc704bvftqjzbiw",
            " 82f1dd3c-de95-075b-93ff-a240f135f8fd",
            "82f1dd3c-de95-075b-93ff-a240f135f8fd ",
            " 82f1dd3c-de95-075b-93ff-a240f135f8fd ",
            "82f1dd3cd-e95-075b-93ff-a240f135f8fd",
            "82f1dd3c-de95075b-93ff-a240f135f8fd",
            "82f1dd3c-de95-075b93ff-a240-f135f8fd",
            "{8273b64c5ed0a88b10dad09a6a2b963c}",
            "urn:uuid:8273b64c5ed0a88b10dad09a6a2b963c",
        ];

        for e in cases {
            assert!(Uuid25::parse(e).is_err());
            assert!(e.parse::<Uuid25>().is_err());
            assert!(Uuid25::parse_uuid25(e).is_err());
            assert!(Uuid25::parse_hex(e).is_err());
            assert!(Uuid25::parse_hyphenated(e).is_err());
            assert!(Uuid25::parse_braced(e).is_err());
            assert!(Uuid25::parse_urn(e).is_err());
        }
    }
}

mod util {
    /// Converts a digit value array in `src_base` to that in `dst_base`.
    ///
    /// Returns `Err` if the resulting array does not fit into `const N`.
    ///
    /// # Panics
    ///
    /// Panics if:
    ///
    /// - `src_base` is not between 2 and 256, inclusive;
    /// - `dst_base` is not between 2 and 256, inclusive; or,
    /// - `src` contains any value not less than `src_base`.
    ///
    /// # Errors
    ///
    /// Returns an error message for debugging on failure.
    pub const fn convert_base<const N: usize>(
        src: &[u8],
        src_base: usize,
        dst_base: usize,
    ) -> Result<[u8; N], &'static str> {
        assert!(2 <= src_base && src_base <= 256, "invalid src_base");
        assert!(2 <= dst_base && dst_base <= 256, "invalid dst_base");
        let (word_len, word_base) = compute_word_size(src_base, dst_base);
        let mut dst = [0u8; N];

        if src.is_empty() {
            return Ok(dst);
        } else if N == 0 {
            return Err("too small dst");
        }

        let mut dst_used = N - 1; // storage to memorize range of `dst` filled

        // read `word_len` digits from `src` for each outer loop
        let mut pos_word_end = match src.len() % word_len {
            0 => word_len,
            rem => rem,
        };
        while pos_word_end <= src.len() {
            let mut carry = 0;
            let mut i = pos_word_end.saturating_sub(word_len);
            while i < pos_word_end {
                let e = src[i] as usize;
                assert!(e < src_base, "invalid src digit");
                carry = carry * src_base + e;
                i += 1;
            }

            // fill in `dst` from right to left, while carrying up prior result to left
            let mut j = N;
            while j > 0 {
                j -= 1;
                carry += dst[j] as usize * word_base;
                dst[j] = (carry % dst_base) as u8;
                carry /= dst_base;

                // break inner loop when `carry` and remaining `dst` digits are all zero
                if carry == 0 && j <= dst_used {
                    dst_used = j;
                    break;
                }
            }
            if carry > 0 {
                return Err("too small dst");
            }
            pos_word_end += word_len;
        }
        Ok(dst)
    }

    /// Determines the number of `src` digits to read for each outer loop.
    const fn compute_word_size(src_base: usize, dst_base: usize) -> (usize, usize) {
        debug_assert!(2 <= src_base && src_base <= 256, "invalid src_base");
        debug_assert!(2 <= dst_base && dst_base <= 256, "invalid dst_base");
        let mut word_len = 1;
        let mut word_base = src_base;
        if usize::MAX > 0xffff || src_base < 256 || dst_base < 256 {
            while word_base <= usize::MAX / (src_base * dst_base) {
                word_len += 1;
                word_base *= src_base;
            }
        }
        (word_len, word_base)
    }

    /// Converts from a string of digit characters to an array of digit values.
    ///
    /// # Panics
    ///
    /// Panics if `base` is not between 2 and 36.
    ///
    /// # Errors
    ///
    /// Returns an error message for debugging on failure.
    pub const fn decode_digit_chars<const N: usize>(
        digit_chars: &str,
        base: u8,
    ) -> Result<[u8; N], &'static str> {
        // O(1) map from ASCII code points to Base36 digit values
        const DECODE_MAP: [u8; 256] = [
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
            0x08, 0x09, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e,
            0x0f, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c,
            0x1d, 0x1e, 0x1f, 0x20, 0x21, 0x22, 0x23, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x0a,
            0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18,
            0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f, 0x20, 0x21, 0x22, 0x23, 0xff, 0xff, 0xff,
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0xff, 0xff, 0xff, 0xff,
        ];

        assert!(2 <= base && base <= 36);
        let utf8_bytes = digit_chars.as_bytes();
        if utf8_bytes.len() != N {
            return Err("invalid length");
        }

        let mut digit_values = [0u8; N];
        let mut i = 0;
        while i < N {
            digit_values[i] = DECODE_MAP[utf8_bytes[i] as usize];
            if digit_values[i] >= base {
                return Err("invalid digit character");
            }
            i += 1;
        }
        Ok(digit_values)
    }

    #[cfg(test)]
    mod tests {
        use super::convert_base;

        /// Runs small, manually prepared test cases on `convert_base()`.
        #[test]
        fn convert_base_quick_test() {
            let bytes = [
                1, 127, 239, 57, 194, 100, 27, 165, 106, 148, 131, 24, 136, 65, 224, 90,
            ];
            let base16 = [
                0, 1, 7, 15, 14, 15, 3, 9, 12, 2, 6, 4, 1, 11, 10, 5, 6, 10, 9, 4, 8, 3, 1, 8, 8,
                8, 4, 1, 14, 0, 5, 10,
            ];
            let base36 = [
                0, 3, 7, 2, 18, 19, 24, 19, 30, 33, 30, 17, 19, 28, 15, 20, 14, 27, 34, 18, 2, 22,
                27, 29, 22,
            ];

            assert_eq!(convert_base(&bytes, 256, 256), Ok(bytes));
            assert_eq!(convert_base(&bytes, 256, 16), Ok(base16));
            assert_eq!(convert_base(&bytes, 256, 36), Ok(base36));
            assert_eq!(convert_base(&base16, 16, 256), Ok(bytes));
            assert_eq!(convert_base(&base16, 16, 16), Ok(base16));
            assert_eq!(convert_base(&base16, 16, 36), Ok(base36));
            assert_eq!(convert_base(&base36, 36, 256), Ok(bytes));
            assert_eq!(convert_base(&base36, 36, 16), Ok(base16));
            assert_eq!(convert_base(&base36, 36, 36), Ok(base36));

            let x: [u8; 40] = convert_base(&bytes, 256, 36).unwrap();
            assert!(x[..15].iter().all(|e| *e == 0));
            assert_eq!(&x[15..], &base36);
        }
    }
}

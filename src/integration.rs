#[cfg(feature = "uuid")]
#[cfg_attr(docsrs, doc(cfg(feature = "uuid")))]
mod uuid_crate {
    use crate::Uuid25;

    impl From<Uuid25> for uuid::Uuid {
        fn from(value: Uuid25) -> Self {
            Self::from_bytes(value.to_bytes())
        }
    }

    impl From<uuid::Uuid> for Uuid25 {
        fn from(value: uuid::Uuid) -> Self {
            Self::from_bytes(*value.as_bytes())
        }
    }

    #[test]
    fn from_into() {
        use crate::test_cases::TEST_CASES;
        for e in TEST_CASES {
            let x = uuid::Uuid::parse_str(e.hyphenated).unwrap();
            let y = uuid::Uuid::from(Uuid25::parse(e.uuid25).unwrap());
            assert_eq!(x, y);
            assert_eq!(Uuid25::from(x), e.uuid25);

            #[cfg(feature = "std")]
            assert_eq!(x.to_string(), e.hyphenated);
        }
    }
}

#[cfg(feature = "bson")]
#[cfg_attr(docsrs, doc(cfg(feature = "bson")))]
mod bson_crate {
    use crate::Uuid25;

    impl From<Uuid25> for bson::Uuid {
        fn from(value: Uuid25) -> Self {
            Self::from_bytes(value.to_bytes())
        }
    }

    impl From<bson::Uuid> for Uuid25 {
        fn from(value: bson::Uuid) -> Self {
            Self::from_bytes(value.bytes())
        }
    }

    #[test]
    fn from_into() {
        use crate::test_cases::TEST_CASES;
        for e in TEST_CASES {
            let x = bson::Uuid::parse_str(e.hyphenated).unwrap();
            let y = bson::Uuid::from(Uuid25::parse(e.uuid25).unwrap());
            assert_eq!(x, y);
            assert_eq!(Uuid25::from(x), e.uuid25);

            #[cfg(feature = "std")]
            assert_eq!(x.to_string(), e.hyphenated);
        }
    }
}

#[cfg(feature = "uuid7")]
#[cfg_attr(docsrs, doc(cfg(feature = "uuid7")))]
mod uuid7_crate {
    use crate::Uuid25;

    impl From<Uuid25> for uuid7::Uuid {
        fn from(value: Uuid25) -> Self {
            Self::from(value.to_bytes())
        }
    }

    impl From<uuid7::Uuid> for Uuid25 {
        fn from(value: uuid7::Uuid) -> Self {
            Self::from_bytes(value.into())
        }
    }

    #[test]
    fn from_into() {
        use crate::test_cases::TEST_CASES;
        for e in TEST_CASES {
            let x = e.hyphenated.parse::<uuid7::Uuid>().unwrap();
            let y = uuid7::Uuid::from(Uuid25::parse(e.uuid25).unwrap());
            assert_eq!(x, y);
            assert_eq!(Uuid25::from(x), e.uuid25);

            #[cfg(feature = "std")]
            assert_eq!(x.to_string(), e.hyphenated);
        }
    }
}

#[cfg(feature = "serde")]
#[cfg_attr(docsrs, doc(cfg(feature = "serde")))]
mod serde_crate {
    #[cfg(not(feature = "std"))]
    use core as std;
    use std::{fmt, str};

    use crate::Uuid25;
    use serde::{de, Deserializer, Serializer};

    impl serde::Serialize for Uuid25 {
        fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
            serializer.serialize_str(self)
        }
    }

    impl<'de> serde::Deserialize<'de> for Uuid25 {
        fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
            deserializer.deserialize_str(VisitorImpl)
        }
    }

    struct VisitorImpl;

    impl<'de> de::Visitor<'de> for VisitorImpl {
        type Value = Uuid25;

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(formatter, "a UUID representation")
        }

        fn visit_str<E: de::Error>(self, value: &str) -> Result<Self::Value, E> {
            Self::Value::parse(value).map_err(de::Error::custom)
        }

        fn visit_bytes<E: de::Error>(self, value: &[u8]) -> Result<Self::Value, E> {
            match Self::Value::try_from(value) {
                Ok(t) => Ok(t),
                Err(err) => match str::from_utf8(value) {
                    Ok(str_value) => self.visit_str(str_value),
                    _ => Err(de::Error::custom(err)),
                },
            }
        }
    }

    #[test]
    fn ser_de() {
        use crate::test_cases::TEST_CASES;
        use serde_test::Token;

        for e in TEST_CASES {
            let x = Uuid25::parse_unwrap(e.uuid25);
            serde_test::assert_tokens(&x, &[Token::Str(e.uuid25)]);
            serde_test::assert_de_tokens(&x, &[Token::Str(e.hex)]);
            serde_test::assert_de_tokens(&x, &[Token::Str(e.hyphenated)]);
            serde_test::assert_de_tokens(&x, &[Token::Str(e.braced)]);
            serde_test::assert_de_tokens(&x, &[Token::Str(e.urn)]);
            serde_test::assert_de_tokens(&x, &[Token::Bytes(e.bytes)]);

            serde_test::assert_de_tokens(&x, &[Token::Bytes(e.uuid25.as_bytes())]);
            serde_test::assert_de_tokens(&x, &[Token::Bytes(e.hex.as_bytes())]);
            serde_test::assert_de_tokens(&x, &[Token::Bytes(e.hyphenated.as_bytes())]);
            serde_test::assert_de_tokens(&x, &[Token::Bytes(e.braced.as_bytes())]);
            serde_test::assert_de_tokens(&x, &[Token::Bytes(e.urn.as_bytes())]);
        }
    }
}

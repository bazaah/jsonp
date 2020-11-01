use {
    json::value::RawValue as RawJson,
    serde::{de::Deserializer as _, Deserialize},
    serde_json as json,
    std::iter::IntoIterator,
    visitor::{ArrayVisitor, MapVisitor},
};

mod to_raw;
mod visitor;

pub use to_raw::ToRaw;

/// Convenience function for using the common dot (`.`) delimited format for dereferencing
/// nested Json structures.
pub fn dotted<'de, 'j: 'de, J, T>(backing: &'j J, pointer: &str) -> Result<T, J::Error>
where
    J: ToRaw<'j> + ?Sized,
    T: Deserialize<'de>,
{
    with_pattern(backing, pointer, ".")
}

/// Dereference using the given pointer and pattern. The pointer is split into
/// segments using the pattern.
pub fn with_pattern<'de, 'j: 'de, J, T>(
    backing: &'j J,
    pointer: &str,
    pattern: &str,
) -> Result<T, J::Error>
where
    J: ToRaw<'j> + ?Sized,
    T: Deserialize<'de>,
{
    let json = backing.try_into_raw()?;
    let pointers = pointer.split(pattern).map(Pointer::from_str);

    inner(json, pointers).map_err(Into::into)
}

/// Dereference using the given iterable set of pointers.
pub fn with_pointer<'de, 'j: 'de, 'p, J, I, T>(backing: &'j J, pointers: I) -> Result<T, J::Error>
where
    J: ToRaw<'j> + ?Sized,
    I: IntoIterator<Item = Pointer<'p>>,
    T: Deserialize<'de>,
{
    let json = backing.try_into_raw()?;

    inner(json, pointers.into_iter()).map_err(Into::into)
}

/// Convenience wrapper around the library core functions for string slices,
/// removing some of the generic noise from function signatures.
#[derive(Debug, Clone)]
pub struct BackingStr<'a> {
    borrow: &'a str,
}

impl<'a> BackingStr<'a> {
    pub fn new(borrow: &'a str) -> Self {
        Self { borrow }
    }

    /// See the documentation of `dotted`
    pub fn dotted<'de, 'j: 'de, T>(&'j self, pointer: &str) -> Result<T, json::Error>
    where
        T: Deserialize<'de>,
    {
        dotted(self.borrow, pointer)
    }

    /// See the documentation of `with_pattern`.
    pub fn pattern<'de, 'j: 'de, T>(
        &'j self,
        pointer: &str,
        pattern: &str,
    ) -> Result<T, json::Error>
    where
        T: Deserialize<'de>,
    {
        with_pattern(self.borrow, pointer, pattern)
    }

    /// See the documentation for `with_pointer`
    pub fn pointer<'de, 'j: 'de, 'p, I, T>(&'j self, pointers: I) -> Result<T, json::Error>
    where
        I: IntoIterator<Item = Pointer<'p>>,
        T: Deserialize<'de>,
    {
        with_pointer(self.borrow, pointers)
    }
}

impl<'a> From<&'a str> for BackingStr<'a> {
    fn from(backing: &'a str) -> Self {
        Self::new(backing)
    }
}

/// Convenience wrapper around the library core functions for raw json,
/// removing some of the generic noise from function signatures.
#[derive(Debug, Clone)]
pub struct BackingJson<'a> {
    borrow: &'a RawJson,
}

impl<'a> BackingJson<'a> {
    pub fn new(borrow: &'a RawJson) -> Self {
        Self { borrow }
    }

    /// See the documentation of `dotted`
    pub fn dotted<'de, 'j: 'de, T>(&'j self, pointer: &str) -> Result<T, json::Error>
    where
        T: Deserialize<'de>,
    {
        dotted(self.borrow, pointer)
    }

    /// See the documentation of `with_pattern`.
    pub fn pattern<'de, 'j: 'de, T>(
        &'j self,
        pointer: &str,
        pattern: &str,
    ) -> Result<T, json::Error>
    where
        T: Deserialize<'de>,
    {
        with_pattern(self.borrow, pointer, pattern)
    }

    /// See the documentation for `with_pointer`
    pub fn pointer<'de, 'j: 'de, 'p, I, T>(&'j self, pointers: I) -> Result<T, json::Error>
    where
        I: IntoIterator<Item = Pointer<'p>>,
        T: Deserialize<'de>,
    {
        with_pointer(self.borrow, pointers)
    }
}

impl<'a> From<&'a RawJson> for BackingJson<'a> {
    fn from(backing: &'a RawJson) -> Self {
        Self::new(backing)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Pointer<'p> {
    inner: PKind<'p>,
}

/// Typed representation of pointer segments
#[derive(Debug, Clone, Copy)]
enum PKind<'k> {
    /// A map's key
    Key(&'k str),
    /// An index into an array
    Index(u64),
}

impl<'p> Pointer<'p> {
    /// Parse a pointer from a string slice, by attempting to convert it
    /// to a number, and if successful setting it as an array index, otherwise
    /// using it as a map key.
    ///
    /// If you keys which may be valid numbers, care should taken when using
    /// this method.
    pub fn from_str(s: &'p str) -> Self {
        use std::str::FromStr;

        if s.is_empty() {
            return Self {
                inner: PKind::Key(""),
            };
        }

        let inner = match u64::from_str(s).ok() {
            Some(n) => PKind::Index(n),
            None => PKind::Key(s),
        };

        Self { inner }
    }

    /// Generate a new map key pointer
    pub fn key(s: &'p str) -> Self {
        Self {
            inner: PKind::Key(s),
        }
    }

    /// Generate a new array index pointer
    pub fn index(idx: u64) -> Self {
        Self {
            inner: PKind::Index(idx),
        }
    }
}

// Crate workhorse, this function abuses Rust's reference guarantees
// to iteratively drill down a nested Json structure
fn inner<'de, 'a: 'de, 'p, I, T>(j: &'a RawJson, p: I) -> Result<T, json::Error>
where
    I: Iterator<Item = Pointer<'p>>,
    T: Deserialize<'de>,
{
    use json::Deserializer;
    let mut target = j;

    for ptr in p {
        let mut de = Deserializer::from_str(target.get());

        match ptr.inner {
            PKind::Key(k) => {
                let value = de.deserialize_map(MapVisitor::new(k))?;

                target = value;
            }
            PKind::Index(i) => {
                let value = de.deserialize_seq(ArrayVisitor::new(i))?;

                target = value;
            }
        }
    }

    serde_json::from_str(target.get()).map_err(Into::into)
}

#[cfg(test)]
#[allow(unused_imports)]
mod tests {
    use super::*;
    use pretty_assertions::{assert_eq, assert_ne};

    type Result = std::result::Result<(), Box<dyn std::error::Error>>;

    const NESTED: &str =
        r#"{"foo": {"bar": [0, "1", {"baz": "hello world!" }, "blitz", "fooey" ] } }"#;

    #[test]
    fn with_pointer_str() -> Result {
        let pointer = &[
            Pointer::key("foo"),
            Pointer::key("bar"),
            Pointer::index(2),
            Pointer::key("baz"),
        ];

        let output: &str = with_pointer(NESTED, pointer.into_iter().copied())?;

        assert_eq!(output, "hello world!");

        Ok(())
    }

    #[test]
    fn with_pointer_json() -> Result {
        let pointer = &[
            Pointer::key("foo"),
            Pointer::key("bar"),
            Pointer::index(2),
            Pointer::key("baz"),
        ];

        let json: &RawJson = serde_json::from_str(NESTED)?;

        let output: &str = with_pointer(json, pointer.into_iter().copied())?;

        assert_eq!(output, "hello world!");

        Ok(())
    }
}

use {
    json::value::RawValue as RawJson,
    serde::{de::Deserializer as _, Deserialize},
    serde_json as json,
    std::iter::IntoIterator,
    visitor::{ArrayVisitor, LazyVisitor, MapVisitor},
};

mod to_raw;
mod visitor;

pub use to_raw::ToRaw;

/// The heart of this library, this structure contains all of the base
/// functionality to dereference into borrowed Json structures.
///
/// While this struct does not implement Copy, it is extremely cheap to
/// clone and can be done liberally.
#[derive(Debug, Default, Clone)]
pub struct Pointer {
    mode: Mode,
}

impl Pointer {
    /// Instantiate a new pointer with the given mode
    pub fn new(mode: Mode) -> Self {
        Self { mode }
    }

    /// Convenience function for using the common dot (`.`) delimited format for dereferencing
    /// nested Json structures.
    pub fn dotted<'de, 'j: 'de, J, T>(&self, backing: &'j J, pointer: &str) -> Result<T, J::Error>
    where
        J: ToRaw<'j> + ?Sized,
        T: Deserialize<'de>,
    {
        self.with_pattern(backing, pointer, ".")
    }

    /// Dereference using the given pointer and pattern. The pointer is split into
    /// segments using the pattern. Starting the pointer with or without the pattern
    /// is equivalent, i.e: `with_pattern(..., ".foo", ".")` is equal to
    /// `with_pattern(..., "foo", ".")`.
    ///
    /// Attempting to pass in either an empty pointer or pattern will cause this function
    /// to short circuit any dereferencing and attempt deserialization from `backing`
    /// directly.
    pub fn with_pattern<'de, 'j: 'de, J, T>(
        &self,
        backing: &'j J,
        pointer: &str,
        pattern: &str,
    ) -> Result<T, J::Error>
    where
        J: ToRaw<'j> + ?Sized,
        T: Deserialize<'de>,
    {
        let json = backing.try_into_raw()?;

        // If the user attempts to pass any of the annoying edge cases around
        // pattern splitting into us, we'll simply short circuit any dereferencing
        // and attempt deserialization of the the entire backing object
        if pointer.is_empty() || pattern.is_empty() || pointer == pattern {
            return self.with_segments(json, None).map_err(Into::into);
        }

        // Allow users to not start a pointer with the given pattern
        // if they choose. This is special cased to allow for situations
        // where it would be annoying to require starting the pointer with a
        // pattern instance, e.g: pat = ", " ptr = "foo, bar, baz".
        if pointer.starts_with(pattern) {
            let pointers = pointer.split(pattern).skip(1).map(|s| self.segment(s));

            self.with_segments(json, pointers).map_err(Into::into)
        } else {
            let pointers = pointer.split(pattern).map(|s| self.segment(s));

            self.with_segments(json, pointers).map_err(Into::into)
        }
    }

    /// Dereference using the given iterable set of segments.
    pub fn with_segments<'de, 'j: 'de, 'p, J, I, T>(
        &self,
        backing: &'j J,
        segments: I,
    ) -> Result<T, J::Error>
    where
        J: ToRaw<'j> + ?Sized,
        I: IntoIterator<Item = Segment<'p>>,
        T: Deserialize<'de>,
    {
        let json = backing.try_into_raw()?;

        inner(json, segments.into_iter()).map_err(Into::into)
    }

    fn segment<'p>(&self, s: &'p str) -> Segment<'p> {
        match self.mode {
            Mode::Late => Segment::lazy(s),
            Mode::Early => Segment::early(s),
        }
    }
}

/// Convenience wrapper around the library core functions for string slices,
/// removing some of the generic noise from function signatures.
#[derive(Debug, Clone)]
pub struct BackingStr<'a> {
    p: Pointer,
    borrow: &'a str,
}

impl<'a> BackingStr<'a> {
    pub fn new(borrow: &'a str) -> Self {
        Self::with(borrow, Default::default())
    }

    pub fn with(borrow: &'a str, pointer: Pointer) -> Self {
        Self { p: pointer, borrow }
    }

    /// See the documentation of `Pointer::dotted`
    pub fn dotted<'de, 'j: 'de, T>(&'j self, pointer: &str) -> Result<T, json::Error>
    where
        T: Deserialize<'de>,
    {
        self.p.dotted(self.borrow, pointer)
    }

    /// See the documentation of `Pointer::with_pattern`.
    pub fn pattern<'de, 'j: 'de, T>(
        &'j self,
        pointer: &str,
        pattern: &str,
    ) -> Result<T, json::Error>
    where
        T: Deserialize<'de>,
    {
        self.p.with_pattern(self.borrow, pointer, pattern)
    }

    /// See the documentation for `Pointer::with_segments`
    pub fn pointer<'de, 'j: 'de, 'p, I, T>(&'j self, pointers: I) -> Result<T, json::Error>
    where
        I: IntoIterator<Item = Segment<'p>>,
        T: Deserialize<'de>,
    {
        self.p.with_segments(self.borrow, pointers)
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
    p: Pointer,
    borrow: &'a RawJson,
}

impl<'a> BackingJson<'a> {
    pub fn new(borrow: &'a RawJson) -> Self {
        Self::with(borrow, Default::default())
    }

    pub fn with(borrow: &'a RawJson, pointer: Pointer) -> Self {
        Self { p: pointer, borrow }
    }

    /// See the documentation of `Pointer::dotted`
    pub fn dotted<'de, 'j: 'de, T>(&'j self, pointer: &str) -> Result<T, json::Error>
    where
        T: Deserialize<'de>,
    {
        self.p.dotted(self.borrow, pointer)
    }

    /// See the documentation of `Pointer::with_pattern`.
    pub fn pattern<'de, 'j: 'de, T>(
        &'j self,
        pointer: &str,
        pattern: &str,
    ) -> Result<T, json::Error>
    where
        T: Deserialize<'de>,
    {
        self.p.with_pattern(self.borrow, pointer, pattern)
    }

    /// See the documentation for `Pointer::with_segments`
    pub fn pointer<'de, 'j: 'de, 'p, I, T>(&'j self, pointers: I) -> Result<T, json::Error>
    where
        I: IntoIterator<Item = Segment<'p>>,
        T: Deserialize<'de>,
    {
        self.p.with_segments(self.borrow, pointers)
    }
}

impl<'a> From<&'a RawJson> for BackingJson<'a> {
    fn from(backing: &'a RawJson) -> Self {
        Self::new(backing)
    }
}

/// Convenience wrapper around the library core functions for byte slices,
/// removing some of the generic noise from function signatures.
#[derive(Debug, Clone)]
pub struct BackingBytes<'a> {
    p: Pointer,
    borrow: &'a [u8],
}

impl<'a> BackingBytes<'a> {
    pub fn new(borrow: &'a [u8]) -> Self {
        Self::with(borrow, Default::default())
    }

    pub fn with(borrow: &'a [u8], pointer: Pointer) -> Self {
        Self { p: pointer, borrow }
    }

    /// See the documentation of `Pointer::dotted`
    pub fn dotted<'de, 'j: 'de, T>(&'j self, pointer: &str) -> Result<T, json::Error>
    where
        T: Deserialize<'de>,
    {
        self.p.dotted(self.borrow, pointer)
    }

    /// See the documentation of `Pointer::with_pattern`.
    pub fn pattern<'de, 'j: 'de, T>(
        &'j self,
        pointer: &str,
        pattern: &str,
    ) -> Result<T, json::Error>
    where
        T: Deserialize<'de>,
    {
        self.p.with_pattern(self.borrow, pointer, pattern)
    }

    /// See the documentation for `Pointer::with_segments`
    pub fn pointer<'de, 'j: 'de, 'p, I, T>(&'j self, pointers: I) -> Result<T, json::Error>
    where
        I: IntoIterator<Item = Segment<'p>>,
        T: Deserialize<'de>,
    {
        self.p.with_segments(self.borrow, pointers)
    }
}

impl<'a> From<&'a [u8]> for BackingBytes<'a> {
    fn from(backing: &'a [u8]) -> Self {
        Self::new(backing)
    }
}

/// Set the mode for interpreting pointer segments.
///
/// The default, Late lazily types each segment waiting until
/// deserialization to determine if the segment is a map key or
/// array index. Early parses each segment as soon as it's handled.
/// For more information, see `Segment`.
#[derive(Debug, Clone, Copy)]
pub enum Mode {
    Late,
    Early,
}

impl Default for Mode {
    fn default() -> Self {
        Self::Late
    }
}

/// Represents a segment of a pointer
#[derive(Debug, Clone, Copy)]
pub struct Segment<'p> {
    inner: PKind<'p>,
}

/// Typed representation of pointer segments
#[derive(Debug, Clone, Copy)]
enum PKind<'p> {
    /// Delayed segment typing
    Lazy(&'p str),
    /// A map's key
    Key(&'p str),
    /// An index into an array
    Index(u64),
}

impl<'p> Segment<'p> {
    /// Lazily type the pointer, delaying the declaration
    /// until called by the Json deserializer.
    ///
    /// Note this allows for processing of all valid Json
    /// map keys; however, using this type _can_ also deserialize
    /// Json arrays if the key is is parsable as a number.
    ///
    /// If you need strongly typed pointers see the `key` and
    /// `index` methods.
    pub fn lazy(s: &'p str) -> Self {
        Self {
            inner: PKind::Lazy(s),
        }
    }

    /// Parse a pointer from a string slice, by attempting to convert it
    /// to a number, and if successful setting it as an array index, otherwise
    /// using it as a map key.
    pub fn early(s: &'p str) -> Self {
        use std::str::FromStr;

        if s.is_empty() {
            return Self::key("");
        }

        let inner = match u64::from_str(s).ok() {
            Some(n) => PKind::Index(n),
            None => PKind::Key(s),
        };

        Self { inner }
    }

    /// Generate a new map key segment
    pub fn key(s: &'p str) -> Self {
        Self {
            inner: PKind::Key(s),
        }
    }

    /// Generate a new array index segment
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
    I: Iterator<Item = Segment<'p>>,
    T: Deserialize<'de>,
{
    use json::Deserializer;
    let mut target = j;

    for ptr in p {
        dbg!("in main loop");
        let mut de = Deserializer::from_str(target.get());

        match ptr.inner {
            PKind::Lazy(l) => {
                let value = de.deserialize_any(LazyVisitor::new(l))?;

                target = value;
            }
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
    fn with_segments_str() -> Result {
        let pointer = &[
            Segment::key("foo"),
            Segment::key("bar"),
            Segment::index(2),
            Segment::key("baz"),
        ];

        let output: &str =
            Pointer::default().with_segments(NESTED, pointer.into_iter().copied())?;

        assert_eq!(output, "hello world!");

        Ok(())
    }

    #[test]
    fn with_segments_json() -> Result {
        let pointer = &[
            Segment::key("foo"),
            Segment::key("bar"),
            Segment::index(2),
            Segment::key("baz"),
        ];

        let json: &RawJson = serde_json::from_str(NESTED)?;

        let output: &str = Pointer::default().with_segments(json, pointer.into_iter().copied())?;

        assert_eq!(output, "hello world!");

        Ok(())
    }

    #[test]
    fn with_pattern_str() -> Result {
        let output: &str = Pointer::default().with_pattern(NESTED, "foo, bar, 2, baz", ", ")?;

        assert_eq!(output, "hello world!");

        Ok(())
    }

    #[test]
    fn with_pattern_json() -> Result {
        let json: &RawJson = serde_json::from_str(NESTED)?;

        let output: &str = Pointer::default().with_pattern(json, "foo, bar, 2, baz", ", ")?;

        assert_eq!(output, "hello world!");

        Ok(())
    }

    #[test]
    fn with_pattern_empty() -> Result {
        let object: &RawJson = json::from_str(NESTED)?;
        let output: &RawJson = Pointer::default().with_pattern(NESTED, "", ", ")?;

        assert_eq!(output.to_string(), object.to_string());

        Ok(())
    }

    #[test]
    fn dotted_str() -> Result {
        let output: &str = Pointer::default().dotted(NESTED, "foo.bar.2.baz")?;

        assert_eq!(output, "hello world!");

        Ok(())
    }

    #[test]
    fn dotted_json() -> Result {
        let json: &RawJson = serde_json::from_str(NESTED)?;

        let output: &str = Pointer::default().dotted(json, "foo.bar.2.baz")?;

        assert_eq!(output, "hello world!");

        Ok(())
    }

    #[test]
    fn dotted_empty() -> Result {
        let object: &RawJson = json::from_str(NESTED)?;
        let output: &RawJson = Pointer::default().dotted(NESTED, "")?;

        assert_eq!(output.to_string(), object.to_string());

        Ok(())
    }
}

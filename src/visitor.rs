use {
    super::RawJson,
    serde::de::{Deserialize, Error, IgnoredAny, MapAccess, SeqAccess, Visitor},
    std::{fmt, str::FromStr},
};

/// Lazily attempts to parse a key / index only once requested by a
/// deserializer. This allows users to pass in "numeric" map key
/// pointer segments and have them deserialize as expected.
///
/// However, it does open the door to unexpected deserialization,
/// if the user was expecting a pointer segment to correspond to a
/// map with a numeric key and instead somehow got an array.
#[derive(Debug, Clone, Copy)]
pub(crate) struct LazyVisitor<'p> {
    k_or_idx: &'p str,
}

impl<'p> LazyVisitor<'p> {
    pub(crate) fn new(k_or_idx: &'p str) -> Self {
        Self { k_or_idx }
    }
}

impl<'de, 'p> Visitor<'de> for LazyVisitor<'p> {
    type Value = &'de RawJson;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        write!(
            formatter,
            "a map or array including the key or index: {}",
            self.k_or_idx
        )
    }

    fn visit_map<A>(self, map: A) -> Result<Self::Value, A::Error>
    where
        A: MapAccess<'de>,
    {
        internal_visit_map(self.k_or_idx, map)
    }

    fn visit_seq<A>(self, seq: A) -> Result<Self::Value, A::Error>
    where
        A: SeqAccess<'de>,
    {
        let index = u64::from_str(self.k_or_idx)
            .map_err(|_| Error::custom(format!("not an indexable number: {}", self.k_or_idx)))?;

        internal_visit_seq(index, seq)
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct MapVisitor<'p> {
    key: &'p str,
}

impl<'p> MapVisitor<'p> {
    pub(crate) fn new(key: &'p str) -> Self {
        Self { key }
    }
}

impl<'de, 'p> Visitor<'de> for MapVisitor<'p> {
    type Value = &'de RawJson;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        write!(formatter, "a map including the key: {}", self.key)
    }

    fn visit_map<A>(self, map: A) -> Result<Self::Value, A::Error>
    where
        A: MapAccess<'de>,
    {
        internal_visit_map(self.key, map)
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct ArrayVisitor {
    index: u64,
}

impl ArrayVisitor {
    pub(crate) fn new(index: u64) -> Self {
        Self { index }
    }
}

impl<'de> Visitor<'de> for ArrayVisitor {
    type Value = &'de RawJson;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        write!(formatter, "an array including the index: {}", self.index)
    }

    fn visit_seq<A>(self, seq: A) -> Result<Self::Value, A::Error>
    where
        A: SeqAccess<'de>,
    {
        internal_visit_seq(self.index, seq)
    }
}

fn internal_visit_map<'de, A, T>(target: &str, map: A) -> Result<T, A::Error>
where
    T: Deserialize<'de>,
    A: MapAccess<'de>,
{
    let mut map = map;
    let mut out = None;

    // Serde expects each call to next_key be followed by a
    // call to next_value before another call to next_key, however
    // we only want to spend effort deserializing if this is the
    // expected key, otherwise we forward to IgnoredAny.
    while let Some(k) = map.next_key::<&str>()? {
        match k == target {
            false => {
                map.next_value::<IgnoredAny>()?;
            }
            true => {
                out = Some(map.next_value()?);
                break;
            }
        }
    }

    // It is a logic error to not fully walk a given map, however we have
    // already found our value here so we ignore everything except potential
    // errors in the stream.
    while let Some((_k, _v)) = map.next_entry::<IgnoredAny, IgnoredAny>()? {}

    out.ok_or_else(|| Error::custom(format!("unable to locate a value with the key: {}", target)))
}

fn internal_visit_seq<'de, A, T>(target: u64, seq: A) -> Result<T, A::Error>
where
    T: Deserialize<'de>,
    A: SeqAccess<'de>,
{
    let mut seq = seq;
    let mut count = 0;

    // Ignore all elements before our target
    while count < target {
        if seq.next_element::<IgnoredAny>()?.is_none() {
            break;
        }
        count += 1;
    }

    let out = seq.next_element()?;

    // It is a logic error to not fully walk a given sequence, however we
    // have already found our value, so we ignore everything except potential
    // errors.
    while let Some(_val) = seq.next_element::<IgnoredAny>()? {}

    out.ok_or_else(|| {
        Error::custom(format!(
            "unable to locate a value with the index: {}",
            target
        ))
    })
}

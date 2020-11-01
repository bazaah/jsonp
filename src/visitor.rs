use {
    super::RawJson,
    serde::de::{Error, IgnoredAny, MapAccess, SeqAccess, Visitor},
    std::fmt,
};

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

    fn visit_map<A>(self, mut map: A) -> Result<Self::Value, A::Error>
    where
        A: MapAccess<'de>,
    {
        let mut out = None;

        while let Some((k, v)) = map.next_entry::<&str, &RawJson>()? {
            if k == self.key {
                out = Some(v);
                break;
            }
        }

        while let Some((_k, _v)) = map.next_entry::<IgnoredAny, IgnoredAny>()? {}

        out.ok_or_else(|| {
            Error::custom(format!(
                "unable to locate a value with the key: {}",
                self.key
            ))
        })
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

    fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
    where
        A: SeqAccess<'de>,
    {
        let mut count = 0;
        let mut out = None;

        while let Some(val) = seq.next_element()? {
            if count == self.index {
                out = Some(val);
                break;
            }
            count += 1;
        }

        while let Some(_val) = seq.next_element::<IgnoredAny>()? {}

        out.ok_or_else(|| {
            Error::custom(format!(
                "unable to locate a value with the index: {}",
                self.index
            ))
        })
    }
}

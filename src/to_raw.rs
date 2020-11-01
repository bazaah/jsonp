use {
    super::{json, RawJson},
    std::error::Error,
};

/// Glue trait allowing the crate's functions to
/// abstract over the exact layout of the borrowed
/// Json.
///
/// Can be potentially implemented by foreign types.
pub trait ToRaw<'j> {
    type Error: From<json::Error> + Error;

    fn try_into_raw(&'j self) -> Result<&'j RawJson, Self::Error>;
}

impl<'j> ToRaw<'j> for RawJson {
    type Error = json::Error;

    fn try_into_raw(&'j self) -> Result<&'j RawJson, Self::Error> {
        Ok(self)
    }
}

impl<'j> ToRaw<'j> for str {
    type Error = json::Error;

    fn try_into_raw(&'j self) -> Result<&'j RawJson, Self::Error> {
        json::from_str(self)
    }
}

impl<'j> ToRaw<'j> for [u8] {
    type Error = json::Error;

    fn try_into_raw(&'j self) -> Result<&'j RawJson, Self::Error> {
        json::from_slice(self)
    }
}

use {
    super::{json, RawJson},
    std::error::Error,
};

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

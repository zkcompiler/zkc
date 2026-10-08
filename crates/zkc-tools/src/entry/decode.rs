//! Exact carrier shapes over serde's derived field validation. A normal derive
//! also accepts positional arrays for records and object forms for unit enums.
//! Remote derives provide the field visitors; these wrappers select only the
//! JSON representation required by the carrier, including inside tagged enums.
use serde::{
    Deserializer,
    de::{MapAccess, Visitor, value::MapAccessDeserializer},
};
use std::{fmt, marker::PhantomData};

pub(super) trait Object<'de>: Sized {
    fn fields<D: Deserializer<'de>>(decoder: D) -> Result<Self, D::Error>;
}
pub(super) fn object<'de, D: Deserializer<'de>, T: Object<'de>>(decoder: D) -> Result<T, D::Error> {
    struct Map<T>(PhantomData<T>);
    impl<'de, T: Object<'de>> Visitor<'de> for Map<T> {
        type Value = T;
        fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("an object")
        }
        fn visit_map<A: MapAccess<'de>>(self, fields: A) -> Result<T, A::Error> {
            T::fields(MapAccessDeserializer::new(fields))
        }
    }
    decoder.deserialize_map(Map(PhantomData))
}
macro_rules! objects {
    ($($ty:ty),* $(,)?) => {$(
        impl<'de> $crate::entry::decode::Object<'de> for $ty {
            fn fields<D: serde::Deserializer<'de>>(decoder: D) -> Result<Self,D::Error> {
                Self::deserialize(decoder)
            }
        }
        impl<'de> serde::Deserialize<'de> for $ty {
            fn deserialize<D: serde::Deserializer<'de>>(decoder: D) -> Result<Self,D::Error> {
                $crate::entry::decode::object(decoder)
            }
        }
    )*};
}
macro_rules! names {
    ($($ty:ty),* $(,)?) => {$(
        impl<'de> serde::Deserialize<'de> for $ty {
            fn deserialize<D: serde::Deserializer<'de>>(decoder: D) -> Result<Self,D::Error> {
                let name = <String as serde::Deserialize>::deserialize(decoder)?;
                Self::deserialize(serde::de::value::StringDeserializer::<D::Error>::new(name))
            }
        }
    )*};
}
pub(super) use {names, objects};

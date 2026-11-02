//! Lookup indexes over the generated catalog and installation rows. Each index
//! is built once from the generated tables and states no fact of its own.

use super::{Identity, Type};
use std::{collections::BTreeMap, sync::OnceLock};
use zkc_catalog::{CATALOG, Codec, INSTALLATION};

type Key = (Type, Identity);

struct Index {
    logical_types: BTreeMap<Key, ()>,
    codecs: BTreeMap<Key, &'static Codec>,
    defaults: BTreeMap<Key, &'static str>,
}

fn key(kind: &str, domain: Option<zkc_catalog::DomainIdentity>) -> Key {
    let kind = Type::parse_kind(kind).expect("every installed row names a constructor");
    (kind, domain.map_or(Identity::None, Identity::from_catalog))
}

fn index() -> &'static Index {
    static INDEX: OnceLock<Index> = OnceLock::new();
    INDEX.get_or_init(|| Index {
        logical_types: CATALOG
            .logical_types
            .iter()
            .map(|row| (key(row.kind, row.domain), ()))
            .collect(),
        codecs: CATALOG
            .codecs
            .iter()
            .map(|row| (key(row.kind, row.domain), row))
            .collect(),
        defaults: INSTALLATION
            .representations
            .iter()
            .filter(|row| row.default)
            .map(|row| (key(row.kind, row.domain), row.identity))
            .collect(),
    })
}

/// An admitted instance of a nullary or unary nominal constructor.
pub(super) fn logical_type(kind: Type, identity: Identity) -> bool {
    index().logical_types.contains_key(&(kind, identity))
}

/// The installed codec of a nominal instance.
pub(super) fn codec(kind: Type, identity: Identity) -> Option<&'static Codec> {
    index().codecs.get(&(kind, identity)).copied()
}

/// The installation's default representation of a nominal instance.
pub(super) fn default_representation(kind: Type, identity: Identity) -> Option<&'static str> {
    index().defaults.get(&(kind, identity)).copied()
}

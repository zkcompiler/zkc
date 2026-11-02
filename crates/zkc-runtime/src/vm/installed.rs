//! Lookup indexes over the generated catalog and installation rows. Each index
//! is built once from the generated tables and states no fact of its own.

use super::{Identity, Type};
use std::{collections::BTreeMap, sync::OnceLock};
use zkc_catalog::{CATALOG, Codec, INSTALLATION, Representation, ValueFrame};

type Key = (Type, Identity);

struct Index {
    logical_types: BTreeMap<Key, ()>,
    codecs: BTreeMap<Key, &'static Codec>,
    defaults: BTreeMap<Key, &'static str>,
    representations: BTreeMap<(Key, &'static str), &'static Representation>,
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
        representations: INSTALLATION
            .representations
            .iter()
            .map(|row| ((key(row.kind, row.domain), row.identity), row))
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

/// Whether an instance's codec reads values held in this representation: the
/// instance's default, or a nondefault row whose value bytes are the codec's
/// frame. A nondefault local row, such as an alternative layout, is not read.
pub(super) fn codec_reads(kind: Type, identity: Identity, representation: &'static str) -> bool {
    index()
        .representations
        .get(&((kind, identity), representation))
        .is_some_and(|row| row.default || row.frame == ValueFrame::Canonical)
}

#[cfg(test)]
mod tests {
    use super::super::{PhysicalType, Representation};
    use zkc_catalog::{INSTALLATION, ValueFrame};

    #[test]
    fn serializable_representations_follow_the_installed_frame_rows() {
        let mut checked = 0;
        for row in INSTALLATION.representations {
            let kind = super::Type::parse_kind(row.kind).unwrap();
            if !kind.is_serializable() {
                continue;
            }
            let spelling = match row.domain {
                Some(domain) => format!("{}:{}@{}", row.kind, domain.name(), row.identity),
                None => format!("{}@{}", row.kind, row.identity),
            };
            let Ok(ty) = PhysicalType::parse(&spelling) else {
                // A provider contributes its resident representations.
                assert!(
                    Representation::BUILT_IN
                        .iter()
                        .all(|built_in| built_in.name() != row.identity),
                    "{spelling}"
                );
                continue;
            };
            assert_eq!(
                ty.is_serializable(),
                row.default || row.frame == ValueFrame::Canonical,
                "{spelling}"
            );
            checked += 1;
        }
        assert!(checked > 100);
        for (spelling, serializable) in [
            ("table:bls12-381.fr@arkworks.mle-lsb/0", true),
            ("table:bls12-381.fr@arkworks.mle-msb/0", false),
            ("vector:bls12-381.fr@arkworks.fr-diagonal/0", false),
            (
                "groups:ristretto255.group@dalek.ristretto-diagonal/0",
                false,
            ),
            ("polynomial:bls12-381.fr@arkworks.polynomial/0", true),
            ("round:koala-bear@plonky3.koala-bear-quadratic/0", true),
        ] {
            assert_eq!(
                PhysicalType::parse(spelling).unwrap().is_serializable(),
                serializable,
                "{spelling}"
            );
        }
    }
}

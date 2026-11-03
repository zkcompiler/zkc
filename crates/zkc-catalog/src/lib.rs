//! Generated declaration data, independent of MLIR, installation and execution.
//!
//! A catalog row describes a logical contract. It neither installs a backend nor
//! admits a source application, supplies a formal interpretation, or permits
//! moving a reached operation. Consumer profiles retain those responsibilities.

mod model;
pub use model::*;

include!(concat!(env!("OUT_DIR"), "/catalog.rs"));

/// Look up exact nominal identity; array position has no semantic authority.
pub fn operation(name: &str) -> Option<&'static Operation> {
    CATALOG.operations.iter().find(|row| row.name == name)
}

pub fn constructor(name: &str) -> Option<&'static TypeConstructor> {
    CATALOG.types.iter().find(|row| row.name == name)
}

pub fn consumer_profile(name: &str) -> Option<&'static ConsumerProfile> {
    CATALOG
        .consumer_profiles
        .iter()
        .find(|row| row.name == name)
}

/// Query a fixed owner-selected profile. Actual arguments, domain capabilities,
/// implementation selection and invocation parameters require separate checks.
pub fn consumer_profile_operation(
    profile: &str,
    operation: &str,
) -> Option<&'static ConsumerProfileOperation> {
    consumer_profile(profile)?
        .operations
        .iter()
        .find(|row| row.operation == operation)
}

/// The installed row of a domain identity.
pub fn installed_domain(identity: DomainIdentity) -> &'static InstalledDomain {
    CATALOG
        .domains
        .iter()
        .find(|row| row.identity == identity)
        .expect("every domain identity has its installed row")
}

/// Look up an installed codec by its exact identity.
pub fn installed_codec(identity: &str) -> Option<&'static Codec> {
    CATALOG.codecs.iter().find(|row| row.identity == identity)
}

const fn same(left: &str, right: &str) -> bool {
    let (left, right) = (left.as_bytes(), right.as_bytes());
    if left.len() != right.len() {
        return false;
    }
    let mut index = 0;
    while index < left.len() {
        if left[index] != right[index] {
            return false;
        }
        index += 1;
    }
    true
}

/// The value of a declared cross-language limit. A name without a `limits`
/// row fails const evaluation, so a constant derived from it cannot outlive
/// the row.
pub const fn limit(name: &str) -> u64 {
    let mut index = 0;
    while index < CATALOG.limits.len() {
        if same(CATALOG.limits[index].name, name) {
            return CATALOG.limits[index].value;
        }
        index += 1;
    }
    panic!("undeclared catalog limit")
}

/// The frame tag of an installed codec. A codec without a frame row fails
/// const evaluation.
pub const fn codec_tag(identity: &str) -> u8 {
    let mut index = 0;
    while index < CATALOG.codecs.len() {
        let row = &CATALOG.codecs[index];
        if same(row.identity, identity) {
            match row.frame {
                Some(frame) => return frame.tag,
                None => panic!("installed codec has no frame"),
            }
        }
        index += 1;
    }
    panic!("uninstalled codec")
}

/// The frame tag of the aggregate frame of `constructor` over `domain`. A pair
/// without an aggregate frame row fails const evaluation.
pub const fn aggregate_frame_tag(constructor: &str, domain: &str) -> u8 {
    let mut index = 0;
    while index < CATALOG.aggregate_frames.len() {
        let row = &CATALOG.aggregate_frames[index];
        if same(row.constructor, constructor)
            && match row.domain {
                Some(identity) => same(identity.name(), domain),
                None => domain.is_empty(),
            }
        {
            return row.tag;
        }
        index += 1;
    }
    panic!("undeclared aggregate frame")
}

/// The frame tag of the installed codec of a nominal instance. An instance
/// without a framed codec fails const evaluation.
pub const fn instance_tag(kind: &str, domain: Option<DomainIdentity>) -> u8 {
    let mut index = 0;
    while index < CATALOG.codecs.len() {
        let row = &CATALOG.codecs[index];
        let same_domain = match (row.domain, domain) {
            (Some(left), Some(right)) => same(left.name(), right.name()),
            (None, None) => true,
            _ => false,
        };
        if same(row.kind, kind) && same_domain {
            match row.frame {
                Some(frame) => return frame.tag,
                None => panic!("installed codec has no frame"),
            }
        }
        index += 1;
    }
    panic!("uninstalled codec")
}

//! Facts about canonical native source-interface leaves. This is a bounded
//! syntax/metadata checker, not a VM type, representation or installation model.
//! Structured logical-type exports have a different grammar and are never a
//! fallback here. Native consumers independently admit these same spellings.
use super::{InterfaceError as E, Result, require};
use serde_json::Value;
use sha2::{Digest, Sha256};
use zkc_catalog::{Kind, TypeConstructor};

#[derive(Debug)]
pub(in crate::entry) struct Leaf {
    pub head: &'static str,
    pub copy: bool,
    pub drop: bool,
    pub participants: bool,
    pub total: bool,
    pub constructible: bool,
    pub message: bool,
    pub needs_setup: bool,
    pub source_identity: Option<String>,
    pub alternatives: Vec<(String, Vec<String>)>,
}
impl Leaf {
    pub fn parse(spelling: &str, remaining: &mut usize) -> Result<Self> {
        parse(spelling, 0, remaining)
    }
    fn declaration(row: &'static TypeConstructor) -> Self {
        Self {
            head: row.name,
            copy: row.copy,
            drop: row.drop,
            participants: row.participants,
            total: row.native_local && row.mathematical,
            constructible: row.constructible,
            message: row.message,
            needs_setup: false,
            source_identity: None,
            alternatives: Vec::new(),
        }
    }
}
/// Leaf parsing draws on its caller's interface work allowance.
fn charge(remaining: &mut usize, amount: usize) -> Result<()> {
    *remaining = remaining.checked_sub(amount).ok_or(E::WorkLimit)?;
    Ok(())
}
fn parse(spelling: &str, depth: usize, remaining: &mut usize) -> Result<Leaf> {
    charge(remaining, 1)?;
    require(depth <= 8, E::Limit)?;
    if spelling.starts_with("variant:") {
        require(depth < 8, E::Limit)?;
        let tree = zkc_format::types::variant_tree(spelling).map_err(|_| E::Schema)?;
        return variant(&tree, depth, remaining);
    }
    require(spelling.len() <= 4096, E::Limit)?;
    if let Some((head, body)) = spelling.split_once('<') {
        require(
            depth < 8
                && !spelling
                    .bytes()
                    .any(|b| b.is_ascii_whitespace() || b == b'@'),
            E::Schema,
        )?;
        // A structural constructor has a Type or Nat parameter.
        let row = zkc_catalog::constructor(head)
            .filter(|row| {
                row.parameters
                    .iter()
                    .any(|parameter| matches!(parameter, Kind::Type | Kind::Nat))
            })
            .ok_or(E::Schema)?;
        let body = body.strip_suffix('>').ok_or(E::Schema)?;
        let mut parts = Vec::new();
        let (mut start, mut nesting) = (0, 0usize);
        for (i, byte) in body.bytes().enumerate() {
            match byte {
                b'<' => {
                    nesting += 1;
                    require(depth + nesting < 8, E::Limit)?;
                }
                b'>' => nesting = nesting.checked_sub(1).ok_or(E::Schema)?,
                b',' if nesting == 0 => {
                    parts.push(&body[start..i]);
                    start = i + 1;
                }
                _ => (),
            }
        }
        require(nesting == 0, E::Schema)?;
        parts.push(&body[start..]);
        require(parts.len() == row.parameters.len(), E::Schema)?;
        let mut leaf = Leaf::declaration(row);
        for (part, parameter) in parts.into_iter().zip(row.parameters) {
            match parameter {
                Kind::Type => {
                    let child = parse(part, depth + 1, remaining)?;
                    if head == "sequence" {
                        require(child.copy && child.drop, E::Schema)?;
                    }
                    leaf.copy &= child.copy;
                    leaf.drop &= child.drop;
                    leaf.constructible &= child.constructible;
                    leaf.needs_setup |= child.needs_setup;
                    if head == "sequence" {
                        leaf.participants = child.copy && child.participants;
                        leaf.total = child.copy && child.total;
                        leaf.message &= child.message;
                    }
                }
                Kind::Domain(sort) => {
                    charge(remaining, 1)?;
                    require(domain(sort, part), E::Schema)?;
                    // A frame over a domain needs the catalog's aggregate frame
                    // row; without it the type is valid local data.
                    leaf.message &= zkc_catalog::CATALOG.aggregate_frames.iter().any(|row| {
                        row.constructor == head && row.domain.map(|d| d.name()) == Some(part)
                    });
                }
                Kind::Nat => {
                    charge(remaining, 1)?;
                    require(
                        zkc_format::logical::natural_index(part).is_ok_and(|n| n <= 1_048_576),
                        E::Schema,
                    )?;
                }
            }
        }
        return Ok(leaf);
    }
    let (head, identity) = spelling.split_once(':').unwrap_or((spelling, ""));
    let row = zkc_catalog::constructor(head).ok_or(E::Schema)?;
    let mut leaf = Leaf::declaration(row);
    match row.parameters {
        [] => require(spelling == head, E::Schema)?,
        [Kind::Domain(sort)] => require(domain(sort, identity), E::Schema)?,
        _ => return Err(E::Schema),
    }
    // The native logical inventory has scalar pairing target groups but no
    // `groups` collection for them (Contracts/Domains.cpp). Logical oracle
    // rows and their Data association must both be formed total shared data.
    if head == "groups" && matches!(identity, "bn254.gt" | "bls12-381.gt") {
        leaf.total = false;
    }
    leaf.needs_setup =
        matches!(head, "prover_key" | "verifier_key") || identity == "multilinear.kzg.bls12-381/0";
    Ok(leaf)
}
fn variant(tree: &Value, depth: usize, remaining: &mut usize) -> Result<Leaf> {
    require(depth < 8, E::Limit)?;
    charge(remaining, 1)?;
    let pair = tree.as_array().filter(|a| a.len() == 2).ok_or(E::Schema)?;
    require(pair[0].as_str() != Some(""), E::Schema)?;
    let nominal = pair[0]
        .as_array()
        .filter(|a| a.len() == 2 && a[0] == "zkc.language");
    let source_identity = nominal.and_then(|a| {
        let key = crate::source_names::decode_nominal_identity(a[1].as_str()?, 256 * 1024)?;
        (!key.is_empty()).then(|| crate::io::bytes::hex(&Sha256::digest(key.as_bytes())))
    });
    let arms = pair[1]
        .as_array()
        .filter(|a| !a.is_empty() && a.len() <= 32)
        .ok_or(E::Schema)?;
    let mut leaf = Leaf {
        head: "variant",
        copy: true,
        drop: true,
        participants: true,
        total: true,
        constructible: true,
        message: true,
        needs_setup: false,
        source_identity,
        alternatives: Vec::new(),
    };
    let mut labels = std::collections::BTreeSet::new();
    for arm in arms {
        let pair = arm.as_array().filter(|a| a.len() == 2).ok_or(E::Schema)?;
        let label = pair[0].as_str().ok_or(E::Schema)?;
        require(native_name(label) && labels.insert(label), E::Schema)?;
        let children = pair[1]
            .as_array()
            .filter(|a| a.len() <= 128)
            .ok_or(E::Schema)?;
        let mut payload = Vec::new();
        for child in children {
            let (facts, spelling) = if let Some(spelling) = child.as_str() {
                require(
                    !spelling.starts_with("variant:") && !spelling.contains('@'),
                    E::Schema,
                )?;
                (parse(spelling, depth + 1, remaining)?, spelling.to_owned())
            } else {
                let spelling = zkc_format::types::variant_spelling(child).map_err(|_| E::Schema)?;
                (variant(child, depth + 1, remaining)?, spelling)
            };
            leaf.copy &= facts.copy;
            leaf.drop &= facts.drop;
            leaf.participants &= facts.copy && facts.participants;
            leaf.total &= facts.copy && facts.total;
            leaf.constructible &= facts.constructible;
            leaf.message &= facts.copy && facts.message;
            leaf.needs_setup |= facts.needs_setup;
            payload.push(spelling);
        }
        leaf.alternatives.push((label.to_owned(), payload));
    }
    Ok(leaf)
}

fn native_name(value: &str) -> bool {
    let bytes = value.as_bytes();
    !bytes.is_empty()
        && bytes.len() <= 128
        && (bytes[0].is_ascii_alphabetic() || bytes[0] == b'_')
        && bytes[1..]
            .iter()
            .all(|b| b.is_ascii_alphanumeric() || matches!(b, b'_' | b'-' | b'.'))
}

// Ground domain spellings in the native source carrier: the catalog's
// installed domains of the sort. These are declaration identities and sorts,
// not a promise that any CPU codec/provider is installed.
fn domain(sort: &str, identity: &str) -> bool {
    if sort == "Slot" {
        return !identity.is_empty()
            && identity.as_bytes()[0].is_ascii_alphabetic()
            && native_name(identity);
    }
    installed(identity).is_some_and(|row| row.sort == sort)
}
fn installed(identity: &str) -> Option<&'static zkc_catalog::InstalledDomain> {
    zkc_catalog::DomainIdentity::parse(identity).map(zkc_catalog::installed_domain)
}
/// Metadata profile only; native admission independently checks installation.
pub(super) fn block_transcript(suite: &str) -> bool {
    installed(suite).is_some_and(|row| {
        row.sort == "Transcript" && row.capabilities.contains(&"IndexBlockTranscript")
    })
}
/// The installed challenge field of a transcript suite.
pub(super) fn transcript_field(suite: &str) -> Option<&'static str> {
    let row = installed(suite).filter(|row| row.sort == "Transcript")?;
    row.members
        .iter()
        .find(|(member, _)| *member == "ChallengeField")
        .map(|(_, field)| field.name())
}
/// The installed field of a random service contract.
pub(super) fn service_field(contract: &str) -> Option<&'static str> {
    zkc_catalog::CATALOG
        .random_services
        .iter()
        .find(|row| row.contract == contract)
        .map(|row| row.field.name())
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn source_facts_come_from_declarations_without_installing_a_codec() {
        for spelling in [
            "bool",
            "field:koala-bear",
            "field_array<koala-bear,4>",
            "sequence<field:koala-bear>",
            "table:koala-bear",
        ] {
            let leaf = Leaf::parse(spelling, &mut 200_000).unwrap();
            assert!(leaf.copy && leaf.drop && leaf.constructible, "{spelling}");
        }
        let affine = Leaf::parse("resource_unit:Slot", &mut 200_000).unwrap();
        assert!(!affine.copy && affine.drop && !affine.constructible && !affine.message);
        let local = Leaf::parse("table:koala-bear", &mut 200_000).unwrap();
        assert!(!local.message && local.participants);
        let key = Leaf::parse("verifier_key:multilinear.kzg.bls12-381/0", &mut 200_000).unwrap();
        assert!(key.copy && key.drop && key.needs_setup && !key.participants);
    }

    #[test]
    fn domains_suites_and_services_are_the_installed_rows() {
        for row in zkc_catalog::CATALOG.domains {
            let name = row.identity.name();
            assert!(domain(row.sort, name), "{name}");
            let challenge = row
                .members
                .iter()
                .find(|(member, _)| *member == "ChallengeField")
                .map(|(_, field)| field.name());
            assert_eq!(transcript_field(name), challenge, "{name}");
            assert_eq!(
                block_transcript(name),
                row.capabilities.contains(&"IndexBlockTranscript"),
                "{name}"
            );
        }
        for row in zkc_catalog::CATALOG.random_services {
            assert_eq!(service_field(row.contract), Some(row.field.name()));
        }
        assert!(!domain("Field", "bn254.g1"));
        assert!(!domain("Field", "unknown"));
        assert_eq!(service_field("random.koala-bear/0"), None);
        assert_eq!(service_field("random.unknown/0"), None);
    }

    #[test]
    fn malformed_or_foreign_grammars_do_not_become_native_leaves() {
        for spelling in [
            "bool:",
            "field",
            "field:bn254.g1",
            "group:koala-bear",
            "field:unknown",
            "service:random.bls12-381.fr/0",
            "field<koala-bear>",
            "sequence<rng:bls12-381.fr>",
            "fixed_vector<bool,01>",
            "fixed_vector<bool,1048577>",
            "field_array<bn254.g1,2>",
            "sequence< bool>",
            "sequence<bool>@native",
            "variant:00",
            "unknown:bls12-381.fr",
            "[\"apply\",\"bool\",[]]",
        ] {
            assert!(Leaf::parse(spelling, &mut 200_000).is_err(), "{spelling}");
        }
        assert_eq!(Leaf::parse("bool", &mut 0).unwrap_err(), E::WorkLimit);
        let deep = "sequence<".repeat(9) + "bool" + &">".repeat(9);
        assert!(Leaf::parse(&deep, &mut 200_000).is_err());
    }

    #[test]
    fn variant_payloads_preserve_permissions_and_expanded_work_limits() {
        let tree = json!(["local", [["A", ["bool"]], ["B", ["resource_unit:Slot"]]]]);
        let spelling = zkc_format::types::variant_spelling(&tree).unwrap();
        let leaf = Leaf::parse(&spelling, &mut 200_000).unwrap();
        assert!(
            !leaf.copy && leaf.drop && !leaf.participants && !leaf.constructible && !leaf.message
        );
        assert_eq!(leaf.alternatives[1].1, ["resource_unit:Slot"]);
        assert_eq!(Leaf::parse(&spelling, &mut 1).unwrap_err(), E::WorkLimit);
        let duplicate =
            zkc_format::types::variant_spelling(&json!(["local", [["A", []], ["A", []]]])).unwrap();
        assert!(Leaf::parse(&duplicate, &mut 200_000).is_err());
    }
}

#[cfg(all(test, feature = "cpu"))]
mod parity;

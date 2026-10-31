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
            constructible: row.constructible,
            message: row.message,
            needs_setup: false,
            source_identity: None,
            alternatives: Vec::new(),
        }
    }
}
fn charge(remaining: &mut usize, amount: usize) -> Result<()> {
    *remaining = remaining.checked_sub(amount).ok_or(E::Limit)?;
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
        require(
            matches!(head, "sequence" | "field_array" | "fixed_vector"),
            E::Schema,
        )?;
        let row = zkc_catalog::constructor(head).ok_or(E::Schema)?;
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
                        leaf.message &= child.message;
                    }
                }
                Kind::Domain(sort) => {
                    charge(remaining, 1)?;
                    require(domain(sort, part), E::Schema)?;
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

// Ground domain spellings in the native source carrier. These are declaration
// identities and sorts, not a promise that any CPU codec/provider is installed.
fn domain(sort: &str, identity: &str) -> bool {
    match sort {
        "Field" => matches!(
            identity,
            "bn254.fr"
                | "bls12-381.fr"
                | "ristretto255.scalar"
                | "koala-bear"
                | "koala-bear.ext4-binomial3"
                | "koala-bear.ext8-binomial3"
                | "baby-bear"
                | "baby-bear.ext4-binomial11"
                | "goldilocks"
                | "goldilocks.ext2-binomial7"
                | "gf2-64.pentanomial-4-3-1"
                | "gf2-64.pentanomial-4-3-1.ext3-trinomial1"
        ),
        "Group" => matches!(
            identity,
            "bn254.g1"
                | "bn254.g2"
                | "bn254.gt"
                | "bls12-381.g1"
                | "bls12-381.g2"
                | "bls12-381.gt"
                | "ristretto255.group"
                | "edwards25519.prime"
        ),
        "Commitment" => {
            identity == "multilinear.kzg.bls12-381/0"
                || matches!(
                    identity,
                    "rows.merkle-keccak256.koala-bear/0"
                        | "rows.merkle-keccak256.koala-bear.ext8-binomial3/0"
                        | "rows.merkle-keccak256.koala-bear.ext4-binomial3/0"
                        | "rows.merkle-poseidon2-16.koala-bear/0"
                        | "rows.merkle-poseidon2-16.koala-bear.ext4-binomial3/0"
                        | "rows.merkle-poseidon2-16.baby-bear/0"
                        | "rows.merkle-poseidon2-16.baby-bear.ext4-binomial11/0"
                        | "rows.merkle-poseidon2-8.goldilocks/0"
                        | "rows.merkle-poseidon2-8.goldilocks.ext2-binomial7/0"
                )
        }
        "Transcript" => transcript_field(identity).is_some(),
        "Slot" => {
            !identity.is_empty()
                && identity.as_bytes()[0].is_ascii_alphabetic()
                && native_name(identity)
        }
        _ => false,
    }
}
pub(super) fn transcript_field(suite: &str) -> Option<&'static str> {
    match suite {
        "merlin3.bls12-381.fr64be/0"
        | "spongefish0.8.0.keccak.bls12-381.fr64be/0"
        | "hash-chain.keccak256.bls12-381.fr64be/0" => Some("bls12-381.fr"),
        "merlin3.ristretto255.scalar64le/0" => Some("ristretto255.scalar"),
        "merlin3.koala-bear.ext8-binomial3.rejection31le/0"
        | "hash-chain.keccak256.koala-bear.ext8-binomial3.rejection31le/0" => {
            Some("koala-bear.ext8-binomial3")
        }
        "hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0" => {
            Some("koala-bear.ext4-binomial3")
        }
        "merlin3.baby-bear.ext4-binomial11.rejection31le/0" => Some("baby-bear.ext4-binomial11"),
        "merlin3.goldilocks.ext2-binomial7.rejection64le/0" => Some("goldilocks.ext2-binomial7"),
        _ => None,
    }
}
pub(super) fn service_field(contract: &str) -> Option<&str> {
    let field = contract.strip_prefix("random.")?.strip_suffix("/0")?;
    matches!(
        field,
        "bn254.fr"
            | "bls12-381.fr"
            | "ristretto255.scalar"
            | "koala-bear.ext8-binomial3"
            | "koala-bear.ext4-binomial3"
            | "baby-bear.ext4-binomial11"
            | "goldilocks.ext2-binomial7"
    )
    .then_some(field)
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
        assert_eq!(Leaf::parse("bool", &mut 0).unwrap_err(), E::Limit);
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
        assert_eq!(Leaf::parse(&spelling, &mut 1).unwrap_err(), E::Limit);
        let duplicate =
            zkc_format::types::variant_spelling(&json!(["local", [["A", []], ["A", []]]])).unwrap();
        assert!(Leaf::parse(&duplicate, &mut 200_000).is_err());
    }
}

#[cfg(all(test, feature = "cpu"))]
mod parity;

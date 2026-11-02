//! The CPU backend's hand-written domain, transcript and codec tables against
//! the installed-instance and installation documents that the catalog build
//! projects into `CATALOG` and `INSTALLATION` (whose fidelity
//! `crates/zkc-catalog/tests/installed.rs` checks row for row). Every known
//! difference is listed with its reason: the consumer step that derives the
//! table from the catalog removes the entry. Any other difference, or a listed
//! one that no longer occurs, fails.
use serde_json::Value;
use std::collections::BTreeSet;
use zkc_cpu::domains::{INSTALLED, TRANSCRIPTS};
use zkc_runtime::vm::{Identity, Type};

fn declarations() -> Value {
    serde_json::from_str(include_str!("../../../common/catalog/declarations.json")).unwrap()
}
fn installation() -> Value {
    serde_json::from_str(include_str!("../../../common/catalog/installation.json")).unwrap()
}
fn rows<'a>(document: &'a Value, table: &str) -> &'a [Value] {
    document[table].as_array().unwrap()
}
fn domain<'a>(document: &'a Value, identity: &str) -> &'a Value {
    rows(document, "domains")
        .iter()
        .find(|row| row["identity"] == identity)
        .unwrap_or_else(|| panic!("{identity} is not installed"))
}
fn member<'a>(row: &'a Value, name: &str) -> Option<&'a str> {
    row["members"]
        .as_array()
        .unwrap()
        .iter()
        .find(|pair| pair[0] == name)
        .map(|pair| pair[1].as_str().unwrap())
}
fn default_provider<'a>(installed: &'a Value, identity: &str) -> &'a str {
    rows(installed, "providers")
        .iter()
        .find(|row| row["domain"] == identity)
        .map(|row| row["default"].as_str().unwrap())
        .unwrap_or_else(|| panic!("{identity} has no provider row"))
}
fn default_representation<'a>(installed: &'a Value, kind: &str, identity: &str) -> Option<&'a str> {
    rows(installed, "representations")
        .iter()
        .find(|row| row["kind"] == kind && row["domain"] == identity && row["default"] == true)
        .map(|row| row["identity"].as_str().unwrap())
}
fn of_sort(document: &Value, sort: &str) -> BTreeSet<String> {
    rows(document, "domains")
        .iter()
        .filter(|row| row["sort"] == sort)
        .map(|row| row["identity"].as_str().unwrap().to_owned())
        .collect()
}

/// The listed differences must be exactly the found ones.
fn agree(comparison: &str, found: BTreeSet<String>, expected: &[(&str, &str)]) {
    let listed = expected
        .iter()
        .map(|(subject, _)| subject.to_string())
        .collect::<BTreeSet<_>>();
    assert_eq!(
        listed.len(),
        expected.len(),
        "{comparison}: duplicate listed difference"
    );
    let unexpected = found.difference(&listed).collect::<Vec<_>>();
    let resolved = listed.difference(&found).collect::<Vec<_>>();
    assert!(
        unexpected.is_empty() && resolved.is_empty(),
        "{comparison}: unexpected {unexpected:?}; no longer differs {resolved:?}"
    );
}

/// Every constructor head; the match makes a new one a compile error here.
fn kinds() -> Vec<Type> {
    use Type::*;
    let all = vec![
        Sequence,
        FieldArray,
        FixedVector,
        Variant,
        ResourceUnit,
        Index,
        Indices,
        Bytes,
        Shake128State,
        QuotientMatrix,
        Matrix,
        Vector,
        Polynomial,
        Field,
        Table,
        Point,
        Round,
        Bool,
        Rng,
        Commitment,
        Commitments,
        OpeningStates,
        Proof,
        ProverKey,
        VerifierKey,
        OpeningState,
        Group,
        Nonce,
        Transcript,
        Groups,
    ];
    for ty in &all {
        match ty {
            Sequence | FieldArray | FixedVector | Variant | ResourceUnit | Index | Indices
            | Bytes | Shake128State | QuotientMatrix | Matrix | Vector | Polynomial | Field
            | Table | Point | Round | Bool | Rng | Commitment | Commitments | OpeningStates
            | Proof | ProverKey | VerifierKey | OpeningState | Group | Nonce | Transcript
            | Groups => {}
        }
    }
    all
}

#[test]
fn installed_domains_cover_the_fields_and_groups_with_their_providers() {
    let declared = declarations();
    let installed = installation();
    let mut found = BTreeSet::new();
    let fields = INSTALLED
        .iter()
        .map(|row| row.field.name().to_owned())
        .collect::<BTreeSet<_>>();
    let groups = INSTALLED
        .iter()
        .filter_map(|row| row.group.map(|group| group.name().to_owned()))
        .collect::<BTreeSet<_>>();
    for missing in of_sort(&declared, "Field").symmetric_difference(&fields) {
        found.insert(format!("field {missing}"));
    }
    for missing in of_sort(&declared, "Group").symmetric_difference(&groups) {
        found.insert(format!("group {missing}"));
    }
    for row in INSTALLED {
        let field = row.field.name();
        if row.provider != default_provider(&installed, field) {
            found.insert(format!("provider {field}"));
        }
        if let Some(group) = row.group {
            let group = group.name();
            if member(domain(&declared, group), "Scalar") != Some(field) {
                found.insert(format!("scalar {group}"));
            }
            if row.provider != default_provider(&installed, group) {
                found.insert(format!("provider {group}"));
            }
        }
    }
    agree("installed domains", found, &[]);
}

#[test]
fn installed_domain_defaults_are_the_default_representations() {
    let installed = installation();
    let mut found = BTreeSet::new();
    for row in INSTALLED {
        for kind in kinds() {
            let Some(physical) = row.physical(kind) else {
                continue;
            };
            let identity = physical.logical().identity();
            let expected = default_representation(&installed, kind.name(), identity.name());
            if Some(physical.representation().name()) != expected {
                found.insert(format!("{} {}", kind.name(), identity.name()));
            }
        }
    }
    agree("installed domain defaults", found, &[]);
}

#[test]
fn transcripts_are_the_installed_suites() {
    let declared = declarations();
    let installed = installation();
    let mut found = BTreeSet::new();
    let suites = TRANSCRIPTS
        .iter()
        .map(|row| row.suite.name().to_owned())
        .collect::<BTreeSet<_>>();
    for missing in of_sort(&declared, "Transcript").symmetric_difference(&suites) {
        found.insert(format!("suite {missing}"));
    }
    for row in TRANSCRIPTS {
        let suite = row.suite.name();
        if member(domain(&declared, suite), "ChallengeField") != Some(row.domain.field.name()) {
            found.insert(format!("challenge field {suite}"));
        }
        if row.provider != default_provider(&installed, suite) {
            found.insert(format!("provider {suite}"));
        }
    }
    agree("transcripts", found, &[]);
}

#[test]
fn codec_formatter_spellings() {
    let declared = declarations();
    let codecs = rows(&declared, "codecs")
        .iter()
        .map(|row| row["identity"].as_str().unwrap().to_owned())
        .collect::<BTreeSet<_>>();
    let mut found = BTreeSet::new();
    let mut spellings = BTreeSet::new();
    for row in INSTALLED {
        for kind in kinds() {
            if let Some(spelling) = row.codec(kind) {
                if !codecs.contains(&spelling) {
                    found.insert(spelling.clone());
                }
                spellings.insert(spelling);
            }
        }
    }
    assert!(spellings.len() > found.len());
    // The formatter appends a field suffix to every kind, so the nullary
    // index, indices and bytes codecs come out as spellings that no codec row
    // declares. The consumer step that reads codec identities from the
    // catalog removes these entries.
    const PHANTOM: &str = "formatted for a field although the codec is nullary";
    let fields = [
        "bls12-381.fr",
        "ristretto255.scalar",
        "koala-bear",
        "koala-bear.ext8-binomial3",
        "koala-bear.ext4-binomial3",
        "baby-bear",
        "baby-bear.ext4-binomial11",
        "goldilocks",
        "goldilocks.ext2-binomial7",
        "gf2-64.pentanomial-4-3-1",
        "gf2-64.pentanomial-4-3-1.ext3-trinomial1",
        "bn254.fr",
    ];
    let phantoms = fields
        .iter()
        .flat_map(|field| {
            ["index", "indices", "bytes"]
                .into_iter()
                .map(move |kind| format!("zkcv.{kind}.{field}/0"))
        })
        .collect::<Vec<_>>();
    assert_eq!(phantoms.len(), 36);
    agree(
        "codec formatter",
        found,
        &phantoms
            .iter()
            .map(|spelling| (spelling.as_str(), PHANTOM))
            .collect::<Vec<_>>(),
    );
    for nullary in ["zkcv.index/0", "zkcv.indices/0", "zkcv.bytes/0"] {
        assert!(codecs.contains(nullary) && !spellings.contains(nullary));
    }
}

#[test]
fn identities_of_the_tables_parse() {
    for row in INSTALLED {
        assert_ne!(row.field, Identity::None);
    }
    for row in TRANSCRIPTS {
        assert_eq!(Identity::parse(row.suite.name()).ok(), Some(row.suite));
    }
}

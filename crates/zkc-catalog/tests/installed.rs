//! The generated installed-instance and installation tables carry every
//! authored row and fact in declared order, and domain identities are exact.
#[path = "../codegen/projection.rs"]
mod projection;

use serde_json::{Value, json};
use zkc_catalog::*;

fn source() -> Value {
    serde_json::from_str(include_str!("../../../common/catalog/declarations.json")).unwrap()
}
fn installation() -> Value {
    serde_json::from_str(include_str!("../../../common/catalog/installation.json")).unwrap()
}
fn domain(identity: Option<DomainIdentity>) -> &'static str {
    identity.map_or("", DomainIdentity::name)
}
fn scheme(scheme: CommitmentScheme) -> &'static str {
    match scheme {
        CommitmentScheme::Keccak256Rows => "keccak256Rows",
        CommitmentScheme::Poseidon2Rows => "poseidon2Rows",
        CommitmentScheme::MultilinearKzg => "multilinearKzg",
    }
}
fn lower(name: String) -> String {
    let mut chars = name.chars();
    chars
        .next()
        .map(|first| first.to_ascii_lowercase().to_string() + chars.as_str())
        .unwrap_or_default()
}

fn installed_domain_json(row: &InstalledDomain) -> Value {
    let mut value = json!({
        "identity": row.identity.name(),
        "sort": row.sort,
        "members": row.members.iter().map(|(m, i)| json!([m, i.name()])).collect::<Vec<_>>(),
        "capabilities": row.capabilities,
    });
    match row.facts {
        DomainFacts::None => {}
        DomainFacts::Field(facts) => {
            let structure = match facts.structure {
                FieldStructure::Prime => json!({"kind": "prime"}),
                FieldStructure::Extension {
                    over,
                    degree,
                    reduction,
                } => json!({
                    "kind": "extension",
                    "over": format!("{over:?}"),
                    "degree": degree,
                    "reduction": reduction.iter().map(|(e, c)| json!([e, c])).collect::<Vec<_>>(),
                }),
            };
            value["field"] = json!({
                "characteristic": facts.characteristic,
                "structure": structure,
                "twoAdic": facts.two_adic.map(|t| json!({
                    "convention": t.convention,
                    "maximalRoot": t.maximal_root,
                    "twoAdicity": t.two_adicity,
                    "ordering": "powers",
                })),
            });
        }
        DomainFacts::Transcript(facts) => {
            value["transcript"] = json!({
                "family": match facts.family {
                    TranscriptFamily::Merlin3 => "merlin3",
                    TranscriptFamily::Spongefish080 => "spongefish0.8.0",
                    TranscriptFamily::HashChain => "hash-chain",
                },
                "hash": facts.hash.map(|ByteHash::Keccak256| "keccak256"),
                "decoder": match facts.decoder {
                    ChallengeDecoder::Fr64Be => "fr64be",
                    ChallengeDecoder::Rejection31Le => "rejection31le",
                    ChallengeDecoder::Rejection64Le => "rejection64le",
                    ChallengeDecoder::Scalar64Le => "scalar64le",
                },
                "bindsSuite": facts.binds_suite,
            });
        }
        DomainFacts::Commitment(facts) => {
            value["commitment"] = match facts {
                CommitmentFacts::Keccak256Rows { digest_bytes } => {
                    json!({"scheme": "keccak256Rows", "digestBytes": digest_bytes})
                }
                CommitmentFacts::Poseidon2Rows {
                    permutation,
                    digest_bytes,
                    digest_word_bytes,
                } => json!({
                    "scheme": "poseidon2Rows",
                    "permutation": permutation,
                    "digestBytes": digest_bytes,
                    "digestWordBytes": digest_word_bytes,
                }),
                CommitmentFacts::MultilinearKzg => json!({"scheme": "multilinearKzg"}),
            };
        }
    }
    value
}

fn logical_json() -> Value {
    let c = &CATALOG;
    json!({
        "domains": c.domains.iter().map(installed_domain_json).collect::<Vec<_>>(),
        "logicalTypes": c.logical_types.iter().map(|t| json!({"kind": t.kind, "domain": domain(t.domain)})).collect::<Vec<_>>(),
        "frameTags": c.frame_tags.iter().map(|t| json!({
            "tag": t.tag,
            "layout": format!("{:?}", t.layout),
            "shared": t.shared.map(|s| json!({"kind": s.kind, "scheme": scheme(s.scheme)})),
        })).collect::<Vec<_>>(),
        "codecs": c.codecs.iter().map(|codec| {
            let frame = codec.frame.map(|f| {
                let mut frame = json!({"tag": f.tag});
                for (name, value) in [("elementBytes", f.element_bytes), ("bytes", f.bytes), ("bytesPerArity", f.bytes_per_arity)] {
                    if let Some(value) = value {
                        frame[name] = json!(value);
                    }
                }
                frame
            });
            json!({"identity": codec.identity, "kind": codec.kind, "domain": domain(codec.domain), "frame": frame})
        }).collect::<Vec<_>>(),
        "aggregateFrames": c.aggregate_frames.iter().map(|a| json!({"constructor": a.constructor, "domain": domain(a.domain), "tag": a.tag})).collect::<Vec<_>>(),
        "randomServices": c.random_services.iter().map(|s| json!({"contract": s.contract, "field": s.field.name()})).collect::<Vec<_>>(),
        "limits": c.limits.iter().map(|l| json!({
            "name": l.name, "value": l.value, "unit": lower(format!("{:?}", l.unit)),
            "owner": l.owner, "scope": l.scope, "phase": lower(format!("{:?}", l.phase)),
        })).collect::<Vec<_>>(),
        "finiteDefinitions": c.finite_definitions.iter().map(|f| json!({
            "identity": f.identity, "mode": lower(format!("{:?}", f.mode)),
            "operation": lower(format!("{:?}", f.operation)), "collection": f.collection, "filtered": f.filtered,
        })).collect::<Vec<_>>(),
        "domainConstructors": c.domain_constructors.iter().map(|d| json!({"identity": d.identity, "kind": format!("{:?}", d.kind), "axis": d.axis})).collect::<Vec<_>>(),
    })
}

fn pattern_json(pattern: &ArgumentPattern) -> Value {
    match pattern {
        ArgumentPattern::Any => json!(["any"]),
        ArgumentPattern::Domain(identity) => {
            json!(["domain", installed_domain(*identity).sort, identity.name()])
        }
        ArgumentPattern::Type(instance) => {
            let arguments = instance
                .domain
                .map(|d| vec![json!(["domain", installed_domain(d).sort, d.name()])])
                .unwrap_or_default();
            json!(["type", ["apply", instance.kind, arguments]])
        }
        ArgumentPattern::Naturals { minimum, maximum } => {
            json!(["natRange", minimum.to_string(), maximum.to_string()])
        }
    }
}

fn installation_json() -> Value {
    let i = &INSTALLATION;
    let frame = |frame: ValueFrame| lower(format!("{frame:?}"));
    json!({
        "format": "zkc.native-installation/0",
        "representations": i.representations.iter().map(|r| json!({
            "identity": r.identity, "kind": r.kind, "domain": domain(r.domain), "default": r.default,
            "layout": r.layout.unwrap_or(""), "frame": frame(r.frame), "unit": r.unit.name(),
        })).collect::<Vec<_>>(),
        "appliedRepresentations": i.applied_representations.iter().map(|r| json!({
            "constructor": r.constructor,
            "arguments": r.arguments.iter().map(pattern_json).collect::<Vec<_>>(),
            "identity": r.identity, "default": r.default,
            "child": r.child.map(|c| json!({"kind": c.kind, "domain": domain(c.domain), "representation": c.representation})),
            "frame": frame(r.frame), "provider": r.provider.map(|p| p.name()), "unit": r.unit.name(),
            "vectorPort": r.vector_port.map(|c| json!({"kind": c.kind, "domain": domain(c.domain), "representation": c.representation})),
        })).collect::<Vec<_>>(),
        "providers": i.providers.iter().map(|p| json!({
            "domain": p.domain.name(), "default": p.default.name(),
            "alternatives": p.alternatives.iter().map(|a| a.name()).collect::<Vec<_>>(),
        })).collect::<Vec<_>>(),
        "providerUnits": i.provider_units.iter().map(|u| json!({"provider": u.provider.name(), "unit": u.unit.name()})).collect::<Vec<_>>(),
        "fieldForms": i.field_forms.iter().map(|f| json!({
            "field": f.field.name(),
            "arithmetic": f.arithmetic.map(|a| json!({"form": "residue", "representation": a.representation})),
            "montgomery": f.montgomery.map(|m| json!({"wordBytes": m.word_bytes, "radixBits": m.radix_bits})),
            "byteEncoding": f.byte_encoding.map(|e| json!({"codec": e.codec, "order": "littleEndian"})),
        })).collect::<Vec<_>>(),
        "physicalArguments": i.physical_arguments.iter().map(|p| json!({"operation": p.operation})).collect::<Vec<_>>(),
    })
}

#[test]
fn logical_tables_carry_every_authored_row_in_order() {
    let authored = source();
    let generated = logical_json();
    for table in [
        "domains",
        "logicalTypes",
        "frameTags",
        "codecs",
        "aggregateFrames",
        "randomServices",
        "limits",
        "finiteDefinitions",
        "domainConstructors",
    ] {
        assert_eq!(generated[table], authored[table], "{table}");
    }
}

#[test]
fn installation_tables_carry_every_authored_row_in_order() {
    assert_eq!(installation_json(), installation());
}

#[test]
fn domain_identities_are_exact_declared_names() {
    let authored = source();
    let names = authored["domains"]
        .as_array()
        .unwrap()
        .iter()
        .map(|row| row["identity"].as_str().unwrap())
        .collect::<Vec<_>>();
    assert_eq!(
        DomainIdentity::ALL
            .iter()
            .map(|identity| identity.name())
            .collect::<Vec<_>>(),
        names
    );
    for identity in DomainIdentity::ALL {
        assert_eq!(DomainIdentity::parse(identity.name()), Some(*identity));
        assert_eq!(installed_domain(*identity).identity, *identity);
    }
    // No suffix, family or presentation spelling parses.
    for spelling in [
        "Bls12381Fr",
        "bls12-381.fr/0",
        "bls12-381",
        "zkcv.field.bls12-381.fr/0",
        "",
    ] {
        assert_eq!(DomainIdentity::parse(spelling), None, "{spelling}");
    }
    assert!(installed_codec("zkcv.field.koala-bear/0").is_some());
    assert!(installed_codec("zkcv.index.koala-bear/0").is_none());
}

#[test]
fn identities_with_one_presentation_refuse() {
    let mut declarations = source();
    let mut installed = installation();
    declarations["domains"]
        .as_array_mut()
        .unwrap()
        .push(json!({"identity": "bn254-gt", "sort": "Group",
                     "members": [["Scalar", "bn254.fr"]], "capabilities": ["Group", "ScalarAction"]}));
    installed["providers"]
        .as_array_mut()
        .unwrap()
        .push(json!({"domain": "bn254-gt", "default": "arkworks", "alternatives": []}));
    let error = projection::generate(
        &serde_json::to_vec(&declarations).unwrap(),
        &serde_json::to_vec(&installed).unwrap(),
    )
    .unwrap_err();
    assert!(
        error.contains(
            "domain identities bn254.gt and bn254-gt have the same Rust presentation Bn254Gt"
        ),
        "{error}"
    );
}

//! The generated conformance suites: golden vectors replayed against
//! the emitted endpoint, one emitter per endpoint frame, plus the
//! literal builders they share.

use crate::binding::{Binding, ImplKind, SpongeImpl};
use crate::doc::{Document, Endpoint};
use std::fmt::Write as _;

use super::vectors::{Cases, ProverCase, Vectors};
use super::REJECT_CLASSES;

/// Decimal text into little-endian 32-bit limbs, refusing overflow.
fn decimal_to_limbs(text: &str, limb_count: usize) -> Result<Vec<u32>, String> {
    if text.is_empty() || !text.chars().all(|c| c.is_ascii_digit()) {
        return Err(format!("'{text}' is not a decimal number"));
    }
    let mut limbs = vec![0u32; limb_count];
    for digit in text.chars() {
        let mut carry = digit.to_digit(10).unwrap() as u64;
        for limb in limbs.iter_mut() {
            let wide = *limb as u64 * 10 + carry;
            *limb = wide as u32;
            carry = wide >> 32;
        }
        if carry != 0 {
            return Err(format!("'{text}' does not fit {limb_count} 32-bit limbs"));
        }
    }
    Ok(limbs)
}

fn statement_literal(
    document: &Document,
    binding: &Binding,
    alias: &str,
    name: &str,
    statement: &[(String, String)],
) -> Result<String, String> {
    let mut fields = Vec::new();
    for (label, class) in &document.statement {
        let implementation = binding.class(class).unwrap().implementation;
        let text = statement
            .iter()
            .find(|(bound, _)| bound == label)
            .map(|(_, value)| value.as_str())
            .ok_or_else(|| format!("vector '{name}' has no statement value for '{label}'"))?;
        let literal = match implementation {
            ImplKind::ToyBe8 => {
                let limbs = decimal_to_limbs(text, 2)?;
                format!("{}u64", (limbs[1] as u64) << 32 | limbs[0] as u64)
            }
            ImplKind::P3Word => format!("{}u32", decimal_to_limbs(text, 1)?[0]),
            ImplKind::P3Ext4 | ImplKind::P3Digest8 => {
                let limbs = decimal_to_limbs(text, implementation.limbs())?;
                let words = limbs
                    .iter()
                    .map(|limb| format!("{limb}u32"))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("[{words}]")
            }
            ImplKind::BlsFrBe32 | ImplKind::BlsG1Be48 => {
                // The decimal statement value is the wire integer; the
                // typed constructor re-establishes canonicality.
                let limbs = decimal_to_limbs(text, implementation.limbs())?;
                let mut bytes = Vec::new();
                for limb in limbs.iter().rev() {
                    bytes.extend_from_slice(&limb.to_be_bytes());
                }
                let list = bytes
                    .iter()
                    .map(|byte| format!("0x{byte:02x}"))
                    .collect::<Vec<_>>()
                    .join(", ");
                let constructor = if implementation == ImplKind::BlsFrBe32 {
                    "fr_from_wire"
                } else {
                    "g1_from_wire"
                };
                format!(
                    "{alias}::zkc_rt::kzg::{constructor}(&[{list}])\n            .expect(\"a canonical statement wire value\")"
                )
            }
        };
        fields.push(format!("{label}: {literal}"));
    }
    Ok(format!("{alias}::Statement {{ {} }}", fields.join(", ")))
}

/// The borrowed kernels a generated suite pins before replaying a single
/// vector. A kernel that drifts derives different challenges or accepts
/// different proofs, and the vectors alone would not say which.
fn kernel_self_checks(document: &Document, binding: &Binding, alias: &str) -> String {
    let mut out = String::new();
    if binding.sponge_impl == SpongeImpl::P3LenpadDuplex {
        let _ = writeln!(
            out,
            "#[test]\nfn permutation_known_answer() {{\n    \
             {alias}::zkc_rt::p3::permutation_self_check();\n}}\n"
        );
    }
    let pairing = document.codecs.iter().any(|(class, _)| {
        matches!(
            binding.class(class).map(|bound| bound.implementation),
            Some(ImplKind::BlsFrBe32 | ImplKind::BlsG1Be48)
        )
    });
    if pairing {
        let _ = writeln!(
            out,
            "#[test]\nfn pairing_is_nondegenerate() {{\n    \
             {alias}::zkc_rt::kzg::pairing_self_check();\n}}\n"
        );
    }
    out
}

/// Lowercase-hex payload text to a Rust byte-slice literal.
fn hex_literal(name: &str, what: &str, hex: &str) -> Result<String, String> {
    if !hex.len().is_multiple_of(2)
        || !hex
            .chars()
            .all(|c| c.is_ascii_hexdigit() && !c.is_ascii_uppercase())
    {
        return Err(format!("vector '{name}' {what} is not lowercase hex"));
    }
    Ok((0..hex.len())
        .step_by(2)
        .map(|at| format!("0x{}", &hex[at..at + 2]))
        .collect::<Vec<_>>()
        .join(", "))
}

pub(crate) fn emit_conformance(
    document: &Document,
    binding: &Binding,
    vectors: &Vectors,
    crate_ident: &str,
) -> Result<String, String> {
    if vectors.artifact_id != document.artifact_id {
        return Err(format!(
            "the vectors file binds artifact {}, the document is {}; matching a sidecar to \
             the wrong artifact is exactly what the identity check refuses",
            vectors.artifact_id, document.artifact_id
        ));
    }
    let cases = match (&vectors.cases, document.endpoint) {
        (Cases::Verifier(cases), Endpoint::Verifier) => cases,
        (Cases::Prover(cases), Endpoint::ProverSkeleton) => {
            return emit_prover_conformance(
                document,
                binding,
                vectors.artifact_id.as_str(),
                cases,
                crate_ident,
            )
        }
        _ => {
            return Err(format!(
                "the vectors file describes the other endpoint; this document is \
                 '{}'",
                document.endpoint_name
            ))
        }
    };
    for case in cases {
        let admitted = case.expect == "accept" || REJECT_CLASSES.contains(&case.expect.as_str());
        if !admitted {
            return Err(format!(
                "vector '{}' expects '{}', which is not a verdict: the reject classes are {}",
                case.name,
                case.expect,
                REJECT_CLASSES.join(", ")
            ));
        }
    }
    if !cases.iter().any(|case| case.expect == "accept") {
        return Err(
            "the vectors file carries no accepting vector; a refusal battery without a \
             positive control asserts nothing"
                .into(),
        );
    }

    let mut out = String::new();
    out.push_str("// Generated conformance suite: the committed golden vectors, replayed\n");
    out.push_str("// against the emitted endpoint. The same vectors drive the reference\n");
    out.push_str("// executor (zkc-run --vectors), so equality here is the differential\n");
    out.push_str("// gate between the emitted program and the reference semantics.\n\n");
    let _ = writeln!(out, "use {crate_ident} as verifier;\n");

    out.push_str("// An empty challenge list on a non-accepting vector means the log is\n");
    out.push_str("// unchecked for that vector (the corpus convention for corrupted-wire\n");
    out.push_str("// cases, where the verdict is the claim); an accepting vector always\n");
    out.push_str("// carries its full log.\n");
    out.push_str("fn run(name: &str, statement: verifier::Statement, proof: &[u8], expect: &str, challenges: Option<&[&str]>) {\n");
    out.push_str("    let outcome = verifier::verify(&statement, proof);\n");
    out.push_str(
        "    assert_eq!(outcome.verdict.as_str(), expect, \"vector '{name}' verdict\");\n",
    );
    out.push_str("    if let Some(challenges) = challenges {\n");
    out.push_str("        let logged: Vec<&str> = outcome.challenges.iter().map(String::as_str).collect();\n");
    out.push_str("        assert_eq!(logged, challenges, \"vector '{name}' challenge log\");\n");
    out.push_str("    }\n");
    out.push_str("}\n\n");

    out.push_str(&kernel_self_checks(document, binding, "verifier"));

    let _ = writeln!(
        out,
        "#[test]\nfn vectors_bind_this_artifact() {{\n    assert_eq!(verifier::ARTIFACT_ID, \"{}\");\n}}\n",
        vectors.artifact_id
    );

    out.push_str("#[test]\nfn golden_vectors() {\n");
    for case in cases {
        let statement =
            statement_literal(document, binding, "verifier", &case.name, &case.statement)?;
        let bytes = hex_literal(&case.name, "proof", &case.proof_hex)?;
        let challenges = if case.challenges.is_empty() && case.expect != "accept" {
            "None".to_owned()
        } else {
            let entries = case
                .challenges
                .iter()
                .map(|entry| format!("{entry:?}"))
                .collect::<Vec<_>>()
                .join(", ");
            format!("Some(&[{entries}])")
        };
        let _ = writeln!(
            out,
            "    run(\n        {:?},\n        {statement},\n        &[{bytes}],\n        {:?},\n        {challenges},\n    );",
            case.name, case.expect
        );
    }
    out.push_str("}\n");
    Ok(out)
}

fn emit_prover_conformance(
    document: &Document,
    binding: &Binding,
    artifact_id: &str,
    cases: &[ProverCase],
    crate_ident: &str,
) -> Result<String, String> {
    if !cases.iter().any(|case| case.expect == "ok") {
        return Err(
            "the vectors file carries no producing vector; a refusal battery without a \
             positive control asserts nothing"
                .into(),
        );
    }

    let mut out = String::new();
    out.push_str("// Generated conformance suite: the committed golden vectors, replayed\n");
    out.push_str("// against the emitted endpoint. The same inputs drive the reference\n");
    out.push_str("// executor (zkc-run --prove), so byte equality here is the differential\n");
    out.push_str("// gate between the emitted program and the reference semantics — a\n");
    out.push_str("// stronger gate than any verdict comparison, since a prover's whole\n");
    out.push_str("// output is under test.\n\n");
    let _ = writeln!(out, "use {crate_ident} as prover;\n");

    // Each harness is written only when the corpus has a case for it;
    // an unused one would warn, and the emitted crates are warning-free.
    if cases.iter().any(|case| case.expect == "ok") {
        out.push_str("fn produce(name: &str, statement: prover::Statement, witness: prover::Witness, proof: &[u8], challenges: &[&str]) {\n");
        out.push_str("    let produced = match prover::prove(&statement, witness) {\n");
        out.push_str("        Ok(produced) => produced,\n");
        out.push_str("        Err(error) => panic!(\"vector '{name}': {error}\"),\n");
        out.push_str("    };\n");
        out.push_str("    assert_eq!(produced.proof, proof, \"vector '{name}' proof bytes\");\n");
        out.push_str("    let logged: Vec<&str> = produced.challenges.iter().map(String::as_str).collect();\n");
        out.push_str("    assert_eq!(logged, challenges, \"vector '{name}' challenge log\");\n");
        out.push_str("}\n\n");
    }

    if cases.iter().any(|case| case.expect != "ok") {
        out.push_str("// A refused run emits nothing: the gates that classify a refusal all\n");
        out.push_str("// run before the value they judge reaches the wire.\n");
        out.push_str("fn refuse(name: &str, statement: prover::Statement, witness: prover::Witness, kind: &str, label: &str, message: &str) {\n");
        out.push_str("    match prover::prove(&statement, witness) {\n");
        out.push_str(
            "        Ok(_) => panic!(\"vector '{name}': expected a refusal, got a proof\"),\n",
        );
        out.push_str("        Err(error) => {\n");
        out.push_str(
            "            assert_eq!(error.kind(), kind, \"vector '{name}' refusal kind\");\n",
        );
        out.push_str(
            "            assert_eq!(error.label(), label, \"vector '{name}' refusal label\");\n",
        );
        out.push_str("            assert_eq!(error.message(), message, \"vector '{name}' refusal message\");\n");
        out.push_str("        }\n");
        out.push_str("    }\n");
        out.push_str("}\n\n");
    }

    out.push_str(&kernel_self_checks(document, binding, "prover"));

    let _ = writeln!(
        out,
        "#[test]\nfn vectors_bind_this_artifact() {{\n    assert_eq!(prover::ARTIFACT_ID, \"{artifact_id}\");\n}}\n"
    );

    out.push_str("#[test]\nfn golden_vectors() {\n");
    for case in cases {
        let statement =
            statement_literal(document, binding, "prover", &case.name, &case.statement)?;
        let mut payloads = Vec::new();
        for (label, _) in &document.witness_labels {
            let hex = case
                .witness
                .iter()
                .find(|(bound, _)| bound == label)
                .map(|(_, hex)| hex.as_str())
                .ok_or_else(|| {
                    format!(
                        "vector '{}' has no witness payload for '{label}'",
                        case.name
                    )
                })?;
            // The hex boundary is the caller's, exactly as it is on the
            // reference executor's command line.
            let bytes = hex_literal(&case.name, "witness payload", hex)?;
            payloads.push(format!("{label}: prover::Payload::new(vec![{bytes}])"));
        }
        let witness = format!("prover::Witness {{ {} }}", payloads.join(", "));
        match case.expect.as_str() {
            "ok" => {
                let bytes = hex_literal(&case.name, "proof", &case.proof_hex)?;
                let challenges = case
                    .challenges
                    .iter()
                    .map(|entry| format!("{entry:?}"))
                    .collect::<Vec<_>>()
                    .join(", ");
                let _ = writeln!(
                    out,
                    "    produce(\n        {:?},\n        {statement},\n        {witness},\n        &[{bytes}],\n        &[{challenges}],\n    );",
                    case.name
                );
            }
            kind @ ("statement" | "fill") => {
                if !case.proof_hex.is_empty() || !case.challenges.is_empty() {
                    return Err(format!(
                        "vector '{}' expects a refusal but carries proof or challenge \
                         expectations; a refused run produces neither",
                        case.name
                    ));
                }
                if case.label.is_empty() || case.message.is_empty() {
                    return Err(format!(
                        "vector '{}' expects a refusal but does not say which ABI label it \
                         names or what it reports",
                        case.name
                    ));
                }
                let _ = writeln!(
                    out,
                    "    refuse(\n        {:?},\n        {statement},\n        {witness},\n        {kind:?},\n        {:?},\n        {:?},\n    );",
                    case.name, case.label, case.message
                );
            }
            other => {
                return Err(format!(
                    "vector '{}' expects '{other}', which is neither 'ok' nor a refusal kind",
                    case.name
                ))
            }
        }
    }
    out.push_str("}\n");
    Ok(out)
}

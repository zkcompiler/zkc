//! Crate-file assembly: everything the emitted crate is besides its
//! walked body — the feature set, `src/lib.rs` preamble and frame,
//! `Cargo.toml`, and `README.md`.

use crate::binding::Binding;
use crate::doc::{Document, Row};
use crate::rust;
use std::fmt::Write as _;

use super::walk::Used;

/// Assemble `src/lib.rs`, `Cargo.toml`, and `README.md` around the
/// walked body. Returned in that order.
pub(crate) fn assemble(
    document: &Document,
    binding: &Binding,
    rt_path: &str,
    crate_name: &str,
    prover: bool,
    used: Used,
    body: &str,
) -> (String, String, String) {
    // Features: the union over the implementations actually bound.
    let mut features: Vec<&str> = Vec::new();
    let add_feature = |feature: &'static str, features: &mut Vec<&str>| {
        if !features.contains(&feature) {
            features.push(feature);
        }
    };
    add_feature(binding.sponge_impl.feature(), &mut features);
    for (class, _) in &document.codecs {
        add_feature(
            binding.class(class).unwrap().implementation.feature(),
            &mut features,
        );
    }
    for row in &document.rows {
        if let Row::HoleCall { digest, .. } = row {
            add_feature(
                binding.hole(digest).unwrap().implementation.feature(),
                &mut features,
            );
        }
    }
    features.sort_unstable();

    // ---- src/lib.rs ----
    let mut lib = String::new();
    let _ = writeln!(
        lib,
        "//! A zkc-emitted {} endpoint.\n//!\n\
         //! Generated from the canonical OIR document whose identity is\n\
         //! baked below; the emitter recomputed that identity from the\n\
         //! document bytes before reading a single row. This crate is the\n\
         //! projection's residual program: the transcript order, proof\n\
         //! ABI, {}, and {} of one sealed protocol, specialized\n\
         //! against one supplier binding. Do not edit; re-emit.\n",
        if prover { "prover" } else { "verifier" },
        if prover { "fills" } else { "checks" },
        if prover { "emission" } else { "decision" },
    );
    if prover {
        lib.push_str("pub use zkc_rt::{self, Payload, Prove, ProveError};\n\n");
    } else {
        lib.push_str("pub use zkc_rt::{self, Outcome, RejectClass, Verdict};\n");
        lib.push_str("use zkc_rt::ProofCursor;\n\n");
    }
    let _ = writeln!(
        lib,
        "/// `SHA256(\"zkc/oir\\n\" ‖ document)` — the endpoint artifact."
    );
    let _ = writeln!(
        lib,
        "pub const ARTIFACT_ID: &str = \"{}\";",
        document.artifact_id
    );
    let _ = writeln!(
        lib,
        "/// The provenance-independent view (`zkc/oir-semantic`)."
    );
    let _ = writeln!(
        lib,
        "pub const SEMANTIC_ID: &str = \"{}\";",
        document.semantic_id
    );
    let _ = writeln!(lib, "/// The sealed protocol this endpoint projects.");
    let _ = writeln!(
        lib,
        "pub const SOURCE_PIR_ID: &str = {};",
        rust::literal(&document.source)
    );
    let _ = writeln!(lib, "/// The supplier binding and its file digest.");
    let _ = writeln!(
        lib,
        "pub const BINDING: &str = {};",
        rust::literal(&binding.name)
    );
    let _ = writeln!(
        lib,
        "pub const BINDING_DIGEST: &str = \"{}\";",
        binding.digest_of_file
    );
    let _ = writeln!(
        lib,
        "pub const EMITTER: &str = \"zkc-emit {}\";",
        env!("CARGO_PKG_VERSION")
    );
    if prover {
        lib.push_str("/// The verifier-local checks this endpoint delegates, as\n");
        lib.push_str("/// `[event position, discharge kind]`. Their schema, uniqueness,\n");
        lib.push_str("/// and discharge kinds were checked at emit time; that they\n");
        lib.push_str("/// exhaust the source obligations is authenticated only where the\n");
        lib.push_str("/// sealed protocol is also present, and is not claimed here.\n");
        let rows = document
            .counterparty
            .iter()
            .map(|(position, kind)| format!("({position}, {})", rust::literal(kind)))
            .collect::<Vec<_>>()
            .join(", ");
        let _ = writeln!(lib, "pub const COUNTERPARTY: &[(u64, &str)] = &[{rows}];");
    }
    lib.push('\n');
    if used.group_modulus || used.field_modulus {
        let algebra = binding.algebra.as_ref().unwrap();
        if used.group_modulus {
            let _ = writeln!(lib, "const GROUP_MODULUS: u64 = {};", algebra.group);
        }
        if used.field_modulus {
            let _ = writeln!(lib, "const FIELD_MODULUS: u64 = {};", algebra.field);
        }
        lib.push('\n');
    }

    lib.push_str("/// The public statement, typed and ordered as the endpoint ABI\n");
    lib.push_str("/// declares it; field names are the ABI labels, verbatim.\n");
    lib.push_str("/// Multi-limb values are little-endian 32-bit limbs.\n");
    lib.push_str("#[allow(non_snake_case)]\npub struct Statement {\n");
    for (label, class) in &document.statement {
        let ty = binding.class(class).unwrap().implementation.rust_type();
        let _ = writeln!(lib, "    pub {label}: {ty},");
    }
    lib.push_str("}\n\n");

    // Every local below is declared from what the walk recorded
    // emitting, never from a second reading of the rows: a body that
    // never squeezes, reads, writes, or names its statement gets a
    // local it can leave alone, and the emitted crate stays
    // warning-free without anyone predicting which rows do what.
    let statement_parameter = if used.statement {
        "statement"
    } else {
        "_statement"
    };
    if prover {
        lib.push_str("/// The opaque witness payloads, by their endpoint ABI labels.\n");
        lib.push_str("/// Every payload is named, so the reference executor's\n");
        lib.push_str("/// missing-payload refusal has no run-time form here; and every\n");
        lib.push_str("/// payload moves, so a handle cannot be spent twice.\n");
        lib.push_str("#[allow(non_snake_case)]\npub struct Witness {\n");
        for (label, class) in &document.witness_labels {
            let _ = writeln!(lib, "    /// Handle class `{}`.", rust::comment(class));
            let _ = writeln!(lib, "    pub {label}: Payload,");
        }
        lib.push_str("}\n\n");

        lib.push_str("/// One prover run: the emitted proof bytes and the ordered\n");
        lib.push_str("/// challenge log of the replica sponge. There is no verdict —\n");
        lib.push_str("/// acceptance belongs to verifiers — so a failure is a refusal\n");
        lib.push_str("/// naming the input or the fill responsible.\n");
        let _ = writeln!(
            lib,
            "pub fn prove({statement_parameter}: &Statement, {}: Witness) -> Result<Prove, ProveError> {{",
            if document.witness_labels.is_empty() {
                "_witness"
            } else {
                "witness"
            }
        );
        let _ = writeln!(
            lib,
            "    let {}challenges: Vec<String> = Vec::new();",
            used.challenges.qualifier()
        );
        let _ = writeln!(
            lib,
            "    let {}proof: Vec<u8> = Vec::new();",
            used.proof.qualifier()
        );
    } else {
        lib.push_str("/// One verifier execution over untrusted proof bytes: a verdict\n");
        lib.push_str("/// and the ordered challenge log. Statement range violations are\n");
        lib.push_str("/// `public_binding_failure`, exactly as the reference executor\n");
        lib.push_str("/// classifies them.\n");
        let _ = writeln!(
            lib,
            "pub fn verify({statement_parameter}: &Statement, proof: &[u8]) -> Outcome {{"
        );
        let _ = writeln!(
            lib,
            "    let {}challenges: Vec<String> = Vec::new();",
            used.challenges.qualifier()
        );
        let _ = writeln!(
            lib,
            "    let {}{}cursor = ProofCursor::new(proof);",
            used.cursor.prefix(),
            used.cursor.qualifier()
        );
    }
    lib.push_str(&body);
    lib.push_str("}\n");

    // ---- Cargo.toml ----
    let feature_list = features
        .iter()
        .map(|feature| format!("\"{feature}\""))
        .collect::<Vec<_>>()
        .join(", ");
    // Witness payloads exist only on the prover side, so only a prover
    // crate offers the memory-hygiene switch — and it offers it as a
    // feature rather than expecting anyone to edit generated code.
    let optional_features = if prover {
        "\n[features]\n\
         # Zero witness payloads on drop; see this crate's README for what\n\
         # that does and does not claim.\n\
         zeroize = [\"zkc-rt/zeroize\"]\n"
    } else {
        ""
    };
    let cargo_toml = format!(
        "# Generated by zkc-emit; do not edit — re-emit.\n\
         [package]\n\
         name = \"{crate_name}\"\n\
         version = \"0.0.0\"\n\
         edition = \"2021\"\n\
         \n\
         [dependencies]\n\
         zkc-rt = {{ path = \"{rt_path}\", default-features = false, features = [{feature_list}] }}\n\
         {optional_features}"
    );

    // ---- README.md ----
    // Written as literal markdown rather than assembled, because this
    // text is the emitted crate's only statement of what it does not
    // claim, and it should read the same in the source as on the page.
    let entry_point = if prover {
        r"`prove(statement, witness)` returns the emitted proof bytes and the
ordered challenge log, or a refusal naming the statement value or fill
responsible. There is no verdict channel: acceptance belongs to
verifiers. Supplier resolution happened at emit time, so no run-time
outcome means `no supplier`.

## What this endpoint does not do

- **Secrets.** Witness payloads pass through as opaque bytes. The
  specification places confidentiality with the provider, runtime, and
  target (`docs/spec/endpoints.md` §6.4); the bound fills are test-grade
  and variable-time, and a deployment supplier owns its own
  constant-time discipline. Building this crate with the `zeroize`
  feature makes `Payload` zero on drop; without it, nothing is claimed
  either way, because memory hygiene is a property of a whole call
  chain, not of one type.
- **Nonces.** Nonce material arrives inside the witness payload.
  Deriving it, and never reusing it, is the caller's — for a
  Schnorr-shaped protocol, nonce reuse across two statements discloses
  the witness. Deterministic derivation in the style of RFC 6979 or
  EdDSA is the deployment-grade pattern; this crate neither generates
  nor checks nonces.
- **Witness computation.** Nothing here computes a witness from a
  relation. That layer is upstream, and the payload boundary is exactly
  where it stops.
- **Counterparty coverage.** The `COUNTERPARTY` rows say which checks
  the verifier performs. Their schema, uniqueness, and discharge kinds
  were checked at emit time; that they exhaust the source obligations is
  authenticated only where the sealed protocol is also present (§6.1).
"
    } else {
        r"`verify(statement, proof)` returns the verdict and the ordered
challenge log. Reject classes are the normative set of
`docs/spec/endpoints.md` §4; supplier resolution happened at emit time,
so no run-time outcome means `cannot judge`.
"
    };
    let readme = format!(
        "# {crate_name}\n\n\
         A zkc-emitted {kind} endpoint. Generated — do not edit; re-emit.\n\n\
         ## Identity chain\n\n\
         | Fact | Value |\n|---|---|\n\
         | OIR artifact id | `{artifact}` |\n\
         | OIR semantic id | `{semantic}` |\n\
         | Sealed source protocol | `{source}` |\n\
         | Supplier binding | `{binding_name}` (file sha256 `{binding_digest}`) |\n\
         | Emitter | zkc-emit {version} |\n\n\
         {entry_point}\n\
         ## Scope\n\n\
         Behavior under this binding, at these pins, established by the\n\
         enclosed conformance vectors. This crate makes no claim of\n\
         protocol soundness, zero knowledge, or conformance beyond those\n\
         vectors; those judgments live with the sealed protocol artifact,\n\
         under the identities above.\n",
        kind = if prover { "prover" } else { "verifier" },
        artifact = document.artifact_id,
        semantic = document.semantic_id,
        source = document.source,
        binding_name = binding.name,
        binding_digest = binding.digest_of_file,
        version = env!("CARGO_PKG_VERSION"),
    );
    (lib, cargo_toml, readme)
}

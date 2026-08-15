//! The emitter: one canonical OIR document plus one supplier binding
//! in, one standalone endpoint crate out. This module owns the
//! emit-time supplier gates and the orchestration; the walk, the
//! vector-corpus vocabulary, the crate-file assembly, and the
//! conformance emitters are its submodules.

mod conformance;
mod crate_files;
mod vectors;
mod walk;

pub use vectors::{Cases, ProverCase, VectorCase, Vectors};

use crate::binding::Binding;
use crate::doc::{Document, Endpoint};
use crate::rust;

use walk::Walk;

pub struct EmittedCrate {
    pub crate_name: String,
    pub lib_rs: String,
    pub cargo_toml: String,
    pub readme: String,
    pub conformance: Option<String>,
}

/// The normative reject classes (`docs/spec/endpoints.md` §4). The
/// emitter writes these spellings into generated code and admits them in
/// a vector corpus, so it holds the closed set; `zkc-rt` carries the same
/// set as the type the generated code returns.
const REJECT_CLASSES: &[&str] = &[
    "abi_decode_failure",
    "abi_validation_failure",
    "proof_trailing_data",
    "public_binding_failure",
    "transcript_failure",
    "check_failure",
];

/// Emit-time supplier gates: every codec route and construction pin must
/// be realized by the binding before any code exists. The sponge is
/// checked where it is opened, in the `init` arm.
fn gate_suppliers(document: &Document, binding: &Binding) -> Result<(), String> {
    for (class, codec) in &document.codecs {
        let class_binding = binding.class(class).ok_or_else(|| {
            format!(
                "codec class '{class}' has no implementation in binding '{}' (zkc-E400's \
                 emit-time form)",
                binding.name
            )
        })?;
        if class_binding.codec != *codec {
            return Err(format!(
                "class '{class}' routes to codec '{codec}', but binding '{}' implements \
                 '{}' for it",
                binding.name, class_binding.codec
            ));
        }
    }
    for pin in &document.param_digests {
        let (tagged, digest) = pin
            .split_once('=')
            .ok_or_else(|| format!("malformed param digest '{pin}'"))?;
        let supplied = binding.digest_for(tagged).ok_or_else(|| {
            format!(
                "pinned construction '{tagged}' has no supplier digest in binding '{}'",
                binding.name
            )
        })?;
        if supplied != digest {
            return Err(format!(
                "param digest mismatch at '{tagged}': the artifact pins {digest}, binding \
                 '{}' implements {supplied} (zkc-E408's emit-time form)",
                binding.name
            ));
        }
    }
    Ok(())
}

pub fn emit(
    document: &Document,
    binding: &Binding,
    rt_path: &str,
    crate_name: Option<&str>,
    vectors: Option<&Vectors>,
) -> Result<EmittedCrate, String> {
    gate_suppliers(document, binding)?;

    let prover = document.endpoint == Endpoint::ProverSkeleton;
    let (crate_name, crate_ident) =
        rust::crate_name(&crate_name.map(str::to_owned).unwrap_or_else(|| {
            format!(
                "zkc-{}-{}",
                if prover { "prover" } else { "verifier" },
                &document.artifact_id[..12]
            )
        }))?;

    let mut walk = Walk::new(document, binding);
    walk.walk()?;
    let (body, used) = walk.finish();

    let (lib, cargo_toml, readme) =
        crate_files::assemble(document, binding, rt_path, &crate_name, prover, used, &body);

    // ---- tests/conformance.rs ----
    let conformance = match vectors {
        None => None,
        Some(vectors) => Some(conformance::emit_conformance(
            document,
            binding,
            vectors,
            &crate_ident,
        )?),
    };

    Ok(EmittedCrate {
        crate_name,
        lib_rs: lib,
        cargo_toml,
        readme,
        conformance,
    })
}

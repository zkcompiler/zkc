//! Independent algorithm using Spongefish's public API and arkworks directly.
//! Call order follows Spongefish 0.7.4 examples/schnorr.rs, pinned in Cargo.lock.
use crate::{Failure, Operation, Report, Request, Result, measure::measure};
use ark_bls12_381::{Fr, G1Projective as G};
use ark_ff::UniformRand;
use ark_serialize::CanonicalDeserialize;
use serde::Deserialize;
use spongefish_074::{self as spongefish, VerificationError};
use std::{path::Path, str::FromStr};

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Point {
    bytes: String,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Public {
    tag: Vec<u8>,
    session: Vec<u8>,
    base: Point,
    point: Point,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Witness {
    scalar: String,
}

fn point(value: &Point) -> Result<G, String> {
    let mut bytes = Vec::new();
    for chunk in value.bytes.as_bytes().chunks(2) {
        if chunk.len() != 2 {
            return Err("odd hex point".into());
        }
        bytes.push(
            u8::from_str_radix(std::str::from_utf8(chunk).map_err(|e| e.to_string())?, 16)
                .map_err(|e| e.to_string())?,
        );
    }
    if bytes.len() != 48 {
        return Err("expected compressed BLS12-381 point".into());
    }
    G::deserialize_compressed(bytes.as_slice()).map_err(|e| e.to_string())
}

pub fn run(job: &Request, public: &Path, witness: Option<&Path>) -> Result<Report> {
    let public: Public = serde_json::from_slice(&std::fs::read(public).map_err(|e| e.to_string())?)
        .map_err(|e| e.to_string())?;
    if public.tag.len() > 64 {
        return Err("protocol tag too long".into());
    }
    let mut tag = [0; 64];
    tag[..public.tag.len()].copy_from_slice(&public.tag);
    let base = point(&public.base)?;
    let point = point(&public.point)?;
    let instance = [base, point];
    let session = std::str::from_utf8(&public.session).map_err(|e| e.to_string())?;
    let domain = || {
        spongefish::DomainSeparator::new(tag)
            .session(spongefish::session_id_from_str(session))
            .instance(&instance)
    };
    let scalar = if job.operation == Operation::Prove {
        let witness: Witness = serde_json::from_slice(
            &std::fs::read(witness.ok_or("missing witness")?).map_err(|e| e.to_string())?,
        )
        .map_err(|e| e.to_string())?;
        Some(Fr::from_str(&witness.scalar).map_err(|_| "invalid scalar")?)
    } else {
        None
    };
    let verify = |proof: &[u8]| -> Result<()> {
        let check = || -> Result<(), VerificationError> {
            let mut state = domain().std_verifier(proof);
            let commitment = state.prover_message::<G>()?;
            let challenge = state.verifier_message::<Fr>();
            let response = state.prover_message::<Fr>()?;
            if base * response != commitment + point * challenge {
                return Err(VerificationError);
            }
            state.check_eof()
        };
        check().map_err(|_| Failure::Rejected("Schnorr verification".into()))
    };
    let input = if job.operation == Operation::Verify {
        std::fs::read(&job.proof).map_err(|e| e.to_string())?
    } else {
        Vec::new()
    };
    let mut last = Vec::new();
    let mut proofs = Vec::new();
    let samples = measure(
        job.plan,
        || Ok(()),
        |_| {
            if let Some(scalar) = scalar {
                let mut state = domain().std_prover();
                let nonce = Fr::rand(state.rng());
                state.prover_message(&(base * nonce));
                let challenge = state.verifier_message::<Fr>();
                state.prover_message(&(nonce + challenge * scalar));
                Ok(state.narg_string().to_vec())
            } else {
                verify(&input)?;
                Ok(Vec::new())
            }
        },
        |proof| {
            if job.operation == Operation::Prove {
                crate::retain_proof(&job.proof, &proof, &mut proofs)?;
                last = proof;
            }
            Ok(())
        },
    )?;
    if job.operation == Operation::Prove {
        std::fs::write(&job.proof, &last).map_err(|e| e.to_string())?;
    }
    let mut report = Report::new(
        "reference_proof_call",
        samples,
        if job.operation == Operation::Prove {
            last.len()
        } else {
            input.len()
        },
    );
    report.proofs = proofs;
    Ok(report)
}

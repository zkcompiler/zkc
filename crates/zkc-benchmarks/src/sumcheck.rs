//! Independent public-table Sumcheck: contiguous halves, pair messages, MSB first.
//! No zkc runtime, mathematical kernel, codec or compiler calls.
use crate::{Failure, Operation, Report, Request, Result, measure::measure};
use ark_bls12_381::Fr;
use ark_ff::AdditiveGroup;
use serde::Deserialize;
use spongefish_074::{self as spongefish, Encoding, VerificationError};
use std::{path::Path, str::FromStr};

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Public {
    values: Vec<String>,
    claim: String,
    rounds: String,
    tag: Vec<u8>,
    session: Vec<u8>,
}

fn fold(table: &mut Vec<Fr>, r: Fr) {
    let half = table.len() / 2;
    for i in 0..half {
        table[i] = table[i] + r * (table[i + half] - table[i]);
    }
    table.truncate(half);
}

pub fn run(job: &Request, public: &Path) -> Result<Report> {
    let public: Public = serde_json::from_slice(&std::fs::read(public).map_err(|e| e.to_string())?)
        .map_err(|e| e.to_string())?;
    let values: Vec<Fr> = public
        .values
        .iter()
        .map(|s| Fr::from_str(s).map_err(|_| "invalid field".to_string()))
        .collect::<Result<_, _>>()?;
    let rounds = public.rounds.parse::<u32>().map_err(|e| e.to_string())?;
    if 1usize.checked_shl(rounds) != Some(values.len()) || public.tag.len() > 64 {
        return Err("table shape or tag".into());
    }
    let claim = Fr::from_str(&public.claim).map_err(|_| "invalid claim")?;
    let mut tag = [0; 64];
    tag[..public.tag.len()].copy_from_slice(&public.tag);
    // Include ordered table, claim and dimension in both implementations.
    let session = std::str::from_utf8(&public.session).map_err(|e| e.to_string())?;
    let instance = || {
        let mut bytes = Vec::with_capacity((values.len() + 2) * 32);
        for value in values.iter().chain([&claim, &Fr::from(rounds)]) {
            bytes.extend_from_slice(value.encode().as_ref());
        }
        bytes
    };
    let verify = |proof: &[u8]| -> Result<()> {
        let check = || -> Result<(), VerificationError> {
            let encoded = instance();
            let domain = spongefish::DomainSeparator::new(tag)
                .session(spongefish::session_id_from_str(session))
                .instance(encoded.as_slice());
            let mut state = domain.std_verifier(proof);
            let mut current = claim;
            let mut point = Vec::new();
            for _ in 0..rounds {
                let a = state.prover_message::<Fr>()?;
                let b = state.prover_message::<Fr>()?;
                if a + b != current {
                    return Err(VerificationError);
                }
                let r = state.verifier_message::<Fr>();
                current = a + r * (b - a);
                point.push(r);
            }
            let mut table = values.clone();
            for r in point {
                fold(&mut table, r);
            }
            if table[0] != current {
                return Err(VerificationError);
            }
            state.check_eof()
        };
        check().map_err(|_| Failure::Rejected("Sumcheck verification".into()))
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
            if job.operation == Operation::Verify {
                verify(&input)?;
                return Ok(Vec::new());
            }
            let encoded = instance();
            let domain = spongefish::DomainSeparator::new(tag)
                .session(spongefish::session_id_from_str(session))
                .instance(encoded.as_slice());
            let mut state = domain.std_prover();
            let mut table = values.clone();
            for _ in 0..rounds {
                let half = table.len() / 2;
                let a = table[..half].iter().fold(Fr::ZERO, |a, b| a + b);
                let b = table[half..].iter().fold(Fr::ZERO, |a, b| a + b);
                state.prover_message(&a);
                state.prover_message(&b);
                fold(&mut table, state.verifier_message::<Fr>());
            }
            Ok(state.narg_string().to_vec())
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

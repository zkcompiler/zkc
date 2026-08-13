//! The KZG golden-vector generator: reads one canonical KZG verifier
//! document (the single-opening shape or the batched shape the
//! same-point transform produces) and prints its vector file.
//!
//! The vectors are built from scalar arithmetic over a known test τ
//! (τ = 20260813, matching the `kzg-toy` binding's pinned `tau_g2`);
//! the emitted verifier checks them with pairings — two independent
//! routes to the same equations, so the file cannot be produced by the
//! code it gates. Committed vector files are regenerated and diffed by
//! the lit suite, which is the determinism contract.

use ark_ec::{AffineRepr, CurveGroup, PrimeGroup};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use zkc_rt::kzg::{fr_decimal, fr_from_digest, fr_to_wire, g1_to_wire, Fr, G1};
use zkc_rt::toy::ToyDuplex;

const TAU: u64 = 20260813;

/// p_a(X) = X² + 3 behind C1, p_b(X) = 2X behind C2, opened at z = 2.
fn polynomial_a(x: Fr) -> Fr {
    x * x + Fr::from(3u64)
}
fn polynomial_b(x: Fr) -> Fr {
    x * Fr::from(2u64)
}

fn commit(value_at_tau: Fr) -> G1 {
    (ark_bls12_381::G1Projective::generator() * value_at_tau).into_affine()
}

/// The opening witness for one polynomial: ((p(τ) − p(z)) / (τ − z))·g1.
fn witness(p_tau: Fr, p_z: Fr, tau: Fr, z: Fr) -> G1 {
    commit((p_tau - p_z) / (tau - z))
}

fn wire_decimal(bytes: &[u8]) -> String {
    // The statement channel carries decimal integers; a wire value is
    // its big-endian integer reading.
    let mut digits = vec![0u8];
    for &byte in bytes {
        let mut carry = byte as u32;
        for digit in digits.iter_mut() {
            let wide = (*digit as u32) * 256 + carry;
            *digit = (wide % 10) as u8;
            carry = wide / 10;
        }
        while carry > 0 {
            digits.push((carry % 10) as u8);
            carry /= 10;
        }
    }
    digits.iter().rev().map(|d| char::from(b'0' + d)).collect()
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn main() {
    let path = std::env::args()
        .nth(1)
        .expect("usage: kzg_vectors <verifier-doc.json>");
    let bytes = std::fs::read(&path).expect("cannot read the document");
    let mut hasher = Sha256::new();
    hasher.update(b"zkc/oir\n");
    hasher.update(&bytes);
    let artifact_id = hex(&hasher.finalize());

    let document: Value = serde_json::from_slice(&bytes).expect("not JSON");
    let source = document["source"].as_str().expect("no source").to_owned();
    let labels: Vec<&str> = document["statement_labels"]
        .as_array()
        .expect("no statement labels")
        .iter()
        .map(|label| label.as_str().unwrap())
        .collect();
    assert_eq!(
        labels,
        ["C1", "C2", "z", "v1", "v2"],
        "the KZG statement shape"
    );
    let program = document["program"].as_array().expect("no program");

    let tau = Fr::from(TAU);
    let z = Fr::from(2u64);
    let openings = [
        (polynomial_a(tau), polynomial_a(z)), // C1, v1
        (polynomial_b(tau), polynomial_b(z)), // C2, v2
    ];
    let commitments = [commit(openings[0].0), commit(openings[1].0)];
    let statement = json!({
        "C1": wire_decimal(&g1_to_wire(&commitments[0])),
        "C2": wire_decimal(&g1_to_wire(&commitments[1])),
        "z": wire_decimal(&fr_to_wire(&z)),
        "v1": wire_decimal(&fr_to_wire(&openings[0].1)),
        "v2": wire_decimal(&fr_to_wire(&openings[1].1)),
    });

    let batch_row = program
        .iter()
        .find(|row| row[0] == "check_call" && row[3] == "zkc.check.kzg-batch-opening");

    let (honest_proof, challenges): (Vec<u8>, Vec<String>) = match batch_row {
        None => {
            // The single-opening shape: the wire is W1 ‖ W2, and no
            // challenge is ever squeezed.
            let w1 = witness(openings[0].0, openings[0].1, tau, z);
            let w2 = witness(openings[1].0, openings[1].1, tau, z);
            let mut wire = g1_to_wire(&w1).to_vec();
            wire.extend_from_slice(&g1_to_wire(&w2));
            (wire, Vec::new())
        }
        Some(check) => {
            // The batched shape: γ from the toy transcript over the
            // absorbed statement, then one folded witness, γ-weighted in
            // the check's own operand order.
            let squeeze = program
                .iter()
                .find(|row| row[0] == "squeeze")
                .expect("the batched shape squeezes gamma");
            let domain = squeeze[5].as_str().expect("no domain");
            let mut sponge = ToyDuplex::new(&source);
            sponge.absorb(&g1_to_wire(&commitments[0]));
            sponge.absorb(&g1_to_wire(&commitments[1]));
            sponge.absorb(&fr_to_wire(&z));
            sponge.absorb(&fr_to_wire(&openings[0].1));
            sponge.absorb(&fr_to_wire(&openings[1].1));
            let gamma = fr_from_digest(&sponge.squeeze(domain));

            // Operand order: the first n check inputs are the commitment
            // references, `["a", index]` into the statement; pair values
            // by the same index order.
            let inputs = check[1].as_array().expect("check inputs");
            let n = (inputs.len() - 3) / 2;
            let mut p_star_tau = Fr::from(0u64);
            let mut weight = Fr::from(1u64);
            let mut y_star = Fr::from(0u64);
            for input in &inputs[..n] {
                let argument = input[1].as_u64().expect("a statement reference") as usize;
                // Arguments 0 and 1 are C1 and C2.
                let (p_tau, p_z) = openings[argument];
                p_star_tau += p_tau * weight;
                y_star += p_z * weight;
                weight *= gamma;
            }
            let folded_witness = witness(p_star_tau, y_star, tau, z);
            (
                g1_to_wire(&folded_witness).to_vec(),
                vec![fr_decimal(&gamma)],
            )
        }
    };

    // The corrupted control stays a valid group element: it must die at
    // the pairing equation, never at decode.
    let mut corrupt_point = zkc_rt::kzg::g1_from_wire(&honest_proof[..48]).unwrap();
    corrupt_point =
        (corrupt_point.into_group() + ark_bls12_381::G1Projective::generator()).into_affine();
    let mut corrupted = honest_proof.clone();
    corrupted[..48].copy_from_slice(&g1_to_wire(&corrupt_point));

    let mut trailing = honest_proof.clone();
    trailing.push(0);

    let mut invalid = honest_proof.clone();
    invalid[..48].copy_from_slice(&[0xff; 48]);

    let vectors = json!({
        "artifact_id": artifact_id,
        "source": source,
        "vectors": [
            {
                "name": "honest",
                "statement": statement,
                "proof": hex(&honest_proof),
                "expect": "accept",
                "challenges": challenges,
            },
            {
                "name": "tampered_witness",
                "statement": statement,
                "proof": hex(&corrupted),
                "expect": "check_failure",
                "challenges": challenges,
            },
            {
                "name": "trailing_byte",
                "statement": statement,
                "proof": hex(&trailing),
                "expect": "proof_trailing_data",
                "challenges": challenges,
            },
            {
                "name": "truncated",
                "statement": statement,
                "proof": hex(&honest_proof[..24]),
                "expect": "abi_decode_failure",
                "challenges": challenges,
            },
            {
                "name": "invalid_point",
                "statement": statement,
                "proof": hex(&invalid),
                "expect": "abi_decode_failure",
                "challenges": challenges,
            },
        ],
    });
    println!(
        "{}",
        serde_json::to_string_pretty(&vectors).expect("serializable")
    );
}

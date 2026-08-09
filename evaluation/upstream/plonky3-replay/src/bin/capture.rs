//! Capture one pinned FRI-shaped witness: prove with the plain challenger,
//! demonstrate non-perturbation of the observer, record the verifier-side
//! transcript, and emit the fixture.
//!
//! Usage: capture [output-path]   (stdout when no path is given)

use p3_field::PrimeField32;
use p3_uni_stark::{prove, verify};
use zkc_plonky3_replay::*;

fn main() {
    let (a, b) = (0u64, 1u64);
    let trace = generate_trace(a, b, TRACE_HEIGHT);
    let pis = public_values(a, b, TRACE_HEIGHT);

    // The proof of record comes from the plain, uninstrumented path.
    let config = plain_config();
    let proof = prove(&config, &FibAir, trace.clone(), &pis);
    verify(&config, &FibAir, &proof, &pis).expect("baseline verification must accept");

    let proof_bytes = postcard::to_allocvec(&proof).expect("postcard encoding");

    // Non-perturbation, demonstrated rather than asserted: an instrumented
    // prover run yields byte-identical proof, and an instrumented verifier
    // run accepts the same proof.
    let (recording, _prover_log) = recording_config();
    let instrumented_proof = prove(&recording, &FibAir, trace, &pis);
    let instrumented_bytes = postcard::to_allocvec(&instrumented_proof).expect("postcard encoding");
    assert_eq!(
        proof_bytes, instrumented_bytes,
        "the observing challenger perturbed the prover"
    );

    // The verifier-side transcript, captured twice: the second run must
    // reproduce the first byte for byte, or the capture is not a record.
    // The proof is re-decoded from its bytes because Proof is typed by the
    // whole config, and the instrumented config is a different type.
    let recording_proof: p3_uni_stark::Proof<RecordingConfig> =
        postcard::from_bytes(&proof_bytes).expect("postcard decoding");
    let transcript = {
        let (recording, log) = recording_config();
        verify(&recording, &FibAir, &recording_proof, &pis)
            .expect("instrumented verification must accept");
        let first = log.lock().unwrap().clone();

        let (recording, log) = recording_config();
        verify(&recording, &FibAir, &recording_proof, &pis)
            .expect("instrumented verification must accept");
        let second = log.lock().unwrap().clone();

        assert_eq!(
            first, second,
            "verifier transcript capture is not deterministic"
        );
        first
    };

    let fixture = Fixture {
        format: FIXTURE_FORMAT.to_string(),
        status: "prototype".to_string(),
        backend: BackendRecord {
            repository: PLONKY3_REPOSITORY.to_string(),
            revision: PLONKY3_REVISION.to_string(),
            crates: [
                "p3-air",
                "p3-baby-bear",
                "p3-challenger",
                "p3-commit",
                "p3-dft",
                "p3-field",
                "p3-fri",
                "p3-matrix",
                "p3-merkle-tree",
                "p3-symmetric",
                "p3-uni-stark",
            ]
            .iter()
            .map(|s| s.to_string())
            .collect(),
        },
        config: config_record(),
        air: AirRecord {
            name: AIR_NAME.to_string(),
            content_digest: air_content_digest(),
            width: NUM_FIB_COLS,
            num_public_values: NUM_PUBLIC_VALUES,
        },
        instance: InstanceRecord {
            public_values: pis.iter().map(|v| v.as_canonical_u32()).collect(),
            degree_bits: proof.degree_bits,
        },
        proof: ProofRecord {
            encoding: "postcard-1".to_string(),
            sha256: sha256_hex(&proof_bytes),
            bytes_hex: hex::encode(&proof_bytes),
        },
        transcript,
        acceptance: true,
    };

    let rendered = serde_json::to_string_pretty(&fixture).expect("fixture serialization");
    match std::env::args().nth(1) {
        Some(path) => std::fs::write(&path, rendered + "\n").expect("write fixture"),
        None => println!("{rendered}"),
    }
}

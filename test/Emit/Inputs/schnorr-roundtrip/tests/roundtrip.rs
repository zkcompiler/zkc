//! Both endpoints of one sealed protocol, emitted from one projection
//! and run against each other in one process.
//!
//! The reference round trip (`test/Oir/prover-round-trip.test`) runs the
//! interpreter on both sides. This runs the emitted crates on both
//! sides, so what is under test is the translation, not the reference:
//! if the emitter mis-emits an absorb order, a framing, or a challenge
//! derivation on either arm, the two replicas disagree and the verifier
//! rejects.
//!
//! The negative leg is the point of the `toy-cheat` binding. Its prover
//! is honest everywhere the emitted program governs — same transcript,
//! same framing, same challenge — and wrong only inside one fill. So the
//! rejection has to land at the equation and nowhere else, which is what
//! makes `check_failure` here a statement about the boundary rather than
//! about a corrupted byte.

use zkc_prover_schnorr as prover;
use zkc_prover_schnorr_cheat as cheat;
use zkc_verifier_schnorr as verifier;

/// The pinned fixture: witness x = 5, nonce k = 7, statement y = 4^5.
const WITNESS: &str = "00000000000000050000000000000007";
const Y: u64 = 1024;

#[test]
fn the_two_endpoints_project_the_same_protocol() {
    // Same seal, same projection: the source identity is what both
    // replica sponges seed from, so a mismatch here would make every
    // other assertion in this file vacuous.
    assert_eq!(prover::SOURCE_PIR_ID, verifier::SOURCE_PIR_ID);
    assert_eq!(cheat::SOURCE_PIR_ID, verifier::SOURCE_PIR_ID);
    // The cheat differs in its binding alone, never in the artifact.
    assert_eq!(cheat::ARTIFACT_ID, prover::ARTIFACT_ID);
    assert_ne!(cheat::BINDING, prover::BINDING);
}

#[test]
fn the_emitted_prover_s_bytes_are_accepted_by_the_emitted_verifier() {
    let produced = prover::prove(
        &prover::Statement { y: Y },
        prover::Witness {
            w: prover::Payload::from_hex(WITNESS).expect("a lowercase-hex payload"),
        },
    )
    .expect("the honest binding produces a proof");

    let outcome = verifier::verify(&verifier::Statement { y: Y }, &produced.proof);
    assert_eq!(outcome.verdict.as_str(), "accept");
    // Entry for entry: the prover's replica sponge and the verifier's
    // derived the same challenge stream from the same transcript.
    assert_eq!(produced.challenges, outcome.challenges);
}

#[test]
fn the_cheating_binding_is_rejected_at_the_equation() {
    let produced = cheat::prove(
        &cheat::Statement { y: Y },
        cheat::Witness {
            w: cheat::Payload::from_hex(WITNESS).expect("a lowercase-hex payload"),
        },
    )
    .expect("a boundary-conformant fill still produces bytes");

    let honest = prover::prove(
        &prover::Statement { y: Y },
        prover::Witness {
            w: prover::Payload::from_hex(WITNESS).expect("a lowercase-hex payload"),
        },
    )
    .expect("the honest binding produces a proof");

    // The commitment and the challenge are untouched; only the response
    // differs. That is what puts the failure at the equation.
    assert_eq!(produced.proof[..8], honest.proof[..8]);
    assert_eq!(produced.challenges, honest.challenges);
    assert_ne!(produced.proof[8..], honest.proof[8..]);

    let outcome = verifier::verify(&verifier::Statement { y: Y }, &produced.proof);
    assert_eq!(outcome.verdict.as_str(), "check_failure");
    assert_eq!(outcome.challenges, produced.challenges);
}

#[test]
fn a_malformed_payload_is_the_caller_s_boundary() {
    // Odd length: the hex boundary is the caller's, exactly where the
    // reference executor puts it, and `prove` is never reached.
    assert!(prover::Payload::from_hex("0f0").is_none());
    assert!(prover::Payload::from_hex("0F").is_none());
}

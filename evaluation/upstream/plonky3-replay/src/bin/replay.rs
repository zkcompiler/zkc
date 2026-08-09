//! Replay the upstream verifier from a captured fixture alone.
//!
//! Usage: replay <fixture.json> [mutation]
//!
//! Mutations, each with the layer that refuses it reported honestly:
//!   flip-proof-byte     flip one bit mid-proof; postcard decoding refuses
//!                       (the byte encoding is load-bearing before the
//!                       verifier ever runs)
//!   truncate-proof      drop the final byte; refused at decode likewise
//!   wrong-public-value  perturb the last public value; refused by the
//!                       pinned verifier itself
//!   flip-opened-value   perturb one opened evaluation inside the decoded
//!                       proof; refused by the pinned verifier itself
//!   swap-events         transcript-level demonstration on the challenger,
//!                       not a verifier run: swapping two adjacent
//!                       observations changes the derived challenge
//!
//! Exit code 0 = the expected outcome happened. Anything else is a defect.

use p3_field::{PrimeCharacteristicRing, PrimeField32, PrimeField64};
use p3_uni_stark::verify;
use zkc_plonky3_replay::*;

fn main() {
    let mut args = std::env::args().skip(1);
    let path = args
        .next()
        .expect("usage: replay <fixture.json> [mutation]");
    let mutation = args.next();

    let fixture: Fixture =
        serde_json::from_str(&std::fs::read_to_string(&path).expect("read fixture"))
            .expect("fixture parse");

    // The fixture must describe exactly the configuration this binary pins;
    // a fixture from another universe is refused, not reinterpreted.
    assert_eq!(fixture.format, FIXTURE_FORMAT, "unknown fixture format");
    assert_eq!(
        fixture.backend.revision, PLONKY3_REVISION,
        "fixture pins a different upstream revision"
    );
    assert_eq!(
        fixture.config,
        config_record(),
        "fixture configuration disagrees with the pinned configuration"
    );
    assert_eq!(
        fixture.air.content_digest,
        air_content_digest(),
        "fixture AIR is not the AIR this binary embeds"
    );

    let mut proof_bytes = hex::decode(&fixture.proof.bytes_hex).expect("proof hex");
    assert_eq!(
        sha256_hex(&proof_bytes),
        fixture.proof.sha256,
        "proof bytes disagree with their recorded digest"
    );

    // Fixture values are canonical field elements or the fixture is refused:
    // Val::new reduces silently, and a silently reduced statement is a
    // different statement.
    for &value in &fixture.instance.public_values {
        assert!(
            (value as u64) < Val::ORDER_U64,
            "fixture public value {value} is not a canonical field element"
        );
    }
    let mut public_values: Vec<Val> = fixture
        .instance
        .public_values
        .iter()
        .map(|&v| Val::new(v))
        .collect();

    let mut mutate_decoded: Option<fn(&mut p3_uni_stark::Proof<RecordingConfig>)> = None;
    match mutation.as_deref() {
        None => {}
        Some("flip-proof-byte") => {
            let middle = proof_bytes.len() / 2;
            proof_bytes[middle] ^= 1;
        }
        Some("truncate-proof") => {
            proof_bytes.pop();
        }
        Some("wrong-public-value") => {
            let last = public_values.len() - 1;
            public_values[last] += Val::ONE;
        }
        Some("flip-opened-value") => {
            mutate_decoded = Some(|proof| {
                let opened = &mut proof.opened_values.trace_local;
                opened[0] += <RecordingConfig as p3_uni_stark::StarkGenericConfig>::Challenge::ONE;
            });
        }
        Some("swap-events") => {
            swap_events_diverges(&fixture);
            return;
        }
        Some(other) => panic!("unknown mutation '{other}'"),
    }

    #[derive(PartialEq, Clone, Copy, Debug)]
    enum Outcome {
        Accepted,
        RefusedAtDecode,
        RefusedByVerifier,
    }

    // Deterministic replay: run twice from the fixture alone, same outcome
    // both times; on the accepting path the captured transcript must be
    // reproduced exactly.
    let run = || -> Outcome {
        let decoded: Result<p3_uni_stark::Proof<RecordingConfig>, _> =
            postcard::from_bytes(&proof_bytes);
        match decoded {
            Err(_) => Outcome::RefusedAtDecode,
            Ok(mut proof) => {
                if let Some(mutate) = mutate_decoded {
                    mutate(&mut proof);
                }
                let (config, log) = recording_config();
                if verify(&config, &FibAir, &proof, &public_values).is_ok() {
                    if mutation.is_none() {
                        let observed = log.lock().unwrap().clone();
                        assert_eq!(
                            observed, fixture.transcript,
                            "replay transcript diverges from the captured transcript"
                        );
                    }
                    Outcome::Accepted
                } else {
                    Outcome::RefusedByVerifier
                }
            }
        }
    };
    let first = run();
    assert_eq!(first, run(), "replay outcome is not deterministic");

    match (mutation.as_deref(), first) {
        (None, Outcome::Accepted) => {
            println!("replay: accepted, deterministic, transcript reproduced")
        }
        (None, other) => panic!("the captured proof must replay to acceptance, got {other:?}"),
        (Some(name), Outcome::RefusedAtDecode) => {
            println!("replay: mutation '{name}' refused at decode")
        }
        (Some(name), Outcome::RefusedByVerifier) => {
            println!("replay: mutation '{name}' refused by the verifier")
        }
        (Some(name), Outcome::Accepted) => panic!("mutation '{name}' was not refused"),
    }
}

/// Transcript-order sensitivity, shown on the challenger itself — this is a
/// property demonstration on the captured log, not an upstream verifier
/// run: replaying the captured observations in order and with two adjacent
/// distinct observations swapped must derive different challenge values
/// (an observation invalidates buffered output in the duplex sponge).
fn swap_events_diverges(fixture: &Fixture) {
    use p3_baby_bear::default_babybear_poseidon2_16;
    use p3_challenger::{CanObserve, CanSample};

    let observes: Vec<u32> = fixture
        .transcript
        .iter()
        .filter_map(|event| match event {
            Event::ObserveVal(value) => Some(*value),
            _ => None,
        })
        .collect();
    assert!(
        observes.len() >= 2,
        "the captured transcript carries too few field observations to swap"
    );

    let derive = |values: &[u32]| -> u32 {
        let mut challenger = PlainChallenger::new(default_babybear_poseidon2_16());
        for &value in values {
            challenger.observe(Val::new(value));
        }
        let sampled: Val = challenger.sample();
        sampled.as_canonical_u32()
    };

    let mut swapped = observes.clone();
    let position = swapped
        .windows(2)
        .position(|pair| pair[0] != pair[1])
        .expect("all observed values equal; nothing to swap");
    swapped.swap(position, position + 1);

    assert_ne!(
        derive(&observes),
        derive(&swapped),
        "swapping adjacent observations did not change the derived challenge"
    );
    println!(
        "replay: mutation 'swap-events' diverges as required (transcript-level, not a verifier run)"
    );
}

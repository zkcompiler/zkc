//! The backend runner (evaluation/upstream/plonky3-replay/README.md): consumes the
//! canonical prover-artifact document, recomputes its identity before
//! reading semantics, drives the pinned FRI prover in-process with the
//! recording challenger, checks every recorded event against the
//! artifact's schedule under the declared correspondence relation for
//! this backend pair, assembles the spine wire the zkc executor reads,
//! and runs the pinned verifier on the produced proof — acceptance leg
//! 3b's verdict and leg 3a's inputs in one run record.
//!
//! The fills are the pinned crate's own code paths (`pcs.open` is the
//! composition of the routed holes), which is exactly the in-process
//! coupling the design gate chose; the correspondence check is what
//! ties the run to the artifact rather than to good intentions.

use std::env;
use std::fs;

use p3_baby_bear::default_babybear_poseidon2_16;
use p3_challenger::{CanObserve, FieldChallenger};
use p3_commit::Pcs as PcsTrait;
use p3_field::PrimeCharacteristicRing;
use p3_field::extension::BinomialExtensionField;
use p3_matrix::dense::RowMajorMatrix;
use serde_json::Value as Json;
use sha2::{Digest, Sha256};
use zkc_plonky3_replay::{
    ChallengeMmcs, Compress, Dft, Event, FieldHash, Pcs, PlainChallenger, RecordingChallenger, Val,
    ValMmcs, fri_parameters,
};

type Challenge = BinomialExtensionField<Val, 4>;

fn fail(message: &str) -> ! {
    eprintln!("prover runner: {message}");
    std::process::exit(1)
}

/// Little-word-first 32-bit limbs to a decimal string — the machine
/// value packing of the zkc executor's digest and extension codecs.
fn packed_decimal(words: &[u32]) -> String {
    let mut limbs: Vec<u32> = words.to_vec();
    let mut digits = Vec::new();
    while limbs.iter().any(|&w| w != 0) {
        let mut remainder: u64 = 0;
        for limb in limbs.iter_mut().rev() {
            let value = (remainder << 32) | u64::from(*limb);
            *limb = (value / 10) as u32;
            remainder = value % 10;
        }
        digits.push(b'0' + remainder as u8);
    }
    if digits.is_empty() {
        return "0".to_string();
    }
    digits.reverse();
    String::from_utf8(digits).unwrap()
}

fn push_word_be(wire: &mut Vec<u8>, word: u32) {
    wire.extend_from_slice(&word.to_be_bytes());
}

/// The class of the value a program-row reference names, resolved the
/// way the canonical document lets any consumer resolve it: block
/// arguments by ABI position, results by their producing row.
fn class_of(
    reference: &Json,
    rows: &[Json],
    statement_count: usize,
    witness_labels: &[Json],
) -> String {
    let parts = reference
        .as_array()
        .unwrap_or_else(|| fail("malformed ref"));
    match parts[0].as_str() {
        Some("a") => {
            let index = parts[1].as_u64().unwrap() as usize;
            if index < statement_count {
                "rs".to_string() // the value-faithful statement channel
            } else if index < statement_count + witness_labels.len() {
                witness_labels[index - statement_count][1]
                    .as_str()
                    .unwrap()
                    .to_string()
            } else {
                fail("reference names the stream argument")
            }
        }
        Some("r") => {
            let row = &rows[parts[1].as_u64().unwrap() as usize];
            let index = parts[2].as_u64().unwrap() as usize;
            let tag = row[0].as_str().unwrap();
            match tag {
                "const" => row[2].as_str().unwrap().to_string(),
                "squeeze" => row[3].as_str().unwrap().to_string(),
                "hole_call" => {
                    let descriptor = row[2][index].as_array().unwrap();
                    descriptor[1].as_str().unwrap().to_string()
                }
                _ => fail("reference into a row that produces no value"),
            }
        }
        _ => fail("unknown reference kind"),
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        fail("usage: prove <canonical-prover-document.json> [corrupt-final-poly]");
    }
    let corrupt = args.iter().any(|a| a == "corrupt-final-poly");
    let bytes = fs::read(&args[1]).unwrap_or_else(|_| fail("cannot read document"));

    // The consumer identity discipline, reimplemented in this language:
    // recompute before reading semantics. The printed id is diffed
    // against the carrier's minted id by the conformance test.
    let mut hasher = Sha256::new();
    hasher.update(b"zkc/oir\n");
    hasher.update(&bytes);
    let artifact_id = hex::encode(hasher.finalize());
    println!("artifact id: {artifact_id}");

    let document: Json = serde_json::from_slice(&bytes).unwrap_or_else(|_| fail("not JSON"));
    if document["endpoint"] != "prover_skeleton" {
        fail("document is not a prover_skeleton endpoint");
    }
    let rows = document["program"]
        .as_array()
        .unwrap_or_else(|| fail("no program"));
    let statement_labels = document["statement_labels"].as_array().unwrap();
    let witness_labels = document["witness_labels"].as_array().unwrap();

    // ----- Drive the pinned prover (the fills, in-process). -----
    let perm = default_babybear_poseidon2_16();
    let hash = FieldHash::new(perm.clone());
    let compress = Compress::new(perm.clone());
    let val_mmcs = ValMmcs::new(hash, compress, 0);
    let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
    let pcs = Pcs::new(Dft::default(), val_mmcs, fri_parameters(challenge_mmcs));

    // One deterministic polynomial: the witness channel is the caller's,
    // and this caller fixes evaluations 1..=8 of a log-size-3 column.
    let log_size = 3usize;
    let evaluations =
        RowMajorMatrix::<Val>::new((1..=1u32 << log_size).map(Val::from_u32).collect(), 1);
    let domain = <Pcs as PcsTrait<Challenge, PlainChallenger>>::natural_domain_for_degree(
        &pcs,
        1 << log_size,
    );

    let (recording, log) = RecordingChallenger::new(PlainChallenger::new(perm.clone()));
    let mut challenger = recording;
    challenger.observe(Val::from_usize(log_size));
    let (commitment, prover_data) = <Pcs as PcsTrait<Challenge, RecordingChallenger>>::commit(
        &pcs,
        vec![(domain, evaluations)],
    );
    challenger.observe(commitment.clone());
    let zeta: Challenge = challenger.sample_algebra_element();
    let (opened_values, mut opening_proof) =
        <Pcs as PcsTrait<Challenge, RecordingChallenger>>::open(
            &pcs,
            vec![(&prover_data, vec![vec![zeta]])],
            &mut challenger,
        );
    let events = log.lock().unwrap().clone();

    // ----- The declared correspondence relation for this pair. -----
    // absorb rs <-> one observed cap; absorb pow_value <-> one observed
    // element; absorb ext_field <-> its four observed coordinates;
    // ext squeeze <-> one extension sample; the nonce absorb plus pow
    // squeeze <-> one grind; one counted vector squeeze <-> its per-draw
    // bit samples. Unmatched events are an error, never silently
    // skipped.
    let mut cursor = 0usize;
    let mut noop_pows = 0usize;
    let mut take = |expect: &str| -> &Event {
        // Zero-bit commit pows are sponge no-ops with no spine member in the
        // captured fixture; they are counted, never silently matched to
        // anything.
        while matches!(events.get(cursor), Some(Event::Grind { bits: 0, .. })) {
            cursor += 1;
            noop_pows += 1;
        }
        let event = events
            .get(cursor)
            .unwrap_or_else(|| fail(&format!("event log short at {expect}")));
        cursor += 1;
        event
    };
    // Absorbed values keyed by the reference that names them, so wire
    // assembly reads exactly what the artifact's write rows cite.
    let mut absorbed: std::collections::HashMap<String, Vec<u32>> =
        std::collections::HashMap::new();
    let mut challenges: Vec<String> = Vec::new();
    let mut correspondence = 0usize;
    for (index, row) in rows.iter().enumerate() {
        let tag = row[0].as_str().unwrap();
        match tag {
            "init" | "const" | "hole_call" | "end_stream" | "finish" | "write" => {}
            "absorb" => {
                let value_ref = row[2].to_string();
                let class = class_of(&row[2], rows, statement_labels.len(), witness_labels);
                match class.as_str() {
                    "rs" => match take("observed cap") {
                        Event::ObserveCap(roots) => {
                            if roots.len() != 1 {
                                fail("cap arity is not one root");
                            }
                            absorbed.insert(value_ref, roots[0].to_vec());
                        }
                        other => fail(&format!("row {index}: expected a cap, saw {other:?}")),
                    },
                    "pow_value" => {
                        let next_is_pow = rows.get(index + 1).and_then(|r| r[0].as_str())
                            == Some("squeeze")
                            && rows[index + 1][3] == "pow_value";
                        if next_is_pow {
                            match take("grind") {
                                Event::Grind { bits, witness } => {
                                    if *bits != 8 {
                                        fail("grind bits disagree");
                                    }
                                    absorbed.insert(value_ref, vec![*witness]);
                                    correspondence += 1;
                                }
                                other => {
                                    fail(&format!("row {index}: expected the grind, saw {other:?}"))
                                }
                            }
                        } else {
                            match take("observed element") {
                                Event::ObserveVal(word) => {
                                    absorbed.insert(value_ref, vec![*word]);
                                }
                                other => fail(&format!(
                                    "row {index}: expected an element, saw {other:?}"
                                )),
                            }
                        }
                    }
                    "ext_field" => {
                        let mut words = Vec::new();
                        for _ in 0..4 {
                            match take("observed coordinate") {
                                Event::ObserveVal(word) => words.push(*word),
                                other => fail(&format!(
                                    "row {index}: expected a coordinate, saw {other:?}"
                                )),
                            }
                        }
                        absorbed.insert(value_ref, words);
                    }
                    other => fail(&format!("row {index}: unroutable class {other}")),
                }
                correspondence += 1;
            }
            "squeeze" => {
                let class = row[3].as_str().unwrap();
                let count = row[4].as_str().unwrap();
                match (class, count) {
                    ("ext_field", "1") => {
                        // The pinned challenger decomposes an extension sample
                        // into four base draws, as recorded by the captured
                        // fixture; a one-shot extension event is accepted
                        // equivalently.
                        let mut words = Vec::new();
                        match take("extension sample") {
                            Event::SampleExt(coords) => words.extend(coords),
                            Event::SampleVal(word) => {
                                words.push(*word);
                                for _ in 0..3 {
                                    match take("extension coordinate") {
                                        Event::SampleVal(word) => words.push(*word),
                                        other => fail(&format!(
                                            "row {index}: expected a base draw, saw {other:?}"
                                        )),
                                    }
                                }
                            }
                            other => fail(&format!(
                                "row {index}: expected an extension sample, saw {other:?}"
                            )),
                        }
                        challenges.push(packed_decimal(&words));
                    }
                    ("pow_value", "1") => {
                        // The grind consumed the sample; the pinned
                        // search found the zero the check demands.
                        challenges.push("0".to_string());
                    }
                    ("query_index", n) => {
                        let draws: usize = n.parse().unwrap();
                        let mut entry = String::new();
                        for draw in 0..draws {
                            match take("query index") {
                                Event::SampleBits { bits, value } => {
                                    if *bits != 4 {
                                        fail("query bits disagree");
                                    }
                                    if draw > 0 {
                                        entry.push('|');
                                    }
                                    entry.push_str(&value.to_string());
                                }
                                other => fail(&format!(
                                    "row {index}: expected a query index, saw {other:?}"
                                )),
                            }
                        }
                        challenges.push(entry);
                    }
                    other => fail(&format!("row {index}: unroutable squeeze {other:?}")),
                }
                correspondence += 1;
            }
            other => fail(&format!("row {index}: unknown row {other}")),
        }
    }
    if cursor != events.len() {
        fail(&format!(
            "{} recorded events past the artifact's schedule",
            events.len() - cursor
        ));
    }
    println!(
        "correspondence: {correspondence} artifact events matched {} recorded \
challenger events ({noop_pows} zero-bit commit pows enumerated as no-ops)",
        events.len()
    );

    // ----- The spine wire: the write rows, in order, each value the
    // one its reference absorbed, canonical by codec width. -----
    let mut wire = Vec::new();
    for row in rows {
        if row[0] != "write" {
            continue;
        }
        let words = absorbed
            .get(&row[2].to_string())
            .unwrap_or_else(|| fail("a written value was never absorbed"));
        for &word in words {
            push_word_be(&mut wire, word);
        }
    }
    // The statement is the first absorbed cap (the input commitment).
    let statement_words = absorbed
        .iter()
        .find_map(|(reference, words)| {
            (reference == "[\"a\",0]" && words.len() == 8).then(|| words.clone())
        })
        .unwrap_or_else(|| fail("no statement cap absorbed"));
    // The trace is the witness the emitted prover is handed; printing
    // it keeps the corpus builder reading this run rather than
    // carrying its own copy of the fixture.
    let trace_hex: String = (1..=1u32 << log_size)
        .map(|value| format!("{value:08x}"))
        .collect();
    println!("trace: {trace_hex}");
    println!("statement f_root: {}", packed_decimal(&statement_words));
    println!("prover challenges: {}", challenges.join(","));
    println!("wire: {}", hex::encode(&wire));

    // ----- Leg 3b: the pinned upstream verifier, fresh challenger. -----
    if corrupt {
        opening_proof.final_poly[0] += Challenge::ONE;
    }
    let mut verifier_challenger = PlainChallenger::new(perm);
    verifier_challenger.observe(Val::from_usize(log_size));
    verifier_challenger.observe(commitment.clone());
    let verifier_zeta: Challenge = verifier_challenger.sample_algebra_element();
    let rounds = vec![(
        commitment,
        vec![(
            domain,
            vec![(verifier_zeta, opened_values[0][0][0].clone())],
        )],
    )];
    match <Pcs as PcsTrait<Challenge, PlainChallenger>>::verify(
        &pcs,
        rounds,
        &opening_proof,
        &mut verifier_challenger,
    ) {
        Ok(()) => println!("upstream verify: accepted the runner's proof at the pinned revision"),
        Err(error) => {
            println!("upstream verify: rejected ({error:?})");
            std::process::exit(2);
        }
    }
}

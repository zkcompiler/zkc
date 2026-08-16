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
use p3_commit::{Mmcs, Pcs as PcsTrait};
use p3_dft::TwoAdicSubgroupDft;
use p3_field::coset::TwoAdicMultiplicativeCoset;
use p3_field::extension::BinomialExtensionField;
use p3_field::{
    BasedVectorSpace, Field, PrimeCharacteristicRing, PrimeField32, batch_multiplicative_inverse,
};
use p3_fri::{FriFoldingStrategy, TwoAdicFriFolding};
use p3_matrix::Matrix;
use p3_matrix::bitrev::BitReversibleMatrix;
use p3_matrix::dense::RowMajorMatrix;
use p3_util::reverse_slice_index_bits;
use serde_json::Value as Json;
use sha2::{Digest, Sha256};
use zkc_plonky3_replay::{
    ChallengeMmcs, Compress, Dft, Event, FieldHash, Pcs, PlainChallenger, RecordingChallenger, Val,
    ValMmcs, fri_parameters_for,
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

/// The element count of the value a program-row reference names: a
/// counted hole result carries it as the descriptor's third entry, and
/// everything else is scalar.
fn count_of(reference: &Json, rows: &[Json]) -> usize {
    let parts = reference
        .as_array()
        .unwrap_or_else(|| fail("malformed ref"));
    if parts[0].as_str() != Some("r") {
        return 1;
    }
    let row = &rows[parts[1].as_u64().unwrap() as usize];
    let index = parts[2].as_u64().unwrap() as usize;
    if row[0].as_str() != Some("hole_call") {
        return 1;
    }
    let descriptor = row[2][index].as_array().unwrap();
    descriptor
        .get(2)
        .and_then(|count| count.as_str())
        .and_then(|text| text.parse().ok())
        .unwrap_or(1)
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
    // The opener's own copies: query answering below rebuilds the
    // commit-phase trees with the same schemes and opens them.
    let opener_val_mmcs = val_mmcs.clone();
    let opener_challenge_mmcs = challenge_mmcs.clone();
    let queries: usize = rows
        .iter()
        .find(|row| row[0] == "squeeze" && row[2] == "query")
        .and_then(|row| row[4].as_str())
        .and_then(|text| text.parse().ok())
        .unwrap_or_else(|| fail("no counted query squeeze"));
    let doc_grind_bits = {
        let row = rows
            .iter()
            .find(|row| row[0] == "squeeze" && row[2] == "pow")
            .unwrap_or_else(|| fail("no pow squeeze"));
        let space: u128 = row[7]
            .as_str()
            .and_then(|text| text.parse().ok())
            .unwrap_or_else(|| fail("pow space is not decimal"));
        if !space.is_power_of_two() {
            fail("pow space is not a power of two");
        }
        space.trailing_zeros() as usize
    };
    // The instance shape, read from the document's own rows — the
    // runner grades whatever the family sealed, not one fixture: the
    // trace log-size is the first pinned constant, the grinding bits
    // and query bits are the squeeze spaces, and the fold depth is the
    // extension-sample count minus the opening point and the batch
    // challenge.
    let log_size = {
        let row = rows
            .iter()
            .find(|row| row[0] == "const")
            .unwrap_or_else(|| fail("no pinned log_size constant"));
        row[1]
            .as_str()
            .and_then(|text| text.parse::<usize>().ok())
            .unwrap_or_else(|| fail("log_size constant is not decimal"))
    };
    let space_log2 = |label: &str| -> usize {
        let row = rows
            .iter()
            .find(|row| row[0] == "squeeze" && row[2] == label)
            .unwrap_or_else(|| fail(&format!("no squeeze labelled {label}")));
        let space: u128 = row[7]
            .as_str()
            .and_then(|text| text.parse().ok())
            .unwrap_or_else(|| fail("squeeze space is not decimal"));
        if !space.is_power_of_two() {
            fail("squeeze space is not a power of two");
        }
        space.trailing_zeros() as usize
    };
    let grind_bits = space_log2("pow");
    let query_bits = space_log2("query");
    let fold_rounds = rows
        .iter()
        .filter(|row| row[0] == "squeeze" && row[3] == "ext_field")
        .count()
        .checked_sub(2)
        .unwrap_or_else(|| fail("fewer extension squeezes than the chain uses"));
    // The shape equation: index bits = trace height + blowup, and the
    // fold chain stops log_final_poly_len above a constant.
    let log_blowup = query_bits
        .checked_sub(log_size)
        .filter(|&b| b >= 1)
        .unwrap_or_else(|| fail("the index space does not cover the trace at a rate below one"));
    let log_final_poly_len = log_size
        .checked_sub(fold_rounds)
        .unwrap_or_else(|| fail("more fold squeezes than the trace height admits"));
    let pcs = Pcs::new(
        Dft::default(),
        val_mmcs,
        fri_parameters_for(
            challenge_mmcs,
            queries,
            doc_grind_bits,
            log_blowup,
            log_final_poly_len,
        ),
    );
    // The deterministic witness column: evaluations 1..=2^log_size.
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
    // The typed samples, in schedule order: the query answering below
    // refolds with exactly the challenges the transcript produced.
    let mut ext_samples: Vec<Challenge> = Vec::new();
    let mut query_indices: Vec<u32> = Vec::new();
    let mut correspondence = 0usize;
    for (index, row) in rows.iter().enumerate() {
        let tag = row[0].as_str().unwrap();
        match tag {
            "init" | "const" | "hole_call" | "end_stream" | "finish" | "write" | "write_vec" => {}
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
                                    if *bits != grind_bits {
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
                        // A counted value absorbs as its elements in
                        // index order — four coordinates each, exactly
                        // the schedule the pinned prover observed.
                        let count = count_of(&row[2], rows);
                        let mut words = Vec::new();
                        for _ in 0..4 * count {
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
                        ext_samples.push(Challenge::from_basis_coefficients_fn(|i| {
                            Val::from_u32(words[i])
                        }));
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
                                    if *bits != query_bits {
                                        fail("query bits disagree");
                                    }
                                    if draw > 0 {
                                        entry.push('|');
                                    }
                                    query_indices.push(*value as u32);
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

    // ----- The query openings: upstream's proof carries pruned
    // multiproofs, whose digest counts depend on which subtrees the
    // sampled indices share; zkc's canonical wire carries per-query
    // independent paths instead (statically counted rows). The runner
    // therefore rebuilds the commit-phase trees with the same schemes
    // and challenges, requires every rebuilt root to equal the proof's
    // own commitment — Merkle binding makes the trees upstream's — and
    // opens full paths from them. -----
    if ext_samples.len() != 2 + fold_rounds {
        fail("the schedule sampled fewer extension values than the chain uses");
    }
    let opener_dft = Dft::default();
    let lde = opener_dft
        .coset_lde_batch(
            RowMajorMatrix::<Val>::new((1..=1u32 << log_size).map(Val::from_u32).collect(), 1),
            log_blowup,
            Val::GENERATOR,
        )
        .bit_reverse_rows()
        .to_row_major_matrix();
    let (rebuilt_commit, input_tree) = opener_val_mmcs.commit_matrix(lde.clone());
    if rebuilt_commit != commitment {
        fail("the rebuilt input tree does not carry the committed root");
    }
    let log_lde_height = log_size + log_blowup;
    let coset = TwoAdicMultiplicativeCoset::new(Val::GENERATOR, log_lde_height)
        .unwrap_or_else(|| fail("the evaluation domain is not two-adic"));
    let mut points: Vec<Val> = coset.iter().collect();
    reverse_slice_index_bits(&mut points);
    let zeta_value = ext_samples[0];
    let opened_at_zeta = opened_values[0][0][0][0];
    let inv_denoms = batch_multiplicative_inverse(
        &points
            .iter()
            .map(|&x| zeta_value - x)
            .collect::<Vec<Challenge>>(),
    );
    let mut current: Vec<Challenge> = lde
        .values
        .iter()
        .zip(&inv_denoms)
        .map(|(&value, &inv)| (opened_at_zeta - Challenge::from(value)) * inv)
        .collect();
    let folding = TwoAdicFriFolding::<(), ()>(std::marker::PhantomData);
    let mut round_trees = Vec::new();
    for (round, &beta) in ext_samples[2..2 + fold_rounds].iter().enumerate() {
        let (cap, tree) = opener_challenge_mmcs.commit_matrix(RowMajorMatrix::new(current, 2));
        if cap != opening_proof.commit_phase_commits[round] {
            fail("a rebuilt round tree does not carry the committed root");
        }
        let leaves = *opener_challenge_mmcs
            .get_matrices(&tree)
            .first()
            .unwrap_or_else(|| fail("a rebuilt round tree holds no matrix"));
        current = <TwoAdicFriFolding<(), ()> as FriFoldingStrategy<Val, Challenge>>::fold_matrix(
            &folding,
            beta,
            1,
            leaves.as_view(),
        );
        round_trees.push(tree);
    }
    let digest_words = |digest: &[Val; 8]| -> Vec<u32> {
        digest
            .iter()
            .map(|element| element.as_canonical_u32())
            .collect()
    };
    let mut leaves_words: Vec<u32> = Vec::new();
    let mut input_path_words: Vec<Vec<u32>> = Vec::new();
    let mut sibling_words: Vec<Vec<u32>> = vec![Vec::new(); round_trees.len()];
    let mut round_path_words: Vec<Vec<u32>> = vec![Vec::new(); round_trees.len()];
    for &index in &query_indices {
        let index = index as usize;
        let opening = opener_val_mmcs.open_batch(index, &input_tree);
        leaves_words.push(opening.opened_values[0][0].as_canonical_u32());
        for digest in &opening.opening_proof {
            input_path_words.push(digest_words(digest));
        }
        let mut current_index = index;
        for (round, tree) in round_trees.iter().enumerate() {
            let group = current_index >> 1;
            let opening = opener_challenge_mmcs.open_batch(group, tree);
            let row = &opening.opened_values[0];
            let sibling = row[(current_index & 1) ^ 1];
            let coordinates: &[Val] = sibling.as_basis_coefficients_slice();
            sibling_words[round]
                .extend(coordinates.iter().map(|element| element.as_canonical_u32()));
            for digest in &opening.opening_proof {
                round_path_words[round].extend(digest_words(digest));
            }
            current_index = group;
        }
    }
    // Keyed by the answer hole's result references, exactly as absorbed
    // values are keyed by theirs.
    let answer_row = rows
        .iter()
        .position(|row| row[0] == "hole_call" && row[4] == "open")
        .unwrap_or_else(|| fail("the prover schedule has no answer hole"));
    let mut openings: std::collections::HashMap<String, Vec<u32>> =
        std::collections::HashMap::new();
    let mut answer_results: Vec<Vec<u32>> = Vec::new();
    answer_results.push(leaves_words);
    answer_results.push(input_path_words.concat());
    for round in 0..round_trees.len() {
        answer_results.push(sibling_words[round].clone());
        answer_results.push(round_path_words[round].clone());
    }
    for (slot, words) in answer_results.into_iter().enumerate() {
        openings.insert(format!("[\"r\",{answer_row},{slot}]"), words);
    }

    // ----- The spine wire: the write rows, in order, each value the
    // one its reference absorbed or the openings above, canonical by
    // codec width. -----
    let mut wire = Vec::new();
    for row in rows {
        if row[0] != "write" && row[0] != "write_vec" {
            continue;
        }
        let reference = row[2].to_string();
        let words = absorbed
            .get(&reference)
            .or_else(|| openings.get(&reference))
            .unwrap_or_else(|| fail("a written value was never absorbed nor opened"));
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

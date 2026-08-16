//! The external judge (the fourth cell of the known-answer square):
//! decode a zkc canonical wire into the pinned upstream `FriProof` and
//! let the pinned upstream verifier grade it. Nothing here consults a
//! zkc verifier — the decoder reads the artifact's schedule for shape,
//! re-derives the query indices with the pinned challenger, rebuilds
//! the pruned multiproofs from the wire's per-query independent paths
//! by pure index arithmetic, and hands the result to `pcs.verify`.
//!
//! The frontier reconstruction cannot mis-accept: upstream's
//! `restore_paths` refuses any digest count other than its own
//! frontier's, so a decoder defect surfaces as a rejection, never as
//! an acceptance the prover did not earn.

use std::env;
use std::fs;

use p3_baby_bear::default_babybear_poseidon2_16;
use p3_challenger::{CanObserve, CanSampleBits, FieldChallenger, GrindingChallenger};
use p3_commit::Pcs as PcsTrait;
use p3_field::extension::BinomialExtensionField;
use p3_field::{BasedVectorSpace, PrimeCharacteristicRing};
use p3_fri::{BatchMultiOpening, CommitPhaseMultiStep, FriProof};
use p3_merkle_tree::PrunedMerklePaths;
use p3_symmetric::{Hash, MerkleCap};
use serde_json::Value as Json;
use sha2::{Digest, Sha256};
use zkc_plonky3_replay::{
    fri_parameters_for, ChallengeMmcs, Compress, Dft, FieldHash, Pcs, PlainChallenger, Val, ValMmcs,
};

type Challenge = BinomialExtensionField<Val, 4>;

fn fail(message: &str) -> ! {
    eprintln!("grade: {message}");
    std::process::exit(1)
}

/// Decimal text into eight 32-bit limbs, least-significant first — the
/// inverse of the run record's `packed_decimal`.
fn decimal_to_digest(text: &str) -> [Val; 8] {
    if text.is_empty() || !text.bytes().all(|b| b.is_ascii_digit()) {
        fail("statement is not decimal");
    }
    let mut limbs = [0u32; 8];
    for digit in text.bytes() {
        let mut carry = u64::from(digit - b'0');
        for limb in limbs.iter_mut() {
            let wide = u64::from(*limb) * 10 + carry;
            *limb = wide as u32;
            carry = wide >> 32;
        }
        if carry != 0 {
            fail("statement does not fit eight limbs");
        }
    }
    limbs.map(Val::from_u32)
}

struct Cursor<'a> {
    bytes: &'a [u8],
    at: usize,
}

impl<'a> Cursor<'a> {
    fn word(&mut self) -> u32 {
        if self.at + 4 > self.bytes.len() {
            fail("wire ends inside a word");
        }
        let word = u32::from_be_bytes(self.bytes[self.at..self.at + 4].try_into().unwrap());
        self.at += 4;
        word
    }
    fn ext(&mut self) -> Challenge {
        let words: [u32; 4] = core::array::from_fn(|_| self.word());
        Challenge::from_basis_coefficients_fn(|i| Val::from_u32(words[i]))
    }
    fn digest(&mut self) -> [Val; 8] {
        core::array::from_fn(|_| Val::from_u32(self.word()))
    }
}

/// One tree's pruned multiproof from per-query independent full paths:
/// the frontier walk is pure index arithmetic over the sorted-unique
/// entry indices (level 0 first; within a level, groups by ascending
/// parent; the missing sibling's digest read from any present member's
/// own path at that level).
fn prune(entries: &[usize], levels: usize, paths: &[Vec<[Val; 8]>]) -> PrunedMerklePaths<Val, 8> {
    let mut sibling_hashes = Vec::new();
    let mut frontier: Vec<usize> = entries.to_vec();
    frontier.sort_unstable();
    frontier.dedup();
    for level in 0..levels {
        // Any query whose entry shifts onto a frontier member supplies
        // that member's sibling digest at this level.
        let digest_of = |member: usize| -> [Val; 8] {
            for (query, entry) in entries.iter().enumerate() {
                if entry >> level == member {
                    return paths[query][level];
                }
            }
            fail("frontier member has no witnessing path");
        };
        let mut next = Vec::new();
        let mut cursor = 0;
        while cursor < frontier.len() {
            let member = frontier[cursor];
            let paired = cursor + 1 < frontier.len() && frontier[cursor + 1] == member ^ 1;
            if paired {
                cursor += 2;
            } else {
                sibling_hashes.push(digest_of(member));
                cursor += 1;
            }
            next.push(member >> 1);
        }
        next.dedup();
        frontier = next;
    }
    PrunedMerklePaths { sibling_hashes }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() != 4 {
        fail("usage: grade <canonical-verifier-document.json> <statement-f_root-decimal-file> <wire-hex-file>");
    }
    let bytes = fs::read(&args[1]).unwrap_or_else(|_| fail("cannot read document"));
    let mut hasher = Sha256::new();
    hasher.update(b"zkc/oir\n");
    hasher.update(&bytes);
    println!("artifact id: {}", hex::encode(hasher.finalize()));

    let document: Json = serde_json::from_slice(&bytes).unwrap_or_else(|_| fail("not JSON"));
    if document["endpoint"] != "verifier" {
        fail("document is not a verifier endpoint");
    }
    let rows = document["program"]
        .as_array()
        .unwrap_or_else(|| fail("no program"));

    // The instance shape from the schedule (the same derivations the
    // parameterized runner uses).
    let log_size: usize = rows
        .iter()
        .find(|row| row[0] == "const")
        .and_then(|row| row[1].as_str())
        .and_then(|text| text.parse().ok())
        .unwrap_or_else(|| fail("no pinned log_size constant"));
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
    let queries: usize = rows
        .iter()
        .find(|row| row[0] == "squeeze" && row[2] == "query")
        .and_then(|row| row[4].as_str())
        .and_then(|text| text.parse().ok())
        .unwrap_or_else(|| fail("no counted query squeeze"));
    let fold_rounds = rows
        .iter()
        .filter(|row| row[0] == "squeeze" && row[3] == "ext_field")
        .count()
        - 2;
    if query_bits != log_size + 1 || fold_rounds + 1 != query_bits {
        fail("the schedule is not the value-faithful family's shape");
    }

    let statement_text =
        fs::read_to_string(&args[2]).unwrap_or_else(|_| fail("cannot read statement"));
    let statement = decimal_to_digest(statement_text.trim());
    let wire_hex = fs::read_to_string(&args[3]).unwrap_or_else(|_| fail("cannot read wire"));
    let wire = hex::decode(wire_hex.trim()).unwrap_or_else(|_| fail("wire is not hex"));
    let mut cursor = Cursor {
        bytes: &wire,
        at: 0,
    };

    // ----- The wire, in the schedule's own order. -----
    let opened_value = cursor.ext();
    let commit_phase_commits: Vec<MerkleCap<Val, [Val; 8]>> = (0..fold_rounds)
        .map(|_| MerkleCap::new(vec![cursor.digest()]))
        .collect();
    let final_poly = vec![cursor.ext()];
    let query_pow_witness = Val::from_u32(cursor.word());
    let leaves: Vec<Val> = (0..queries).map(|_| Val::from_u32(cursor.word())).collect();
    let input_paths: Vec<Vec<[Val; 8]>> = (0..queries)
        .map(|_| (0..query_bits).map(|_| cursor.digest()).collect())
        .collect();
    let mut sibling_values: Vec<Vec<Vec<Challenge>>> = Vec::new();
    let mut round_paths: Vec<Vec<Vec<[Val; 8]>>> = Vec::new();
    for round in 1..=fold_rounds {
        sibling_values.push((0..queries).map(|_| vec![cursor.ext()]).collect());
        round_paths.push(
            (0..queries)
                .map(|_| (0..query_bits - round).map(|_| cursor.digest()).collect())
                .collect(),
        );
    }
    if cursor.at != wire.len() {
        fail("trailing bytes past the schedule");
    }

    // ----- Re-derive the query indices with the pinned challenger,
    // exactly the pre-query prefix the upstream verifier replays. -----
    let perm = default_babybear_poseidon2_16();
    let mut challenger = PlainChallenger::new(perm.clone());
    challenger.observe(Val::from_usize(log_size));
    let commitment: Hash<Val, Val, 8> = Hash::from(core::array::from_fn::<Val, 8, _>(|i| statement[i]));
    let commitment_cap = MerkleCap::new(vec![statement]);
    challenger.observe(commitment_cap.clone());
    let zeta: Challenge = challenger.sample_algebra_element();
    let _ = zeta;
    challenger.observe_algebra_element(opened_value);
    let _alpha: Challenge = challenger.sample_algebra_element();
    let mut betas = Vec::new();
    for cap in &commit_phase_commits {
        challenger.observe(cap.clone());
        let beta: Challenge = challenger.sample_algebra_element();
        betas.push(beta);
    }
    challenger.observe_algebra_element(final_poly[0]);
    for _ in 0..fold_rounds {
        challenger.observe(Val::from_usize(1));
    }
    if !challenger.check_witness(grind_bits, query_pow_witness) {
        println!("upstream grade: rejected (the grinding witness does not meet its target)");
        std::process::exit(2);
    }
    let indices: Vec<usize> = (0..queries)
        .map(|_| challenger.sample_bits(query_bits))
        .collect();
    let _ = commitment;

    // ----- The pruned multiproofs, from indices and full paths. -----
    let input_openings = vec![BatchMultiOpening::<Val, ValMmcs> {
        opened_values: indices
            .iter()
            .zip(&leaves)
            .map(|(_, &leaf)| vec![vec![leaf]])
            .collect(),
        opening_proof: prune(&indices, query_bits, &input_paths),
    }];
    let commit_phase_openings: Vec<CommitPhaseMultiStep<Challenge, ChallengeMmcs>> = (1
        ..=fold_rounds)
        .map(|round| {
            let entries: Vec<usize> = indices.iter().map(|&index| index >> round).collect();
            CommitPhaseMultiStep {
                log_arity: 1,
                sibling_values: sibling_values[round - 1].clone(),
                opening_proof: prune(&entries, query_bits - round, &round_paths[round - 1]),
            }
        })
        .collect();
    let proof: FriProof<Challenge, ChallengeMmcs, Val, Vec<BatchMultiOpening<Val, ValMmcs>>> =
        FriProof {
            commit_phase_commits,
            commit_pow_witnesses: vec![Val::ZERO; fold_rounds],
            input_openings,
            commit_phase_openings,
            final_poly,
            query_pow_witness,
        };

    // ----- The pinned upstream verifier, fresh challenger. -----
    let hash = FieldHash::new(perm.clone());
    let compress = Compress::new(perm.clone());
    let val_mmcs = ValMmcs::new(hash, compress, 0);
    let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
    let pcs = Pcs::new(
        Dft::default(),
        val_mmcs,
        fri_parameters_for(challenge_mmcs, queries, grind_bits),
    );
    let domain =
        <Pcs as PcsTrait<Challenge, PlainChallenger>>::natural_domain_for_degree(&pcs, 1 << log_size);
    let mut verifier_challenger = PlainChallenger::new(perm);
    verifier_challenger.observe(Val::from_usize(log_size));
    verifier_challenger.observe(commitment_cap.clone());
    let verifier_zeta: Challenge = verifier_challenger.sample_algebra_element();
    let rounds = vec![(
        commitment_cap,
        vec![(domain, vec![(verifier_zeta, vec![opened_value])])],
    )];
    match <Pcs as PcsTrait<Challenge, PlainChallenger>>::verify(
        &pcs,
        rounds,
        &proof,
        &mut verifier_challenger,
    ) {
        Ok(()) => println!("upstream grade: accepted the decoded wire at the pinned revision"),
        Err(error) => {
            println!("upstream grade: rejected ({error:?})");
            std::process::exit(2);
        }
    }
}

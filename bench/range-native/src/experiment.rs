//! Seeded fixtures and measurements. Seeds are public research data ONLY.
use crate::{
    EquationReport, Generators, ProverMode, Statement, VerifierMode, baseline::Upstream, evaluate,
    prove,
};
use curve25519_dalek::scalar::Scalar;
use rand_chacha::ChaCha20Rng;
use rand_core::SeedableRng;
use serde_json::{Value, json};
use sha3::{Digest, Sha3_256};
use std::{hint::black_box, time::Instant};

pub const MODES: [VerifierMode; 3] = [
    VerifierMode::Folding,
    VerifierMode::FlatMaterialized,
    VerifierMode::FlatPulledBack,
];
pub const CONTEXT: &[u8]=b"research-only|network=isolated|asset=unit|fee=3|component=range|occurrence=0|generator=bp5-default";

pub fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}
pub fn digest(bytes: &[u8]) -> String {
    hex(&Sha3_256::digest(bytes))
}

pub fn fixture(n: usize, m: usize, seed: u64) -> (Generators, Statement, Vec<u64>, Vec<Scalar>) {
    let gens = Generators::new(n, m).unwrap();
    let max = if n == 64 { u64::MAX } else { (1u64 << n) - 1 };
    let values: Vec<_> = (0..m)
        .map(|j| match j % 4 {
            0 => 0,
            1 => max,
            2 => 1,
            _ => max / 2,
        })
        .collect();
    let mut rng = ChaCha20Rng::seed_from_u64(seed);
    let blindings: Vec<_> = (0..m).map(|_| Scalar::random(&mut rng)).collect();
    let commitments = values
        .iter()
        .zip(&blindings)
        .map(|(v, b)| gens.commit(*v, *b))
        .collect();
    let statement = Statement {
        bits: n,
        count: m,
        context: CONTEXT.to_vec(),
        commitments,
    };
    (gens, statement, values, blindings)
}

pub fn agree(gens: &Generators, s: &Statement, bytes: &[u8]) -> EquationReport {
    let reports = MODES.map(|m| evaluate(gens, s, bytes, m).unwrap());
    assert_eq!(reports[0], reports[1]);
    assert_eq!(reports[0], reports[2]);
    reports[0].clone()
}

fn timed<T>(f: impl FnOnce() -> T) -> u64 {
    let start = Instant::now();
    black_box(f());
    start.elapsed().as_nanos().try_into().unwrap()
}
fn statistics(samples: &[u64]) -> Value {
    let mut sorted = samples.to_vec();
    sorted.sort_unstable();
    json!({"samples_ns":samples,"median_ns":sorted[sorted.len()/2],"min_ns":sorted[0],"max_ns":sorted[sorted.len()-1]})
}

pub fn run_case(n: usize, m: usize, repeats: usize) -> Value {
    eprintln!("range-native: cross-verifying and measuring n={n}, m={m}, repeats={repeats}");
    let seed = 0x52414e4745 + n as u64 * 100 + m as u64;
    let (gens, s, values, blindings) = fixture(n, m, seed);
    let upstream = Upstream::new(n, m);
    let materialized = prove(
        &gens,
        &s,
        &values,
        &blindings,
        &mut ChaCha20Rng::seed_from_u64(seed + 1),
        ProverMode::Materialized,
    )
    .unwrap();
    let pulled = prove(
        &gens,
        &s,
        &values,
        &blindings,
        &mut ChaCha20Rng::seed_from_u64(seed + 1),
        ProverMode::PulledBack,
    )
    .unwrap();
    assert_eq!(
        materialized, pulled,
        "same randomness must give identical full proof bytes"
    );
    let native_report = agree(&gens, &s, &pulled);
    native_report.acceptance().unwrap();
    let up_end = upstream
        .verify(&s, &pulled, &mut ChaCha20Rng::seed_from_u64(seed + 2))
        .unwrap();
    assert_eq!(up_end, native_report.transcript_end);
    let (up_bytes, commitments, up_prove_end) = upstream.prove(
        &s,
        &values,
        &blindings,
        &mut ChaCha20Rng::seed_from_u64(seed + 3),
    );
    assert_eq!(commitments, s.commitments);
    let up_report = agree(&gens, &s, &up_bytes);
    up_report.acceptance().unwrap();
    assert_eq!(up_prove_end, up_report.transcript_end);
    assert_eq!(
        upstream
            .verify(&s, &up_bytes, &mut ChaCha20Rng::seed_from_u64(seed + 4))
            .unwrap(),
        up_report.transcript_end
    );

    // All paths warm up once; rotation counteracts fixed ordering. RNG streams
    // advance throughout timed trials and are outside each timed closure.
    let mut samples: Vec<Vec<u64>> = vec![Vec::new(); 7];
    let mut rngs: Vec<_> = (0..7)
        .map(|i| ChaCha20Rng::seed_from_u64(seed + 100 + i))
        .collect();
    for iteration in 0..=repeats {
        for offset in 0..7 {
            let lane = (offset + iteration) % 7;
            let elapsed = match lane {
                0 => timed(|| {
                    prove(
                        &gens,
                        &s,
                        &values,
                        &blindings,
                        &mut rngs[0],
                        ProverMode::Materialized,
                    )
                    .unwrap()
                }),
                1 => timed(|| {
                    prove(
                        &gens,
                        &s,
                        &values,
                        &blindings,
                        &mut rngs[1],
                        ProverMode::PulledBack,
                    )
                    .unwrap()
                }),
                2..=4 => timed(|| {
                    evaluate(&gens, &s, &pulled, MODES[lane - 2])
                        .unwrap()
                        .acceptance()
                        .unwrap()
                }),
                5 => timed(|| upstream.prove(&s, &values, &blindings, &mut rngs[5])),
                6 => timed(|| upstream.verify(&s, &pulled, &mut rngs[6]).unwrap()),
                _ => unreachable!(),
            };
            if iteration != 0 {
                samples[lane].push(elapsed);
            }
        }
    }
    let mut native_setup = Vec::new();
    let mut upstream_setup = Vec::new();
    for _ in 0..repeats {
        native_setup.push(timed(|| Generators::new(n, m).unwrap()));
        upstream_setup.push(timed(|| Upstream::new(n, m)));
    }
    let names = [
        "prove_materialized",
        "prove_pulled_back",
        "verify_folding",
        "verify_flat_materialized",
        "verify_flat_pulled_back",
        "upstream_prove_context",
        "upstream_verify_randomized_vartime_context",
    ];
    let measurements: serde_json::Map<String, Value> = names
        .iter()
        .zip(&samples)
        .map(|(name, samples)| ((*name).to_owned(), statistics(samples)))
        .collect();
    let med = |i: usize| {
        let mut x = samples[i].clone();
        x.sort_unstable();
        x[x.len() / 2] as f64
    };
    let events: Vec<_>=native_report.events.iter().map(|e|json!({"op":e.operation,"label":e.label,"bytes_hex":hex(&e.bytes),"scalar_le_hex":e.reduced.map(|b|hex(&b))})).collect();
    let gen_bytes: Vec<_> = gens.generator_bytes().into_iter().flatten().collect();
    json!({"bits":n,"count":m,"total":n*m,"proof_bytes":pulled.len(),"seed":seed,
        "public_context_hex":hex(&s.context),"values_research_fixture":values,
        "commitments_hex":s.commitments.iter().map(|b|hex(b)).collect::<Vec<_>>(),
        "native_proof_hex":hex(&pulled),"upstream_proof_hex":hex(&up_bytes),
        "native_proof_sha3_256":digest(&pulled),"upstream_proof_sha3_256":digest(&up_bytes),
        "generator_bytes_sha3_256":digest(&gen_bytes),
        "native_parent_hex":hex(&native_report.parent),"native_Q_hex":hex(&native_report.q),
        "native_range_residual_hex":hex(&native_report.range_residual),"native_ipa_residual_hex":hex(&native_report.ipa_residual),
        "native_transcript_end_hex":hex(&native_report.transcript_end),"upstream_transcript_end_hex":hex(&up_report.transcript_end),
        "native_transcript_events":events,"measurements":measurements,
        "setup":{"native":statistics(&native_setup),"upstream":statistics(&upstream_setup)},
        "ratios":{"prove_pulled_over_materialized":med(1)/med(0),"verify_pulled_over_materialized":med(4)/med(3),
            "verify_pulled_over_folding":med(4)/med(2),"native_pulled_prove_over_upstream_context":med(1)/med(5),
            "native_pulled_verify_over_upstream_context":med(4)/med(6)},
        "source_level_view_accounting":{"eliminated_Hprime_elements":n*m,"eliminated_Hprime_bytes":n*m*std::mem::size_of::<curve25519_dalek::ristretto::RistrettoPoint>(),
            "scope":"one diagonal group-vector materialization; not total allocation, copying, peak memory or fallible-execution equivalence"},
        "checks":{"same_tape_native_modes_identical_bytes":true,"both_crossverification_directions":true,"three_exact_verifiers_same_residuals":true,"upstream_transcript_end_matches":true}})
}

pub fn run(repeats: usize) -> Value {
    assert!(repeats > 0);
    json!({"experiment":"visible-range-reduction-recursive-ipa","profile":"bp5-wire-strict-nonzero-v1",
        "repeats":repeats,"cases":([(8,1),(8,2),(16,4),(32,4),(64,1),(64,16)].map(|(n,m)|run_case(n,m,repeats))),
        "measurement_scope":"release wall-clock; one warmup per lane; rotated order; generators reused; native includes public admission, proof codec and transcript audit collection; upstream includes codec; RNG construction excluded and streams advance; setup separate; concurrent machine load uncontrolled",
        "non_claims":["not completed Goal 3","no maintained compiler integration","no formal security, soundness, zero knowledge or full constant-time claim","seeded RNG is research-only","two deterministic equations are not upstream randomized batching","no total allocation or peak-memory claim","no cross-implementation same-seed proof-byte equality claim"]})
}

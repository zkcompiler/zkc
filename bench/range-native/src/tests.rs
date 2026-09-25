use super::*;
use crate::{
    baseline::Upstream,
    codec::Proof,
    experiment::{MODES, agree, fixture},
    linear::{diagonal_msm, dot, msm, powers},
    prover::prove_core,
    transcript::Flight,
    verifier::evaluate_core,
};
use curve25519_dalek::{ristretto::RistrettoPoint, scalar::Scalar, traits::Identity};
use rand_chacha::ChaCha20Rng;
use rand_core::SeedableRng;

fn rng(seed: u64) -> ChaCha20Rng {
    ChaCha20Rng::seed_from_u64(seed)
}
fn sample() -> (Generators, Statement, Vec<u64>, Vec<Scalar>, Vec<u8>) {
    let (g, s, v, b) = fixture(8, 2, 901);
    let bytes = prove(&g, &s, &v, &b, &mut rng(902), ProverMode::PulledBack).unwrap();
    (g, s, v, b, bytes)
}
fn refused(g: &Generators, s: &Statement, bytes: &[u8], error: Error) {
    for mode in MODES {
        assert_eq!(validate(g, s, bytes, mode), Err(error), "{mode:?}");
    }
}

#[test]
fn bidirectional_interoperability_all_20_profiles() {
    for n in [8, 16, 32, 64] {
        for m in [1, 2, 4, 8, 16] {
            let seed = 7000 + (n * 100 + m) as u64;
            let (g, s, v, b) = fixture(n, m, seed);
            let up = Upstream::new(n, m);
            let bytes = prove(&g, &s, &v, &b, &mut rng(seed + 1), ProverMode::PulledBack).unwrap();
            let direct =
                prove(&g, &s, &v, &b, &mut rng(seed + 1), ProverMode::Materialized).unwrap();
            assert_eq!(bytes, direct, "n={n} m={m}");
            assert_eq!(bytes.len(), 32 * (9 + 2 * (n * m).ilog2() as usize));
            let report = agree(&g, &s, &bytes);
            report.acceptance().unwrap();
            assert_eq!(
                up.verify(&s, &bytes, &mut rng(seed + 2)).unwrap(),
                report.transcript_end
            );
            let (ub, uc, ut) = up.prove(&s, &v, &b, &mut rng(seed + 3));
            assert_eq!(uc, s.commitments);
            let ur = agree(&g, &s, &ub);
            ur.acceptance().unwrap();
            assert_eq!(ut, ur.transcript_end);
            assert_eq!(up.verify(&s, &ub, &mut rng(seed + 4)).unwrap(), ut);
            eprintln!(
                "crossverification n={n} m={m}: two producers, three exact validators, upstream baseline, transcript ends, same-tape native bytes"
            );
        }
    }
}

#[test]
fn exact_generators_and_pedersen_release_correspondence() {
    let g = Generators::new(64, 16).unwrap();
    let up = Upstream::new(64, 16);
    assert_eq!(g.base, up.pc.B);
    assert_eq!(g.blind, up.pc.B_blinding);
    for j in 0..16 {
        let public_g: Vec<_> = up.bp.share(j).G(64).copied().collect();
        assert_eq!(g.g[j * 64..(j + 1) * 64], public_g);
    }
    // H is private upstream: its interoperability is tested through both proof
    // directions, not through a false claim of direct H-array inspection.
    for n in [8, 16, 32] {
        let small = Generators::new(n, 16).unwrap();
        for j in 0..16 {
            assert_eq!(small.g[j * n..(j + 1) * n], g.g[j * 64..j * 64 + n]);
            assert_eq!(small.h[j * n..(j + 1) * n], g.h[j * 64..j * 64 + n]);
        }
    }
    assert_ne!(g.g[0], g.h[0]);
    assert_ne!(g.g[0], g.g[64]);
    assert_eq!(
        g.commit(42, Scalar::from(19u64)),
        up.pc
            .commit(Scalar::from(42u64), Scalar::from(19u64))
            .compress()
            .to_bytes()
    );
}

#[test]
fn invalid_dimensions_counts_context_and_resources() {
    assert_eq!(Dimensions::new(7, 1), Err(Error::Bits));
    for m in [0, 3, 6] {
        assert_eq!(Dimensions::new(8, m), Err(Error::Count));
    }
    assert_eq!(
        Dimensions::new(64, 1usize << (usize::BITS - 1)),
        Err(Error::Overflow)
    );
    assert_eq!(Dimensions::new(64, 512), Err(Error::ResourceLimit));
    let (g, s, v, b, bytes) = sample();
    let mut wrong = s.clone();
    wrong.count = 1;
    refused(&g, &wrong, &bytes, Error::Count);
    wrong = s.clone();
    wrong.commitments.pop();
    refused(&g, &wrong, &bytes, Error::Count);
    wrong = s.clone();
    wrong.context.clear();
    refused(&g, &wrong, &bytes, Error::Context);
    wrong = s.clone();
    wrong.context = vec![0; MAX_CONTEXT_BYTES + 1];
    refused(&g, &wrong, &bytes, Error::Context);
    wrong = s.clone();
    wrong.bits = 16;
    refused(&g, &wrong, &bytes, Error::Shape);
    assert_eq!(
        prove(&g, &s, &v[..1], &b, &mut rng(1), ProverMode::PulledBack),
        Err(Error::Count)
    );
    assert_eq!(
        prove(&g, &s, &v, &b[..1], &mut rng(1), ProverMode::PulledBack),
        Err(Error::Count)
    );
}

#[test]
fn hostile_public_commitments_context_and_parent() {
    let (g, s, v, b, bytes) = sample();
    for mutation in 0..3 {
        let mut wrong = s.clone();
        match mutation {
            0 => {
                wrong.commitments[0] = (decode_point(wrong.commitments[0], false).unwrap() + g.base)
                    .compress()
                    .to_bytes()
            }
            1 => wrong.context.extend_from_slice(b"|occurrence=1"),
            _ => wrong.commitments.swap(0, 1),
        }
        let report = agree(&g, &wrong, &bytes);
        assert!(report.acceptance().is_err());
        assert!(
            Upstream::new(8, 2)
                .verify(&wrong, &bytes, &mut rng(9))
                .is_err()
        );
        if mutation != 1 {
            assert_eq!(
                prove(&g, &wrong, &v, &b, &mut rng(3), ProverMode::PulledBack),
                Err(Error::WitnessCommitment)
            );
        }
    }
    let good = agree(&g, &s, &bytes);
    let wrong_parent = decode_point(good.parent, false).unwrap() + g.base;
    for mode in MODES {
        let report = evaluate_core(
            &g,
            &s,
            &bytes,
            mode,
            Flight::new(&s.context),
            Some(wrong_parent),
        )
        .unwrap();
        assert_eq!(report.range_residual, [0; 32]);
        assert_eq!(report.ipa_residual, g.base.compress().to_bytes());
        assert_eq!(report.acceptance(), Err(Error::IpaEquation));
    }
    // Actual child-byte substitution from an unrelated parent/transcript.
    let other = prove(&g, &s, &v, &b, &mut rng(400), ProverMode::PulledBack).unwrap();
    let mut splice = bytes.clone();
    splice[224..].copy_from_slice(&other[224..]);
    let report = agree(&g, &s, &splice);
    assert_eq!(report.range_residual, [0; 32]);
    assert_eq!(report.acceptance(), Err(Error::IpaEquation));
}

#[test]
fn canonical_codec_rejects_every_scalar_and_point_slot() {
    let (g, s, _, _, bytes) = sample();
    let k = g.dimensions().rounds();
    for slot in [4, 5, 6, 7 + 2 * k, 8 + 2 * k] {
        let mut noncanonical = bytes.clone();
        noncanonical[32 * slot..32 * (slot + 1)].fill(255);
        refused(&g, &s, &noncanonical, Error::NoncanonicalScalar);
        let mut tampered = Proof::parse(&bytes, g.dimensions()).unwrap();
        match slot {
            4 => tampered.tx += Scalar::ONE,
            5 => tampered.tau += Scalar::ONE,
            6 => tampered.mu += Scalar::ONE,
            i if i == 7 + 2 * k => tampered.a += Scalar::ONE,
            _ => tampered.b += Scalar::ONE,
        };
        assert!(agree(&g, &s, &tampered.bytes()).acceptance().is_err());
    }
    for slot in (0..4).chain(7..7 + 2 * k) {
        let mut bad = bytes.clone();
        bad[32 * slot..32 * (slot + 1)].fill(255);
        refused(&g, &s, &bad, Error::CurveEncoding);
        bad[32 * slot..32 * (slot + 1)].fill(0);
        refused(&g, &s, &bad, Error::IdentityPoint);
        let point =
            decode_point(bytes[32 * slot..32 * (slot + 1)].try_into().unwrap(), true).unwrap();
        bad[32 * slot..32 * (slot + 1)].copy_from_slice((point + g.base).compress().as_bytes());
        assert!(agree(&g, &s, &bad).acceptance().is_err());
    }
    let mut wrong = s.clone();
    wrong.commitments[0] = [255; 32];
    refused(&g, &wrong, &bytes, Error::CurveEncoding);
    assert_eq!(Proof::parse(&bytes, g.dimensions()).unwrap().bytes(), bytes);
}

#[test]
fn exact_length_round_count_and_round_order() {
    let (g, s, _, _, bytes) = sample();
    for size in [0, 1, 31, 32, 223, bytes.len() - 1, bytes.len() - 32] {
        refused(&g, &s, &bytes[..size], Error::Length);
    }
    let mut dropped = bytes.clone();
    dropped.drain(224..288);
    refused(&g, &s, &dropped, Error::Length);
    let mut extra = bytes.clone();
    extra.extend_from_slice(&[0; 64]);
    refused(&g, &s, &extra, Error::Length);
    extra = bytes.clone();
    extra.push(0);
    refused(&g, &s, &extra, Error::Length);
    let mut p = Proof::parse(&bytes, g.dimensions()).unwrap();
    p.rounds.reverse();
    assert_eq!(
        agree(&g, &s, &p.bytes()).acceptance(),
        Err(Error::IpaEquation)
    );
    p = Proof::parse(&bytes, g.dimensions()).unwrap();
    p.rounds[0] = (p.rounds[0].1, p.rounds[0].0);
    assert_eq!(
        agree(&g, &s, &p.bytes()).acceptance(),
        Err(Error::IpaEquation)
    );
}

#[test]
fn independent_terminal_obligations_range_and_ipa() {
    let (g, mut s, mut v, b, bytes) = sample();
    let mut terminal = Proof::parse(&bytes, g.dimensions()).unwrap();
    terminal.a += Scalar::ONE;
    let r = agree(&g, &s, &terminal.bytes());
    assert_eq!(r.range_residual, [0; 32]);
    assert_eq!(r.acceptance(), Err(Error::IpaEquation));
    assert_ne!(
        terminal.tx,
        terminal.a * terminal.b,
        "tx=ab is not the IPA terminal equation"
    );
    // Honest admission refuses, then ONLY this test bypasses that one guard.
    v[0] = 256;
    s.commitments[0] = g.commit(v[0], b[0]);
    assert_eq!(
        prove(&g, &s, &v, &b, &mut rng(77), ProverMode::PulledBack),
        Err(Error::WitnessRange)
    );
    let invalid = prove_core(
        &g,
        &s,
        &v,
        &b,
        &mut rng(77),
        ProverMode::PulledBack,
        false,
        Flight::new(&s.context),
    )
    .unwrap();
    let r = agree(&g, &s, &invalid);
    assert_eq!(r.ipa_residual, [0; 32]);
    assert_eq!(r.acceptance(), Err(Error::RangeEquation));
    assert!(
        Upstream::new(8, 2)
            .verify(&s, &invalid, &mut rng(88))
            .is_err()
    );
}

#[test]
fn zero_challenge_policy_injected_at_every_security_site_no_retry() {
    let (g, s, v, b, bytes) = sample();
    for label in ["y", "z", "x", "w", "u"] {
        assert_eq!(
            require_nonzero(label, Scalar::ZERO),
            Err(Error::ZeroChallenge(label))
        );
        for mode in MODES {
            let mut t = Flight::new(&s.context);
            t.inject = Some((label, Scalar::ZERO));
            assert_eq!(
                evaluate_core(&g, &s, &bytes, mode, t, None),
                Err(Error::ZeroChallenge(label))
            );
        }
        let mut t = Flight::new(&s.context);
        t.inject = Some((label, Scalar::ZERO));
        assert_eq!(
            prove_core(&g, &s, &v, &b, &mut rng(6), ProverMode::PulledBack, true, t),
            Err(Error::ZeroChallenge(label))
        );
        let mut t = Flight::new(&s.context);
        t.inject = Some((label, Scalar::ZERO));
        assert_eq!(t.challenge(label), Err(Error::ZeroChallenge(label)));
        assert_eq!(t.events.len(), 1, "one squeeze, no retry");
    }
}

#[test]
fn y_one_and_identity_value_commitment_are_valid() {
    let (g, mut s, mut v, mut b, _) = sample();
    v[0] = 0;
    b[0] = Scalar::ZERO;
    s.commitments[0] = g.commit(0, Scalar::ZERO);
    assert_eq!(s.commitments[0], [0; 32]);
    let bytes = prove(&g, &s, &v, &b, &mut rng(300), ProverMode::PulledBack).unwrap();
    agree(&g, &s, &bytes).acceptance().unwrap();
    Upstream::new(8, 2)
        .verify(&s, &bytes, &mut rng(301))
        .unwrap();
    let (ub, _, _) = Upstream::new(8, 2).prove(&s, &v, &b, &mut rng(302));
    agree(&g, &s, &ub).acceptance().unwrap();
    let mut t = Flight::new(&s.context);
    t.inject = Some(("y", Scalar::ONE));
    let bytes = prove_core(
        &g,
        &s,
        &v,
        &b,
        &mut rng(303),
        ProverMode::PulledBack,
        true,
        t,
    )
    .unwrap();
    for mode in MODES {
        let mut t = Flight::new(&s.context);
        t.inject = Some(("y", Scalar::ONE));
        evaluate_core(&g, &s, &bytes, mode, t, None)
            .unwrap()
            .acceptance()
            .unwrap();
    }
    // Forced y=1 is a helper test, not claimed upstream interoperability.
}

#[test]
fn maximum_u64_witness_and_fresh_rng_progress() {
    let (g, mut s, _, b) = fixture(64, 1, 400);
    let v = [u64::MAX];
    s.commitments[0] = g.commit(v[0], b[0]);
    let mut advancing = rng(401);
    let one = prove(&g, &s, &v, &b, &mut advancing, ProverMode::PulledBack).unwrap();
    let two = prove(&g, &s, &v, &b, &mut advancing, ProverMode::PulledBack).unwrap();
    assert_ne!(one, two);
    for proof in [&one, &two] {
        agree(&g, &s, proof).acceptance().unwrap();
        Upstream::new(64, 1)
            .verify(&s, proof, &mut rng(402))
            .unwrap();
    }
}

#[test]
fn range_polynomial_identity_including_nonbit_residual() {
    for (n, m, y) in [
        (8, 2, Scalar::from(7u64)),
        (16, 4, Scalar::ONE),
        (64, 1, Scalar::from(11u64)),
    ] {
        let z = Scalar::from(13u64);
        let ys = powers(y, n * m);
        let zs = powers(z, m + 3);
        let twos = powers(Scalar::from(2u64), n);
        let mut a: Vec<_> = (0..n * m).map(|i| Scalar::from((i % 2) as u64)).collect();
        a[0] = Scalar::from(2u64); // Bitness term cannot be silently omitted.
        let values: Vec<Scalar> = (0..m).map(|j| Scalar::from((j + 3) as u64)).collect();
        let l: Vec<_> = a.iter().map(|a| a - z).collect();
        let r: Vec<_> = (0..n * m)
            .map(|i| ys[i] * (a[i] - Scalar::ONE + z) + zs[i / n + 2] * twos[i % n])
            .collect();
        let delta = (z - z * z) * ys.iter().sum::<Scalar>()
            - zs[3..m + 3].iter().sum::<Scalar>() * twos.iter().sum::<Scalar>();
        let lhs =
            dot(&l, &r).unwrap() - delta - (0..m).map(|j| zs[j + 2] * values[j]).sum::<Scalar>();
        let bitness = (0..n * m)
            .map(|i| ys[i] * a[i] * (a[i] - Scalar::ONE))
            .sum::<Scalar>();
        let reconstruction = (0..m)
            .map(|j| {
                zs[j + 2] * ((0..n).map(|b| twos[b] * a[j * n + b]).sum::<Scalar>() - values[j])
            })
            .sum::<Scalar>();
        assert_eq!(lhs, bitness + reconstruction);
        assert_ne!(lhs, reconstruction);
    }
}

#[test]
fn checked_contractions_and_nonsymmetric_pullback_controls() {
    let g = Generators::new(8, 1).unwrap();
    let w: Vec<_> = (1u64..=8).map(Scalar::from).collect();
    let f = powers(Scalar::from(7u64), 8);
    let materialized: Vec<_> = g.h.iter().zip(&f).map(|(p, f)| f * p).collect();
    assert_eq!(msm(&w, &materialized), diagonal_msm(&w, &f, &g.h));
    let mut wrong = f.clone();
    wrong.rotate_left(1);
    assert_ne!(msm(&w, &materialized), diagonal_msm(&w, &wrong, &g.h));
    assert_eq!(msm(&w[..7], &g.h), Err(Error::Shape));
    assert_eq!(dot(&w[..7], &f), Err(Error::Shape));
    assert_eq!(diagonal_msm(&w, &f[..7], &g.h), Err(Error::Shape));
    assert_eq!(msm(&[], &[]).unwrap(), RistrettoPoint::identity());
    let u = Scalar::from(9u64);
    let inv = u.invert();
    let folded: Vec<_> = (0..4).map(|i| inv * g.g[i] + u * g.g[i + 4]).collect();
    let weights: Vec<_> = w[..4]
        .iter()
        .map(|a| inv * a)
        .chain(w[..4].iter().map(|a| u * a))
        .collect();
    assert_eq!(msm(&w[..4], &folded), msm(&weights, &g.g));
    let wrong: Vec<_> = w[..4]
        .iter()
        .map(|a| u * a)
        .chain(w[..4].iter().map(|a| inv * a))
        .collect();
    assert_ne!(msm(&w[..4], &folded), msm(&wrong, &g.g));
}

#[test]
fn transcript_literal_replay_and_terminal_continuation_obligation() {
    let (g, s, _, _, bytes) = sample();
    let report = agree(&g, &s, &bytes);
    let p = Proof::parse(&bytes, g.dimensions()).unwrap();
    // Literal independent Merlin schedule: bypass Flight and compare every draw.
    let mut raw = merlin::Transcript::new(b"zkc-goal3-range-native-v1");
    raw.append_message(b"application-context", &s.context);
    raw.append_message(b"dom-sep", b"rangeproof v1");
    raw.append_u64(b"n", 8);
    raw.append_u64(b"m", 2);
    for c in &s.commitments {
        raw.append_message(b"V", c);
    }
    raw.append_message(b"A", p.a_commit.compress().as_bytes());
    raw.append_message(b"S", p.s_commit.compress().as_bytes());
    let mut draws = Vec::new();
    fn draw(t: &mut merlin::Transcript, label: &'static [u8], out: &mut Vec<Vec<u8>>) {
        let mut b = [0; 64];
        t.challenge_bytes(label, &mut b);
        out.push(b.to_vec());
    }
    draw(&mut raw, b"y", &mut draws);
    draw(&mut raw, b"z", &mut draws);
    raw.append_message(b"T_1", p.t1_commit.compress().as_bytes());
    raw.append_message(b"T_2", p.t2_commit.compress().as_bytes());
    draw(&mut raw, b"x", &mut draws);
    raw.append_message(b"t_x", p.tx.as_bytes());
    raw.append_message(b"t_x_blinding", p.tau.as_bytes());
    raw.append_message(b"e_blinding", p.mu.as_bytes());
    draw(&mut raw, b"w", &mut draws);
    raw.append_message(b"dom-sep", b"ipp v1");
    raw.append_u64(b"n", 16);
    for (l, r) in &p.rounds {
        raw.append_message(b"L", l.compress().as_bytes());
        raw.append_message(b"R", r.compress().as_bytes());
        draw(&mut raw, b"u", &mut draws);
    }
    assert_eq!(
        draws,
        report
            .events
            .iter()
            .filter(|e| e.operation == "challenge")
            .map(|e| e.bytes.clone())
            .collect::<Vec<_>>()
    );
    for event in report.events.iter().filter(|e| e.operation == "challenge") {
        assert_eq!(
            event.reduced.unwrap(),
            Scalar::from_bytes_mod_order_wide(&event.bytes.clone().try_into().unwrap()).to_bytes()
        );
    }
    let mut end = [0; 32];
    raw.challenge_bytes(b"research-end-state", &mut end);
    assert_eq!(end, report.transcript_end);
    let mut bad = p.clone();
    bad.a += Scalar::ONE;
    let altered = agree(&g, &s, &bad.bytes());
    assert_eq!(
        report.transcript_end, altered.transcript_end,
        "release does not absorb a,b"
    );
    assert_eq!(altered.acceptance(), Err(Error::IpaEquation));
    // A future enclosing protocol must bind the full child evidence explicitly.
    let bind = |bytes: &[u8]| {
        let mut t = application_transcript(&s.context);
        t.append_message(b"child-proof", bytes);
        let mut out = [0; 32];
        t.challenge_bytes(b"next", &mut out);
        out
    };
    assert_ne!(bind(&bytes), bind(&bad.bytes()));
}

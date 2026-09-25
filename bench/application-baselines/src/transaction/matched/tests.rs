use super::*;

fn fixture() -> (Parameters, Ledger, Transaction, Witness) {
    super::super::tests::fixture()
}
fn prepare(p: Parameters, l: &Ledger, t: &Transaction) -> (Public, Prepared) {
    let p = Public::new(p, l, t).unwrap();
    let s = Prepared::new(&p, l, t).unwrap();
    (p, s)
}
fn frames(proof: &[u8]) -> Vec<std::ops::Range<usize>> {
    let mut pos = MAGIC.len();
    let mut result = Vec::new();
    while pos < proof.len() {
        let length = u32::from_le_bytes(proof[pos..pos + 4].try_into().unwrap()) as usize;
        pos += 4;
        result.push(pos..pos + length);
        pos += length;
    }
    assert_eq!(pos, proof.len());
    result
}
fn error(p: &Public, s: &Prepared, proof: &[u8]) -> String {
    verify(p, s, proof).unwrap_err().to_string()
}

#[test]
fn honest_zero_excess_fresh_proofs_and_no_wire_interop() {
    let (params, l, t, w) = fixture();
    let (p, s) = prepare(params, &l, &t);
    assert_eq!(p.excess, RistrettoPoint::identity());
    let w = Private::new(&p.p, &w).unwrap();
    let a = prove(&p, &s, &w).unwrap();
    let b = prove(&p, &s, &w).unwrap();
    verify(&p, &s, &a).unwrap();
    verify(&p, &s, &b).unwrap();
    assert_ne!(a, b);
    assert_eq!(a.len(), 904);
    assert_eq!(frames(&a).len(), 10 + 2 * 4 + 2 * (1 + p.p.inputs));
    assert!(super::super::verify(&p, &a).is_err());
    let upstream = super::super::prove(&p, &w).unwrap();
    assert_eq!(error(&p, &s, &upstream), "proof-version");
}

#[test]
fn full_width_boundary_amounts() {
    let (mut params, mut l, mut t, mut w) = fixture();
    params.bits = 64;
    t.bits = 64;
    let pc = PedersenGens::default();
    for (i, entry) in l.entries.iter_mut().enumerate() {
        entry.range_bits = 64;
        w.input_values[i] = u64::MAX.to_string();
        let blinding = scalar(&unhex(&w.input_blindings[i]).unwrap()).unwrap();
        entry.commitment = hex(pc
            .commit(Scalar::from(u64::MAX), blinding)
            .compress()
            .as_bytes());
    }
    for (i, value) in [u64::MAX - 1, u64::MAX].into_iter().enumerate() {
        w.values[i] = value.to_string();
        let blinding = scalar(&unhex(&w.blindings[i]).unwrap()).unwrap();
        t.outputs[i] = hex(pc
            .commit(Scalar::from(value), blinding)
            .compress()
            .as_bytes());
    }
    let (p, s) = prepare(params, &l, &t);
    let proof = prove(&p, &s, &Private::new(&p.p, &w).unwrap()).unwrap();
    verify(&p, &s, &proof).unwrap();
}

#[test]
fn private_errors_reach_separate_verifier_equations() {
    for case in 0..5 {
        let (params, l, mut t, mut w) = fixture();
        let expected = match case {
            0 | 1 => {
                w.secrets[case] = hex(Scalar::from(99u64).as_bytes());
                "tx-matched-authorization"
            }
            2 => {
                w.input_blindings[0] = hex(Scalar::from(99u64).as_bytes());
                "tx-matched-balance"
            }
            3 | 4 => {
                let value = if case == 3 { 8u64 } else { 256u64 };
                w.values[0] = value.to_string();
                t.outputs[0] = hex(PedersenGens::default()
                    .commit(Scalar::from(value), Scalar::from(7u64))
                    .compress()
                    .as_bytes());
                if case == 3 {
                    "tx-matched-balance"
                } else {
                    "tx-matched-range"
                }
            }
            _ => unreachable!(),
        };
        let (p, s) = prepare(params, &l, &t);
        let w = Private::new(&p.p, &w).unwrap();
        let proof = prove(&p, &s, &w).unwrap();
        assert_eq!(error(&p, &s, &proof), expected, "case {case}");
    }
}

#[test]
fn opening_guard_is_a_source_producer_rejection() {
    let (params, l, t, mut w) = fixture();
    let (p, s) = prepare(params, &l, &t);
    w.blindings[0] = hex(Scalar::from(99u64).as_bytes());
    let w = Private::new(&p.p, &w).unwrap(); // syntax succeeds
    assert_eq!(
        prove(&p, &s, &w).unwrap_err().to_string(),
        "tx-matched-commitment-sum"
    );
}

#[test]
fn all_equation_guards_and_canonical_messages() {
    let (params, l, t, w) = fixture();
    let (p, s) = prepare(params, &l, &t);
    let proof = prove(&p, &s, &Private::new(&p.p, &w).unwrap()).unwrap();
    let frames = frames(&proof);
    let range_count = 10 + 2 * 4;
    for (index, expected) in [
        (5, "tx-matched-range"),
        (range_count - 1, "tx-matched-ipa"),
        (range_count + 1, "tx-matched-balance"),
        (range_count + 3, "tx-matched-authorization"),
        (range_count + 5, "tx-matched-authorization"),
    ] {
        let mut changed = proof.clone();
        let field = frames[index].clone();
        let value = scalar(&changed[field.clone()]).unwrap() + Scalar::ONE;
        changed[field].copy_from_slice(value.as_bytes());
        assert_eq!(error(&p, &s, &changed), expected, "frame {index}");
    }
    for (index, frame) in frames.iter().enumerate() {
        let mut changed = proof.clone();
        changed[frame.end - 1] ^= 1;
        assert!(verify(&p, &s, &changed).is_err(), "frame {index}");
    }
    for index in [1, 2, 3, 4, 8, 9, 10, 11, 12, 13, 14, 15, 18, 20, 22] {
        let mut changed = proof.clone();
        changed[frames[index].clone()].fill(0);
        assert_eq!(
            error(&p, &s, &changed),
            "tx-matched-identity",
            "point {index}"
        );
    }
    let mut changed = proof.clone();
    changed[frames[5].clone()].fill(0xff);
    assert_eq!(error(&p, &s, &changed), "tx-scalar");
    changed = proof.clone();
    changed[frames[1].clone()].fill(0xff);
    assert_eq!(error(&p, &s, &changed), "tx-point");
    // Equal sums cannot substitute for the ordered point checks.
    changed = proof.clone();
    let first: [u8; 32] = changed[12..44].try_into().unwrap();
    changed.copy_within(44..76, 12);
    changed[44..76].copy_from_slice(&first);
    assert_eq!(error(&p, &s, &changed), "tx-matched-commitment-order");
}

#[test]
fn framing_and_complete_public_root_bindings() {
    let (params, l, t, w) = fixture();
    let (p, s) = prepare(params.clone(), &l, &t);
    let proof = prove(&p, &s, &Private::new(&p.p, &w).unwrap()).unwrap();
    for case in 0..10 {
        let (mut l, mut t) = (l.clone(), t.clone());
        match case {
            0 => t.context.push('x'),
            1 => t.fee = "2".into(),
            2 => l.entries[0].owner = l.entries[1].owner.clone(),
            3 => t.input_ids.swap(0, 1),
            4 => t.outputs.swap(0, 1),
            5 => l.entries[0].commitment = l.entries[1].commitment.clone(),
            6 => {
                t.network.push('x');
                l.network = t.network.clone();
            }
            7 => {
                t.ledger_snapshot.push('x');
                l.snapshot = t.ledger_snapshot.clone();
            }
            8 => {
                l.entries[0].id.push('x');
                t.input_ids[0] = l.entries[0].id.clone();
            }
            9 => {
                // admitted lower prior-range declaration in a 16-bit fixture
                let mut params = params.clone();
                params.bits = 16;
                t.bits = 16;
                let (p, s) = prepare(params, &l, &t);
                assert!(verify(&p, &s, &proof).is_err());
                continue;
            }
            _ => unreachable!(),
        }
        let (p, s) = prepare(params.clone(), &l, &t);
        assert!(verify(&p, &s, &proof).is_err(), "context {case}");
    }
    let mut extra = proof.clone();
    extra.push(0);
    assert_eq!(error(&p, &s, &extra), "proof-trailing-bytes");
    for end in [0, 7, 8, 10, 76, proof.len() - 1] {
        assert!(verify(&p, &s, &proof[..end]).is_err());
    }
    for frame in frames(&proof) {
        let mut bad = proof.clone();
        bad[frame.start - 4..frame.start].copy_from_slice(&u32::MAX.to_le_bytes());
        assert_eq!(error(&p, &s, &bad), "proof-truncated");
    }
}

#[test]
fn finite_power_sums_y_one_and_zero_guard() {
    assert_eq!(
        inverse(Scalar::ZERO).unwrap_err().to_string(),
        "tx-matched-zero-challenge"
    );
    assert_eq!(inverse(Scalar::ONE).unwrap(), Scalar::ONE);
    let (params, l, t, _) = fixture();
    let (p, s) = prepare(params, &l, &t);
    let zs = powers(Scalar::from(2u64), p.p.outputs + 3);
    let state = RangeState {
        a: p.pc.B,
        s: p.pc.B,
        y: Scalar::ONE,
        z: Scalar::from(2u64),
        x: Scalar::ONE,
        w: Scalar::ONE,
        tx: Scalar::ZERO,
        mu: Scalar::ZERO,
    };
    let delta = (state.z - state.z * state.z) * Scalar::from(s.g.len() as u64)
        - zs[3..].iter().sum::<Scalar>() * Scalar::from(255u64);
    // Select T1 to satisfy the independent range equation at y=1.
    let t1 = -delta * p.pc.B - msm(&zs[2..p.p.outputs + 2], &s.outputs) - p.pc.B;
    state.check_range(&p, &s, t1, p.pc.B, Scalar::ZERO).unwrap();
    state.parent(&p, &s).unwrap();
}

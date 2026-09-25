//! Deterministic byte-consuming validator. Both residuals must be identity.
//! Direct folding and flattening are distinct implementations of the IPA check.
use crate::{
    Error, Generators, Result, Statement,
    codec::Proof,
    linear::{diagonal_msm, msm, powers},
    transcript::{Event, Flight},
};
use curve25519_dalek::{ristretto::RistrettoPoint, scalar::Scalar};

#[derive(Clone, Copy, Debug)]
pub enum VerifierMode {
    Folding,
    FlatMaterialized,
    FlatPulledBack,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EquationReport {
    pub range_residual: [u8; 32],
    pub ipa_residual: [u8; 32],
    pub parent: [u8; 32],
    pub q: [u8; 32],
    pub transcript_end: [u8; 32],
    pub events: Vec<Event>,
}
impl EquationReport {
    pub fn acceptance(&self) -> Result<()> {
        if self.range_residual != [0; 32] {
            return Err(Error::RangeEquation);
        }
        if self.ipa_residual != [0; 32] {
            return Err(Error::IpaEquation);
        }
        Ok(())
    }
}

pub fn validate(
    gens: &Generators,
    statement: &Statement,
    proofbytes: &[u8],
    mode: VerifierMode,
) -> Result<()> {
    evaluate(gens, statement, proofbytes, mode)?.acceptance()
}

/// Evaluation of well-formed hostile proofs returns BOTH residuals for research.
/// Callers needing acceptance must call `validate` or `acceptance`.
pub fn evaluate(
    gens: &Generators,
    statement: &Statement,
    proofbytes: &[u8],
    mode: VerifierMode,
) -> Result<EquationReport> {
    evaluate_core(
        gens,
        statement,
        proofbytes,
        mode,
        Flight::new(&statement.context),
        None,
    )
}

pub(crate) fn evaluate_core(
    gens: &Generators,
    statement: &Statement,
    proofbytes: &[u8],
    mode: VerifierMode,
    mut t: Flight,
    parent_override: Option<RistrettoPoint>,
) -> Result<EquationReport> {
    let values = statement.decode(gens)?;
    let d = gens.dimensions();
    let p = Proof::parse(proofbytes, d)?;
    t.range_domain(d, statement);
    t.point("A", p.a_commit)?;
    t.point("S", p.s_commit)?;
    let y = t.challenge("y")?;
    let z = t.challenge("z")?;
    t.point("T_1", p.t1_commit)?;
    t.point("T_2", p.t2_commit)?;
    let x = t.challenge("x")?;
    t.scalar("t_x", p.tx);
    t.scalar("t_x_blinding", p.tau);
    t.scalar("e_blinding", p.mu);
    let w = t.challenge("w")?;
    let q = w * gens.base;
    let ys = powers(y, d.total);
    let invys = powers(y.invert(), d.total);
    let twos = powers(Scalar::from(2u64), d.n);
    let zs = powers(z, d.m + 3);
    // Direct finite sums handle y=1 without division by y-1.
    let delta = (z - z * z) * ys.iter().sum::<Scalar>()
        - zs[3..d.m + 3].iter().sum::<Scalar>() * twos.iter().sum::<Scalar>();
    // E_R is RHS minus LHS, the same orientation as upstream's batching.
    let rw: Vec<_> = [delta - p.tx, -p.tau, x, x * x]
        .into_iter()
        .chain(zs[2..d.m + 2].iter().copied())
        .collect();
    let rb: Vec<_> = [gens.base, gens.blind, p.t1_commit, p.t2_commit]
        .into_iter()
        .chain(values)
        .collect();
    let range_residual = msm(&rw, &rb)?;

    // Actual range parent: never accept an IPA's independently supplied P.
    let h_parent_weights: Vec<_> = (0..d.total)
        .map(|i| z * ys[i] + zs[i / d.n + 2] * twos[i % d.n])
        .collect();
    let h_materialized: Option<Vec<_>> = match mode {
        VerifierMode::FlatPulledBack => None,
        _ => Some(gens.h.iter().zip(&invys).map(|(h, f)| f * h).collect()),
    };
    let h_parent = match &h_materialized {
        Some(h) => msm(&h_parent_weights, h)?,
        None => diagonal_msm(&h_parent_weights, &invys, &gens.h)?,
    };
    let parent = msm(
        &[Scalar::ONE, x, -p.mu, p.tx],
        &[p.a_commit, p.s_commit, gens.blind, q],
    )? + msm(&vec![-z; d.total], &gens.g)?
        + h_parent;
    let actual_parent = parent_override.unwrap_or(parent); // private negative-control injection
    t.ipa_domain(d.total);
    let mut challenges = Vec::with_capacity(d.rounds());
    for (l, r) in &p.rounds {
        t.point("L", *l)?;
        t.point("R", *r)?;
        let u = t.challenge("u")?;
        challenges.push((u, u.invert()));
    }
    let ipa_residual = match mode {
        VerifierMode::Folding => ipa_folding(
            &p,
            actual_parent,
            q,
            &gens.g,
            h_materialized.as_ref().expect("materialized"),
            &challenges,
        )?,
        _ => ipa_flat(
            &p,
            actual_parent,
            q,
            gens,
            h_materialized.as_deref(),
            &invys,
            &challenges,
        )?,
    };
    Ok(EquationReport {
        range_residual: range_residual.compress().to_bytes(),
        ipa_residual: ipa_residual.compress().to_bytes(),
        parent: actual_parent.compress().to_bytes(),
        q: q.compress().to_bytes(),
        transcript_end: t.fingerprint(),
        events: t.events,
    })
}

fn ipa_folding(
    p: &Proof,
    mut parent: RistrettoPoint,
    q: RistrettoPoint,
    g: &[RistrettoPoint],
    h: &[RistrettoPoint],
    challenges: &[(Scalar, Scalar)],
) -> Result<RistrettoPoint> {
    let mut g = g.to_vec();
    let mut h = h.to_vec();
    for ((u, inv), (left, right)) in challenges.iter().zip(&p.rounds) {
        if g.len() != h.len() || g.len() < 2 || !g.len().is_multiple_of(2) {
            return Err(Error::Shape);
        }
        let half = g.len() / 2;
        let mut ng = Vec::with_capacity(half);
        let mut nh = Vec::with_capacity(half);
        for i in 0..half {
            // Intentionally straightforward point arithmetic, independent of
            // prover's two-term MSM implementation and flat scalar expansion.
            ng.push(inv * g[i] + u * g[i + half]);
            nh.push(u * h[i] + inv * h[i + half]);
        }
        parent = parent + (u * u) * left + (inv * inv) * right;
        g = ng;
        h = nh;
    }
    if g.len() != 1 || h.len() != 1 {
        return Err(Error::Shape);
    }
    Ok(parent - (p.a * g[0] + p.b * h[0] + (p.a * p.b) * q))
}

fn ipa_flat(
    p: &Proof,
    parent: RistrettoPoint,
    q: RistrettoPoint,
    gens: &Generators,
    materialized_h: Option<&[RistrettoPoint]>,
    invys: &[Scalar],
    challenges: &[(Scalar, Scalar)],
) -> Result<RistrettoPoint> {
    let n = gens.dimensions().total;
    let k = challenges.len();
    if k != gens.dimensions().rounds() {
        return Err(Error::Shape);
    }
    let mut g_weights = Vec::with_capacity(n);
    let mut h_weights = Vec::with_capacity(n);
    // Explicit MSB-to-LSB index products. No upstream recurrence is reused.
    for i in 0..n {
        let mut s = Scalar::ONE;
        let mut inverse_s = Scalar::ONE;
        for (r, (u, inv)) in challenges.iter().enumerate() {
            if (i >> (k - 1 - r)) & 1 == 0 {
                s *= inv;
                inverse_s *= u;
            } else {
                s *= u;
                inverse_s *= inv;
            }
        }
        g_weights.push(-p.a * s);
        h_weights.push(-p.b * inverse_s);
    }
    let h_term = match materialized_h {
        Some(h) => msm(&h_weights, h)?,
        None => diagonal_msm(&h_weights, invys, &gens.h)?,
    };
    let mut weights = vec![Scalar::ONE, -p.a * p.b];
    let mut points = vec![parent, q];
    for ((u, inv), (l, r)) in challenges.iter().zip(&p.rounds) {
        weights.extend([u * u, inv * inv]);
        points.extend([*l, *r]);
    }
    Ok(msm(&weights, &points)? + msm(&g_weights, &gens.g)? + h_term)
}

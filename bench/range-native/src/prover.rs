//! Independently authored global-vector reduction and recursive IPA.
//! No upstream proof constructor, verifier, or private IPA API is used here.
use crate::{
    Error, Generators, Result, Statement,
    codec::Proof,
    linear::{dot, msm, powers},
    transcript::Flight,
};
use curve25519_dalek::{ristretto::RistrettoPoint, scalar::Scalar};
use rand_core::{CryptoRng, RngCore};

#[derive(Clone, Copy, Debug)]
pub enum ProverMode {
    Materialized,
    PulledBack,
}

/// Fresh masks come from the caller's advancing RNG. Seeding, persistence and
/// session custody are caller responsibilities; this API does not clone RNGs.
pub fn prove<R: RngCore + CryptoRng>(
    gens: &Generators,
    statement: &Statement,
    values: &[u64],
    blindings: &[Scalar],
    rng: &mut R,
    mode: ProverMode,
) -> Result<Vec<u8>> {
    prove_core(
        gens,
        statement,
        values,
        blindings,
        rng,
        mode,
        true,
        Flight::new(&statement.context),
    )
}

// Admission bypass is private and used only by an explicit negative test.
#[allow(clippy::too_many_arguments)]
pub(crate) fn prove_core<R: RngCore + CryptoRng>(
    gens: &Generators,
    statement: &Statement,
    values: &[u64],
    blindings: &[Scalar],
    rng: &mut R,
    mode: ProverMode,
    admit_range: bool,
    mut transcript: Flight,
) -> Result<Vec<u8>> {
    let commitments = statement.decode(gens)?;
    let d = gens.dimensions();
    if values.len() != d.m || blindings.len() != d.m {
        return Err(Error::Count);
    }
    for j in 0..d.m {
        if admit_range && d.n < 64 && values[j] >= (1u64 << d.n) {
            return Err(Error::WitnessRange);
        }
        if gens.commit(values[j], blindings[j]) != commitments[j].compress().to_bytes() {
            return Err(Error::WitnessCommitment);
        }
    }
    transcript.range_domain(d, statement);

    let a_l: Vec<_> = values
        .iter()
        .flat_map(|v| (0..d.n).map(move |b| Scalar::from((v >> b) & 1)))
        .collect();
    let a_r: Vec<_> = a_l.iter().map(|a| a - Scalar::ONE).collect();
    // Deliberately a global-vector draw schedule, not upstream's per-party tape.
    let alpha = Scalar::random(&mut *rng);
    let rho = Scalar::random(&mut *rng);
    let s_l: Vec<_> = (0..d.total).map(|_| Scalar::random(&mut *rng)).collect();
    let s_r: Vec<_> = (0..d.total).map(|_| Scalar::random(&mut *rng)).collect();
    let vector_commit = |a: &[Scalar], b: &[Scalar], mask: Scalar| -> Result<RistrettoPoint> {
        let weights: Vec<_> = a.iter().chain(b).copied().chain([mask]).collect();
        let bases: Vec<_> = gens
            .g
            .iter()
            .chain(&gens.h)
            .copied()
            .chain([gens.blind])
            .collect();
        msm(&weights, &bases)
    };
    let a_commit = vector_commit(&a_l, &a_r, alpha)?;
    let s_commit = vector_commit(&s_l, &s_r, rho)?;
    transcript.point("A", a_commit)?;
    transcript.point("S", s_commit)?;
    let y = transcript.challenge("y")?;
    let z = transcript.challenge("z")?;
    let y_powers = powers(y, d.total);
    let z_powers = powers(z, d.m + 2);
    let twos = powers(Scalar::from(2u64), d.n);
    let l0: Vec<_> = a_l.iter().map(|a| a - z).collect();
    let r0: Vec<_> = (0..d.total)
        .map(|i| y_powers[i] * (a_r[i] + z) + z_powers[i / d.n + 2] * twos[i % d.n])
        .collect();
    let r1: Vec<_> = y_powers.iter().zip(&s_r).map(|(y, s)| y * s).collect();
    // t(X) = <l0 + X*sL, r0 + X*r1>. Cross terms remain visible.
    let t1 = dot(&s_l, &r0)? + dot(&l0, &r1)?;
    let t2 = dot(&s_l, &r1)?;
    let tau1 = Scalar::random(&mut *rng);
    let tau2 = Scalar::random(&mut *rng);
    let t1_commit = msm(&[t1, tau1], &[gens.base, gens.blind])?;
    let t2_commit = msm(&[t2, tau2], &[gens.base, gens.blind])?;
    transcript.point("T_1", t1_commit)?;
    transcript.point("T_2", t2_commit)?;
    let x = transcript.challenge("x")?;
    let l: Vec<_> = l0.iter().zip(&s_l).map(|(a, s)| a + x * s).collect();
    let r: Vec<_> = r0.iter().zip(&r1).map(|(a, s)| a + x * s).collect();
    let tx = dot(&l, &r)?;
    let tau = x * tau1
        + x * x * tau2
        + blindings
            .iter()
            .enumerate()
            .map(|(j, g)| z_powers[j + 2] * g)
            .sum::<Scalar>();
    let mu = alpha + x * rho;
    transcript.scalar("t_x", tx);
    transcript.scalar("t_x_blinding", tau);
    transcript.scalar("e_blinding", mu);
    let w = transcript.challenge("w")?;
    let q = w * gens.base;
    let h_factors = powers(y.invert(), d.total); // y was checked before inversion.
    let (rounds, a, b) = ipa_prove(&mut transcript, q, &gens.g, &gens.h, &h_factors, l, r, mode)?;
    let proof = Proof {
        a_commit,
        s_commit,
        t1_commit,
        t2_commit,
        tx,
        tau,
        mu,
        rounds,
        a,
        b,
    };
    let bytes = proof.bytes();
    // Recheck the public output boundary, including exact rounds and encodings.
    Proof::parse(&bytes, d)?;
    Ok(bytes)
}

type IpaOutput = (Vec<(RistrettoPoint, RistrettoPoint)>, Scalar, Scalar);

#[allow(clippy::too_many_arguments)]
fn ipa_prove(
    t: &mut Flight,
    q: RistrettoPoint,
    original_g: &[RistrettoPoint],
    original_h: &[RistrettoPoint],
    factors: &[Scalar],
    mut a: Vec<Scalar>,
    mut b: Vec<Scalar>,
    mode: ProverMode,
) -> Result<IpaOutput> {
    let n = a.len();
    if !n.is_power_of_two()
        || b.len() != n
        || original_g.len() != n
        || original_h.len() != n
        || factors.len() != n
    {
        return Err(Error::Shape);
    }
    t.ipa_domain(n);
    let mut g = original_g.to_vec();
    let mut h: Vec<_> = match mode {
        ProverMode::Materialized => original_h.iter().zip(factors).map(|(p, f)| f * p).collect(),
        ProverMode::PulledBack => original_h.to_vec(),
    };
    let mut first = true;
    let mut rounds = Vec::with_capacity(n.ilog2() as usize);
    while a.len() > 1 {
        let half = a.len() / 2;
        let (al, ar) = a.split_at(half);
        let (bl, br) = b.split_at(half);
        let (gl, gr) = g.split_at(half);
        let (hl, hr) = h.split_at(half);
        // Only the first round carries the diagonal H view. Subsequent bases
        // are already actual folded points. No dense matrix is constructed.
        let factor = |i: usize| {
            if first && matches!(mode, ProverMode::PulledBack) {
                factors[i]
            } else {
                Scalar::ONE
            }
        };
        let lw: Vec<_> = al
            .iter()
            .copied()
            .chain(br.iter().enumerate().map(|(i, b)| b * factor(i)))
            .chain([dot(al, br)?])
            .collect();
        let rw: Vec<_> = ar
            .iter()
            .copied()
            .chain(bl.iter().enumerate().map(|(i, b)| b * factor(half + i)))
            .chain([dot(ar, bl)?])
            .collect();
        let lp: Vec<_> = gr.iter().chain(hl).copied().chain([q]).collect();
        let rp: Vec<_> = gl.iter().chain(hr).copied().chain([q]).collect();
        let left = msm(&lw, &lp)?;
        let right = msm(&rw, &rp)?;
        t.point("L", left)?;
        t.point("R", right)?;
        let u = t.challenge("u")?;
        let inv = u.invert();
        let mut next_g = Vec::with_capacity(half);
        let mut next_h = Vec::with_capacity(half);
        for i in 0..half {
            next_g.push(msm(&[inv, u], &[gl[i], gr[i]])?);
            next_h.push(msm(
                &[u * factor(i), inv * factor(half + i)],
                &[hl[i], hr[i]],
            )?);
        }
        let next_a = al.iter().zip(ar).map(|(l, r)| u * l + inv * r).collect();
        let next_b = bl.iter().zip(br).map(|(l, r)| inv * l + u * r).collect();
        rounds.push((left, right));
        g = next_g;
        h = next_h;
        a = next_a;
        b = next_b;
        first = false;
    }
    Ok((rounds, a[0], b[0]))
}

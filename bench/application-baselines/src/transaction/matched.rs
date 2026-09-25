//! Direct transcription of the selected transaction's local algorithms.
//! Separate equations, materialized IPA folds, constant-time Dalek MSM.
//! Own public-root transcript/wire; not an interpreter or a security theorem.
use super::*;
use curve25519_dalek::traits::MultiscalarMul;
use sha3::{
    Shake256,
    digest::{ExtendableOutput, Update, XofReader},
};

const MAGIC: &[u8] = b"ZKCTXM01";
const PROFILE: &[u8] = b"direct-tx/pir-matched/1;range+explicit-ipa+balance+all-owners;ct-msm;separate-equations;scalar64le";

pub(super) struct Prepared {
    g: Vec<RistrettoPoint>,
    h: Vec<RistrettoPoint>,
    inputs: Vec<RistrettoPoint>,
    outputs: Vec<RistrettoPoint>,
    fee: Scalar,
    root: Vec<u8>,
    pub(super) generator_setup_seconds: f64,
}
impl Prepared {
    pub(super) fn new(p: &Public, ledger: &Ledger, tx: &Transaction) -> Result<Self> {
        let start = Instant::now();
        let g = (0..p.p.outputs)
            .flat_map(|j| p.bp.share(j).G(p.p.bits).copied())
            .collect::<Vec<_>>();
        // BulletproofGensShare::H is private. This is the existing application
        // helper's fixed upstream generator derivation, using pinned primitives.
        let mut h = Vec::with_capacity(g.len());
        for j in 0..p.p.outputs {
            let mut xof = Shake256::default();
            xof.update(b"GeneratorsChain");
            xof.update(b"H");
            xof.update(&(j as u32).to_le_bytes());
            let mut reader = xof.finalize_xof();
            for _ in 0..p.p.bits {
                let mut uniform = [0; 64];
                XofReader::read(&mut reader, &mut uniform);
                h.push(RistrettoPoint::from_uniform_bytes(&uniform));
            }
        }
        let generator_setup_seconds = start.elapsed().as_secs_f64();
        let inputs = tx
            .input_ids
            .iter()
            .map(|id| {
                let entry = ledger
                    .entries
                    .iter()
                    .find(|e| &e.id == id)
                    .ok_or("tx-missing-input")?;
                point(&unhex(&entry.commitment)?)
            })
            .collect::<Result<_>>()?;
        let outputs = p
            .outputs
            .iter()
            .map(|c| point(c.as_bytes()))
            .collect::<Result<_>>()?;
        let root = serde_json::to_vec(&(
            hex(PROFILE),
            hex(b"zkc/confidential-transaction/1"),
            hex(&p.root),
            g.iter()
                .map(|p| hex(p.compress().as_bytes()))
                .collect::<Vec<_>>(),
            h.iter()
                .map(|p| hex(p.compress().as_bytes()))
                .collect::<Vec<_>>(),
        ))?;
        Ok(Self {
            g,
            h,
            inputs,
            outputs,
            fee: Scalar::from(natural(&tx.fee)?),
            root,
            generator_setup_seconds,
        })
    }
    fn transcript(&self) -> Transcript {
        let mut t = Transcript::new(b"zkc-direct-transaction/pir-matched/1");
        t.append_message(b"public-root", &self.root);
        t
    }
}

fn inverse(x: Scalar) -> Result<Scalar> {
    ensure(x != Scalar::ZERO, "tx-matched-zero-challenge")?;
    Ok(x.invert())
}
fn draw(t: &mut Transcript, label: &'static [u8]) -> Result<Scalar> {
    let mut bytes = [0u8; 64];
    t.challenge_bytes(label, &mut bytes);
    let value = Scalar::from_bytes_mod_order_wide(&bytes);
    inverse(value)?; // DrawChallenge's explicit inverse guard; never resample.
    Ok(value)
}
fn nonidentity(p: RistrettoPoint) -> Result<()> {
    ensure(p != RistrettoPoint::identity(), "tx-matched-identity")
}
fn check_points(a: RistrettoPoint, b: RistrettoPoint) -> Result<()> {
    nonidentity(a)?;
    nonidentity(b)
}
fn powers(x: Scalar, n: usize) -> Vec<Scalar> {
    let mut current = Scalar::ONE;
    (0..n)
        .map(|_| {
            let v = current;
            current *= x;
            v
        })
        .collect()
}
fn scale(a: &[Scalar], x: Scalar) -> Vec<Scalar> {
    a.iter().map(|v| v * x).collect()
}
fn zip(a: &[Scalar], b: &[Scalar], f: impl Fn(Scalar, Scalar) -> Scalar) -> Vec<Scalar> {
    assert_eq!(a.len(), b.len());
    a.iter().zip(b).map(|(a, b)| f(*a, *b)).collect()
}
fn add(a: &[Scalar], b: &[Scalar]) -> Vec<Scalar> {
    zip(a, b, |a, b| a + b)
}
fn sub(a: &[Scalar], b: &[Scalar]) -> Vec<Scalar> {
    zip(a, b, |a, b| a - b)
}
fn mul(a: &[Scalar], b: &[Scalar]) -> Vec<Scalar> {
    zip(a, b, |a, b| a * b)
}
fn dot(a: &[Scalar], b: &[Scalar]) -> Scalar {
    assert_eq!(a.len(), b.len());
    a.iter().zip(b).map(|(a, b)| a * b).sum()
}
fn kronecker(a: &[Scalar], b: &[Scalar]) -> Vec<Scalar> {
    a.iter()
        .flat_map(|a| b.iter().map(move |b| a * b))
        .collect()
}
fn msm(a: &[Scalar], b: &[RistrettoPoint]) -> RistrettoPoint {
    assert_eq!(a.len(), b.len());
    RistrettoPoint::multiscalar_mul(a, b)
}
fn scale_each(a: &[Scalar], b: &[RistrettoPoint]) -> Vec<RistrettoPoint> {
    assert_eq!(a.len(), b.len());
    a.iter().zip(b).map(|(a, b)| a * b).collect()
}
fn group_scale(a: &[RistrettoPoint], b: Scalar) -> Vec<RistrettoPoint> {
    a.iter().map(|a| a * b).collect()
}
fn group_add(a: &[RistrettoPoint], b: &[RistrettoPoint]) -> Vec<RistrettoPoint> {
    assert_eq!(a.len(), b.len());
    a.iter().zip(b).map(|(a, b)| a + b).collect()
}
fn split<T: Clone>(a: &[T]) -> (Vec<T>, Vec<T>) {
    assert!(!a.is_empty() && a.len().is_multiple_of(2));
    (a[..a.len() / 2].to_vec(), a[a.len() / 2..].to_vec())
}
fn check_commitments(actual: &[RistrettoPoint], expected: &[RistrettoPoint]) -> Result<()> {
    ensure(
        actual.len() == expected.len(),
        "tx-matched-commitment-shape",
    )?;
    let ones = vec![Scalar::ONE; expected.len()];
    ensure(
        msm(&ones, actual) == msm(&ones, expected),
        "tx-matched-commitment-sum",
    )?;
    for (a, b) in actual.iter().zip(expected) {
        ensure(a == b, "tx-matched-commitment-order")?;
    }
    Ok(())
}
fn send_point(out: &mut Vec<u8>, t: &mut Transcript, label: &'static [u8], p: RistrettoPoint) {
    send(out, t, label, p.compress().as_bytes());
}
fn send_scalar(out: &mut Vec<u8>, t: &mut Transcript, label: &'static [u8], s: Scalar) {
    send(out, t, label, s.as_bytes());
}
fn receive_point(
    r: &mut Reader<'_>,
    t: &mut Transcript,
    label: &'static [u8],
) -> Result<RistrettoPoint> {
    point(r.message(t, label)?)
}
fn receive_scalar(r: &mut Reader<'_>, t: &mut Transcript, label: &'static [u8]) -> Result<Scalar> {
    scalar(r.message(t, label)?)
}

struct RangeState {
    a: RistrettoPoint,
    s: RistrettoPoint,
    y: Scalar,
    z: Scalar,
    x: Scalar,
    w: Scalar,
    tx: Scalar,
    mu: Scalar,
}
impl RangeState {
    fn parent(
        &self,
        p: &Public,
        prepared: &Prepared,
    ) -> Result<(RistrettoPoint, RistrettoPoint, Vec<Scalar>)> {
        let n = prepared.g.len();
        let factors = powers(inverse(self.y)?, n);
        let ys = powers(self.y, n);
        let zs = powers(self.z, p.p.outputs + 2);
        let z_weights = zs[2..].to_vec();
        let twos = powers(Scalar::from(2u64), p.p.bits);
        let d = kronecker(&z_weights, &twos);
        let zy = scale(&ys, self.z);
        let h_weights = add(&zy, &d);
        let h_prime = scale_each(&factors, &prepared.h);
        let h_term = msm(&h_weights, &h_prime);
        let g_weights = vec![-self.z; n];
        let g_term = msm(&g_weights, &prepared.g);
        let xs = self.x * self.s;
        let mu_term = -self.mu * p.pc.B_blinding;
        let q = self.w * p.pc.B;
        let txq = self.tx * q;
        let parent = self.a + xs + g_term + h_term + mu_term + txq;
        Ok((parent, q, factors))
    }
    fn check_range(
        &self,
        p: &Public,
        prepared: &Prepared,
        t1: RistrettoPoint,
        t2: RistrettoPoint,
        tau: Scalar,
    ) -> Result<()> {
        let ys = powers(self.y, prepared.g.len());
        let twos = powers(Scalar::from(2u64), p.p.bits);
        let zs = powers(self.z, p.p.outputs + 3);
        let delta_zs = zs[3..].to_vec();
        let z_weights = zs[2..p.p.outputs + 2].to_vec();
        let delta = (self.z - self.z * self.z) * ys.iter().sum::<Scalar>()
            - delta_zs.iter().sum::<Scalar>() * twos.iter().sum::<Scalar>();
        let values = msm(&z_weights, &prepared.outputs);
        let delta_b = delta * p.pc.B;
        let xt1 = self.x * t1;
        let x2t2 = (self.x * self.x) * t2;
        let rhs = values + delta_b + xt1 + x2t2;
        let txb = self.tx * p.pc.B;
        let taub = tau * p.pc.B_blinding;
        ensure(txb + taub == rhs, "tx-matched-range")
    }
}

struct IpaVectors {
    a: Vec<Scalar>,
    b: Vec<Scalar>,
    g: Vec<RistrettoPoint>,
    h: Vec<RistrettoPoint>,
}
impl IpaVectors {
    fn cross(&self, q: RistrettoPoint) -> (RistrettoPoint, RistrettoPoint) {
        let (al, ar) = split(&self.a);
        let (bl, br) = split(&self.b);
        let (gl, gr) = split(&self.g);
        let (hl, hr) = split(&self.h);
        let al_gr = msm(&al, &gr);
        let br_hl = msm(&br, &hl);
        let lq = dot(&al, &br) * q;
        let left = al_gr + br_hl + lq;
        let ar_gl = msm(&ar, &gl);
        let bl_hr = msm(&bl, &hr);
        let rq = dot(&ar, &bl) * q;
        (left, ar_gl + bl_hr + rq)
    }
    fn fold(&mut self, u: Scalar) -> Result<()> {
        let inv = inverse(u)?;
        let (al, ar) = split(&self.a);
        let (bl, br) = split(&self.b);
        let (gl, gr) = split(&self.g);
        let (hl, hr) = split(&self.h);
        let ual = scale(&al, u);
        let iar = scale(&ar, inv);
        self.a = add(&ual, &iar);
        let ibl = scale(&bl, inv);
        let ubr = scale(&br, u);
        self.b = add(&ibl, &ubr);
        let igl = group_scale(&gl, inv);
        let ugr = group_scale(&gr, u);
        self.g = group_add(&igl, &ugr);
        let uhl = group_scale(&hl, u);
        let ihr = group_scale(&hr, inv);
        self.h = group_add(&uhl, &ihr);
        Ok(())
    }
}

pub(super) fn prove(p: &Public, prepared: &Prepared, private: &Private) -> Result<Vec<u8>> {
    let mut transcript = prepared.transcript();
    let t = &mut transcript;
    let mut out = MAGIC.to_vec();
    check_points(p.pc.B, p.pc.B_blinding)?;
    let mut commitments = Vec::new();
    for (value, blinding) in private.values.iter().zip(&private.blindings) {
        let value_point = Scalar::from(*value) * p.pc.B;
        let blind_point = blinding * p.pc.B_blinding;
        // curve.append returns a newly allocated vector at each source step.
        let mut next = commitments.clone();
        next.push(value_point + blind_point);
        commitments = next;
    }
    check_commitments(&commitments, &prepared.outputs)?;
    let wire: Vec<_> = commitments
        .iter()
        .flat_map(|p| p.compress().to_bytes())
        .collect();
    send(&mut out, t, b"ordered_commitments", &wire);
    let n = prepared.g.len();
    let al: Vec<_> = private
        .values
        .iter()
        .flat_map(|v| (0..p.p.bits).map(move |j| Scalar::from((v >> j) & 1)))
        .collect();
    let alpha = Scalar::random(&mut OsRng);
    let rho = Scalar::random(&mut OsRng);
    let sl: Vec<_> = (0..n).map(|_| Scalar::random(&mut OsRng)).collect();
    let sr: Vec<_> = (0..n).map(|_| Scalar::random(&mut OsRng)).collect();
    let ones = vec![Scalar::ONE; n];
    let ar = sub(&al, &ones);
    let alg = msm(&al, &prepared.g);
    let arh = msm(&ar, &prepared.h);
    let ab = alpha * p.pc.B_blinding;
    let a = alg + arh + ab;
    let slg = msm(&sl, &prepared.g);
    let srh = msm(&sr, &prepared.h);
    let rb = rho * p.pc.B_blinding;
    let s = slg + srh + rb;
    check_points(a, s)?;
    send_point(&mut out, t, b"range_a", a);
    send_point(&mut out, t, b"range_s", s);
    let y = draw(t, b"range_y")?;
    inverse(y)?;
    let z = draw(t, b"range_z")?;
    inverse(z)?;
    let ys = powers(y, n);
    let zs = powers(z, p.p.outputs + 2);
    let z_weights = zs[2..].to_vec();
    let twos = powers(Scalar::from(2u64), p.p.bits);
    let d = kronecker(&z_weights, &twos);
    let z_vector = vec![z; n];
    let l0 = sub(&al, &z_vector);
    let ar_z = add(&ar, &z_vector);
    let y_ar_z = mul(&ys, &ar_z);
    let r0 = add(&y_ar_z, &d);
    let r1 = mul(&ys, &sr);
    let t1 = dot(&sl, &r0) + dot(&l0, &r1);
    let t2 = dot(&sl, &r1);
    let tau1 = Scalar::random(&mut OsRng);
    let tau2 = Scalar::random(&mut OsRng);
    let first = t1 * p.pc.B + tau1 * p.pc.B_blinding;
    let second = t2 * p.pc.B + tau2 * p.pc.B_blinding;
    check_points(first, second)?;
    send_point(&mut out, t, b"range_t1", first);
    send_point(&mut out, t, b"range_t2", second);
    let x = draw(t, b"range_x")?;
    inverse(x)?;
    let xsl = scale(&sl, x);
    let xr1 = scale(&r1, x);
    let l = add(&l0, &xsl);
    let r = add(&r0, &xr1);
    let tx = dot(&l, &r);
    let tau = x * tau1 + (x * x) * tau2 + dot(&z_weights, &private.blindings);
    let mu = alpha + x * rho;
    send_scalar(&mut out, t, b"range_tx", tx);
    send_scalar(&mut out, t, b"range_tau", tau);
    send_scalar(&mut out, t, b"range_mu", mu);
    let w = draw(t, b"range_w")?;
    inverse(w)?;
    let state = RangeState {
        a,
        s,
        y,
        z,
        x,
        w,
        tx,
        mu,
    };
    let (parent, q, factors) = state.parent(p, prepared)?;
    let h_prime = scale_each(&factors, &prepared.h);
    let a_g = msm(&l, &prepared.g);
    let b_h = msm(&r, &h_prime);
    let ab_q = dot(&l, &r) * q;
    ensure(parent == a_g + b_h + ab_q, "tx-matched-prepare-ipa")?;
    let mut vectors = IpaVectors {
        a: l,
        b: r,
        g: prepared.g.clone(),
        h: h_prime,
    };
    for _ in 0..n.ilog2() {
        let (left, right) = vectors.cross(q);
        check_points(left, right)?;
        send_point(&mut out, t, b"ipa_left", left);
        send_point(&mut out, t, b"ipa_right", right);
        let u = draw(t, b"ipa_challenge")?;
        vectors.fold(u)?;
    }
    ensure(
        vectors.a.len() == 1 && vectors.b.len() == 1,
        "tx-matched-ipa-shape",
    )?;
    send_scalar(&mut out, t, b"ipa_terminal_a", vectors.a[0]);
    send_scalar(&mut out, t, b"ipa_terminal_b", vectors.b[0]);
    let excess_secret =
        private.input_blindings.iter().sum::<Scalar>() - private.blindings.iter().sum::<Scalar>();
    for (i, secret) in std::iter::once(&excess_secret)
        .chain(&private.owners)
        .enumerate()
    {
        t.append_u64(b"schnorr-component", i as u64);
        let base = if i == 0 { p.pc.B_blinding } else { p.pc.B };
        let nonce = Scalar::random(&mut OsRng);
        let point = nonce * base;
        nonidentity(point)?;
        send_point(&mut out, t, b"schnorr_nonce", point);
        let challenge = draw(t, b"schnorr_challenge")?;
        send_scalar(&mut out, t, b"schnorr_response", nonce + challenge * secret);
    }
    Ok(out)
}

pub(super) fn verify(p: &Public, prepared: &Prepared, proof: &[u8]) -> Result<()> {
    let mut r = Reader::new(proof, MAGIC)?;
    let mut transcript = prepared.transcript();
    let t = &mut transcript;
    check_points(p.pc.B, p.pc.B_blinding)?;
    let wire = r.message(t, b"ordered_commitments")?;
    ensure(
        wire.len() == 32 * p.p.outputs,
        "tx-matched-commitment-shape",
    )?;
    let commitments = wire
        .as_chunks::<32>()
        .0
        .iter()
        .map(|b| point(b))
        .collect::<Result<Vec<_>>>()?;
    check_commitments(&commitments, &prepared.outputs)?;
    let a = receive_point(&mut r, t, b"range_a")?;
    let s = receive_point(&mut r, t, b"range_s")?;
    check_points(a, s)?;
    let y = draw(t, b"range_y")?;
    let z = draw(t, b"range_z")?;
    let first = receive_point(&mut r, t, b"range_t1")?;
    let second = receive_point(&mut r, t, b"range_t2")?;
    check_points(first, second)?;
    let x = draw(t, b"range_x")?;
    let tx = receive_scalar(&mut r, t, b"range_tx")?;
    let tau = receive_scalar(&mut r, t, b"range_tau")?;
    let mu = receive_scalar(&mut r, t, b"range_mu")?;
    let w = draw(t, b"range_w")?;
    let state = RangeState {
        a,
        s,
        y,
        z,
        x,
        w,
        tx,
        mu,
    };
    state.check_range(p, prepared, first, second, tau)?;
    let (mut parent, q, factors) = state.parent(p, prepared)?;
    let mut gw = vec![Scalar::ONE];
    let mut hw = vec![Scalar::ONE];
    for _ in 0..prepared.g.len().ilog2() {
        let left = receive_point(&mut r, t, b"ipa_left")?;
        let right = receive_point(&mut r, t, b"ipa_right")?;
        check_points(left, right)?;
        let u = draw(t, b"ipa_challenge")?;
        let inv = inverse(u)?;
        let u2l = (u * u) * left;
        let i2r = (inv * inv) * right;
        parent = parent + u2l + i2r;
        gw = kronecker(&gw, &[inv, u]);
        hw = kronecker(&hw, &[u, inv]);
    }
    let a = receive_scalar(&mut r, t, b"ipa_terminal_a")?;
    let b = receive_scalar(&mut r, t, b"ipa_terminal_b")?;
    ensure(
        gw.len() == prepared.g.len() && hw.len() == prepared.h.len(),
        "tx-matched-ipa-shape",
    )?;
    let a_weights = scale(&gw, a);
    let b_weights = scale(&hw, b);
    let a_g = msm(&a_weights, &prepared.g);
    let h_prime = scale_each(&factors, &prepared.h);
    let b_h = msm(&b_weights, &h_prime);
    let ab_q = (a * b) * q;
    ensure(parent == a_g + b_h + ab_q, "tx-matched-ipa")?;
    // BalanceSubject's two MSMs and three scalar multiplications occur here,
    // after range+IPA, instead of using the admission-time cached excess.
    let input_weights = vec![Scalar::ONE; p.p.inputs];
    let output_weights = vec![Scalar::ONE; p.p.outputs];
    let incoming = msm(&input_weights, &prepared.inputs);
    let outgoing = msm(&output_weights, &prepared.outputs);
    let fee_point = prepared.fee * p.pc.B;
    let negative_outputs = -Scalar::ONE * outgoing;
    let negative_fee = -Scalar::ONE * fee_point;
    let excess = incoming + negative_outputs + negative_fee;
    for (i, subject) in std::iter::once(&excess).chain(&p.owners).enumerate() {
        if i > 0 {
            nonidentity(*subject)?;
        }
        t.append_u64(b"schnorr-component", i as u64);
        let base = if i == 0 { p.pc.B_blinding } else { p.pc.B };
        let nonce = receive_point(&mut r, t, b"schnorr_nonce")?;
        nonidentity(nonce)?;
        let challenge = draw(t, b"schnorr_challenge")?;
        let response = receive_scalar(&mut r, t, b"schnorr_response")?;
        let left = response * base;
        let weighted = challenge * subject;
        ensure(
            left == nonce + weighted,
            if i == 0 {
                "tx-matched-balance"
            } else {
                "tx-matched-authorization"
            },
        )?;
    }
    r.end()
}

#[cfg(test)]
mod tests;

/// Diagnostic export for the existing independently written equation checker.
/// The CLI validates first. This is not a challenge-input verifier API.
pub(super) fn trace(p: &Public, prepared: &Prepared, proof: &[u8]) -> Result<Value> {
    fn event(events: &mut Vec<Value>, tag: u8, label: &[u8], bytes: &[u8]) {
        let mut wire = b"ZKCV\x01".to_vec();
        wire.push(tag);
        if tag == 17 {
            wire.extend_from_slice(&((bytes.len() / 32) as u32).to_le_bytes());
        }
        wire.extend_from_slice(bytes);
        events.push(json!([
            "message",
            "direct-diagnostic",
            hex(label),
            hex(&wire)
        ]));
    }
    fn receive(
        events: &mut Vec<Value>,
        r: &mut Reader<'_>,
        t: &mut Transcript,
        tag: u8,
        label: &'static [u8],
    ) -> Result<()> {
        event(events, tag, label, r.message(t, label)?);
        Ok(())
    }
    fn challenge(events: &mut Vec<Value>, t: &mut Transcript, label: &'static [u8]) -> Result<()> {
        event(events, 13, label, draw(t, label)?.as_bytes());
        Ok(())
    }
    let mut events = Vec::new();
    let mut r = Reader::new(proof, MAGIC)?;
    let mut t = prepared.transcript();
    receive(&mut events, &mut r, &mut t, 17, b"ordered_commitments")?;
    for label in [b"range_a", b"range_s"] {
        receive(&mut events, &mut r, &mut t, 16, label)?;
    }
    for label in [b"range_y", b"range_z"] {
        challenge(&mut events, &mut t, label)?;
    }
    for label in [b"range_t1", b"range_t2"] {
        receive(&mut events, &mut r, &mut t, 16, label)?;
    }
    challenge(&mut events, &mut t, b"range_x")?;
    for label in [b"range_tx".as_slice(), b"range_tau", b"range_mu"] {
        receive(&mut events, &mut r, &mut t, 13, label)?;
    }
    challenge(&mut events, &mut t, b"range_w")?;
    for _ in 0..prepared.g.len().ilog2() {
        receive(&mut events, &mut r, &mut t, 16, b"ipa_left")?;
        receive(&mut events, &mut r, &mut t, 16, b"ipa_right")?;
        challenge(&mut events, &mut t, b"ipa_challenge")?;
    }
    for label in [b"ipa_terminal_a", b"ipa_terminal_b"] {
        receive(&mut events, &mut r, &mut t, 13, label)?;
    }
    for i in 0..=p.p.inputs {
        t.append_u64(b"schnorr-component", i as u64);
        receive(&mut events, &mut r, &mut t, 16, b"schnorr_nonce")?;
        challenge(&mut events, &mut t, b"schnorr_challenge")?;
        receive(&mut events, &mut r, &mut t, 13, b"schnorr_response")?;
    }
    r.end()?;
    Ok(json!({"events":events,"generators":{
        "g":prepared.g.iter().map(|p|hex(p.compress().as_bytes())).collect::<Vec<_>>(),
        "h":prepared.h.iter().map(|p|hex(p.compress().as_bytes())).collect::<Vec<_>>()},
        "scope":"diagnostic only; direct public transcript, not native transcript or wire equivalence"}))
}

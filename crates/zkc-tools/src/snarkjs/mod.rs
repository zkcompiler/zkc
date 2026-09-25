//! Bounded snarkjs 0.7.5 Groth16 BN254 `.zkey` v1 / `.wtns` v2 import.
//!
//! This is a binary-format adapter, not a prover, ceremony validator, or
//! relation checker. Prepared components become ordinary typed kernel values.
//! Contributions (optional section 10) are bounded opaque provenance only.
//! Points use Montgomery R, coefficients R², and witnesses canonical integers.
//! H queries retain snarkjs's odd-coset convention unchanged.
mod binary;
use ark_bn254::{Fq, Fq2, Fr, G1Affine, G2Affine};
use ark_ff::{BigInt, FftField, Field, One, PrimeField, Zero};
use binary::{Cursor, exact_count, reserve, section, sections};
use std::{collections::BTreeMap, path::Path, sync::Arc};
use zkc_arkworks::bn254::{G1, G2};
use zkc_backends::{Policy, Value, matrix::SparseCoo};
use zkc_runtime::interactive::Value as RuntimeValue;

/// Stable importer refusal code. Parsing establishes no setup or relation claim.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Error(pub &'static str);
impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.0)
    }
}
impl std::error::Error for Error {}
pub type Result<T> = std::result::Result<T, Error>;
/// Caller ceilings, further capped by hard implementation limits.
#[derive(Clone, Copy, Debug)]
pub struct Limits {
    pub max_file_bytes: usize,
    pub max_variables: usize,
    pub max_domain_size: usize,
    pub max_coefficients: usize,
    pub max_decoded_bytes: usize,
}
impl Default for Limits {
    fn default() -> Self {
        Self {
            max_file_bytes: 64 << 20,
            max_variables: 32768,
            max_domain_size: 32768,
            max_coefficients: 1 << 20,
            max_decoded_bytes: 128 << 20,
        }
    }
}
impl Limits {
    fn file_bytes(&self) -> usize {
        self.max_file_bytes.min(256 << 20)
    }
    fn variables(&self) -> usize {
        self.max_variables.min(32768)
    }
    fn domain(&self) -> usize {
        self.max_domain_size.min(32768)
    }
    fn coefficients(&self) -> usize {
        self.max_coefficients.min(1 << 20)
    }
    fn decoded(&self, n: usize) -> Result<()> {
        if n > self.max_decoded_bytes.min(256 << 20) {
            Err(Error("import-decoded-limit"))
        } else {
            Ok(())
        }
    }
}
/// Parsed and checked carrier components. Does not authenticate a proving key.
#[derive(Clone, Debug)]
pub struct PreparedKey {
    pub alpha1: G1,
    pub beta1: G1,
    pub beta2: G2,
    pub gamma2: G2,
    pub delta1: G1,
    pub delta2: G2,
    pub ic: Arc<[G1]>,
    pub a_query: Arc<[G1]>,
    pub b1_query: Arc<[G1]>,
    pub b2_query: Arc<[G2]>,
    pub l_query: Arc<[G1]>,
    pub h_query: Arc<[G1]>,
    pub domain_size: usize,
    pub n_public: usize,
    pub n_vars: usize,
    pub qap_a: SparseCoo<Fr>,
    pub qap_b: SparseCoo<Fr>,
    /// Root in natural order; exactly the installed BN254 root convention.
    pub domain_root: Fr,
    /// The 2n-th root used by snarkjs for its odd-coset H inputs.
    pub coset_shift: Fr,
}
impl PreparedKey {
    /// Role-local host bindings. Public/private role admission remains the caller's job.
    pub fn values(&self) -> BTreeMap<String, Value> {
        [
            ("alpha1", Value::Bn254G1(self.alpha1)),
            ("beta1", Value::Bn254G1(self.beta1)),
            ("beta2", Value::Bn254G2(self.beta2)),
            ("gamma2", Value::Bn254G2(self.gamma2)),
            ("delta1", Value::Bn254G1(self.delta1)),
            ("delta2", Value::Bn254G2(self.delta2)),
            ("ic", Value::Bn254G1Vector(self.ic.clone())),
            ("a_query", Value::Bn254G1Vector(self.a_query.clone())),
            ("b1_query", Value::Bn254G1Vector(self.b1_query.clone())),
            ("b2_query", Value::Bn254G2Vector(self.b2_query.clone())),
            ("l_query", Value::Bn254G1Vector(self.l_query.clone())),
            ("h_query", Value::Bn254G1Vector(self.h_query.clone())),
            ("domain_size", Value::Index(self.domain_size as u64)),
            ("n_public", Value::Index(self.n_public as u64)),
            ("n_vars", Value::Index(self.n_vars as u64)),
            ("domain_root", Value::Bn254Field(self.domain_root)),
            ("coset_shift", Value::Bn254Field(self.coset_shift)),
            ("qap_a", Value::Bn254Matrix(self.qap_a.clone())),
            ("qap_b", Value::Bn254Matrix(self.qap_b.clone())),
        ]
        .into_iter()
        .map(|(k, v)| (k.into(), v))
        .collect()
    }
    /// Bind an assignment by cardinality and constant-one convention only.
    pub fn assignment(&self, witness: &Witness) -> Result<Value> {
        if witness.0.first() != Some(&Fr::one()) {
            return Err(Error("import-assignment-one"));
        }
        if witness.0.len() != self.n_vars {
            return Err(Error("import-assignment-length"));
        }
        Ok(Value::Bn254Vector(witness.0.clone()))
    }
}
/// Canonical Fr witness with first element one. No constraint satisfaction claim.
#[derive(Clone, Debug)]
pub struct Witness(pub Arc<[Fr]>);
fn bigint(b: &[u8]) -> Result<BigInt<4>> {
    if b.len() != 32 {
        return Err(Error("import-field-width"));
    }
    let mut words = [0; 4];
    for (w, b) in words.iter_mut().zip(b.as_chunks::<8>().0.iter()) {
        *w = u64::from_le_bytes(*b);
    }
    Ok(BigInt(words))
}
fn field<F: PrimeField<BigInt = BigInt<4>>>(b: &[u8]) -> Result<F> {
    F::from_bigint(bigint(b)?).ok_or(Error("import-noncanonical-field"))
}
fn prime<F: PrimeField<BigInt = BigInt<4>>>(r: &mut Cursor<'_>) -> Result<()> {
    if r.u32()? != 32 {
        return Err(Error("import-field-width"));
    }
    if bigint(r.take(32)?)? != F::MODULUS {
        return Err(Error("import-field-modulus"));
    }
    Ok(())
}
fn g1(b: &[u8], ri: Fq) -> Result<G1> {
    exact_count(b, 1, 64)?;
    let x = field::<Fq>(&b[..32])? * ri;
    let y = field::<Fq>(&b[32..])? * ri;
    if x.is_zero() && y.is_zero() {
        return Ok(G1::identity());
    }
    G1::from_affine(G1Affine::new_unchecked(x, y)).map_err(|_| Error("import-invalid-g1"))
}
fn g2(b: &[u8], ri: Fq) -> Result<G2> {
    exact_count(b, 1, 128)?;
    let mut f = [Fq::zero(); 4];
    for (x, b) in f.iter_mut().zip(b.as_chunks::<32>().0.iter()) {
        *x = field::<Fq>(b)? * ri;
    }
    if f.iter().all(Zero::is_zero) {
        return Ok(G2::identity());
    }
    G2::from_affine(G2Affine::new_unchecked(
        Fq2::new(f[0], f[1]),
        Fq2::new(f[2], f[3]),
    ))
    .map_err(|_| Error("import-invalid-g2"))
}
fn points<T>(
    b: &[u8],
    n: usize,
    width: usize,
    decode: impl Fn(&[u8]) -> Result<T>,
) -> Result<Arc<[T]>> {
    exact_count(b, n, width)?;
    let mut out = reserve(n)?;
    for bytes in b.chunks_exact(width) {
        out.push(decode(bytes)?);
    }
    Ok(out.into())
}
fn matrix(
    mut entries: Vec<(u32, u32, Fr)>,
    rows: usize,
    cols: usize,
    p: &Policy,
) -> Result<SparseCoo<Fr>> {
    entries.sort_unstable_by_key(|e| (e.0, e.1));
    // snarkjs accumulates repeated entries; combine them before canonical COO.
    let mut used = 0;
    for j in 0..entries.len() {
        let e = entries[j];
        if used > 0 && (entries[used - 1].0, entries[used - 1].1) == (e.0, e.1) {
            entries[used - 1].2 += e.2;
        } else {
            entries[used] = e;
            used += 1;
        }
    }
    entries.truncate(used);
    entries.retain(|e| !e.2.is_zero());
    match Value::bn254_matrix(rows, cols, &entries, p).map_err(|_| Error("import-matrix-policy"))? {
        Value::Bn254Matrix(m) => Ok(m),
        _ => unreachable!(),
    }
}
/// Read a bounded file, then decode its exact supported container.
pub fn read_zkey(path: impl AsRef<Path>, limits: &Limits, policy: &Policy) -> Result<PreparedKey> {
    decode_zkey(&binary::read(path.as_ref(), limits)?, limits, policy)
}
/// Read a bounded file, then decode its exact supported witness container.
pub fn read_wtns(path: impl AsRef<Path>, limits: &Limits, policy: &Policy) -> Result<Witness> {
    decode_wtns(&binary::read(path.as_ref(), limits)?, limits, policy)
}
/// Decode Groth16 BN254 only; fail closed on unknown versions, sections and sizes.
pub fn decode_zkey(bytes: &[u8], limits: &Limits, policy: &Policy) -> Result<PreparedKey> {
    let s = sections(bytes, b"zkey", 1, 10, limits)?;
    for id in 1..=9 {
        section(&s, id)?;
    }
    if section(&s, 1)? != 1u32.to_le_bytes() {
        return Err(Error("import-protocol"));
    }
    let mut h = Cursor(section(&s, 2)?);
    prime::<Fq>(&mut h)?;
    prime::<Fr>(&mut h)?;
    let n_vars = h.u32()? as usize;
    let n_public = h.u32()? as usize;
    let domain_size = h.u32()? as usize;
    if n_vars == 0 {
        return Err(Error("import-variable-count"));
    }
    if n_vars > limits.variables() {
        return Err(Error("import-variable-limit"));
    }
    if n_public >= n_vars {
        return Err(Error("import-public-count"));
    }
    if domain_size > limits.domain() {
        return Err(Error("import-domain-limit"));
    }
    if !domain_size.is_power_of_two()
        || domain_size < n_public + 1
        || domain_size.trailing_zeros() >= Fr::TWO_ADICITY
    {
        return Err(Error("import-domain-size"));
    }
    let n_groups = n_vars.max(domain_size).max(n_public + 1);
    if n_groups > policy.max_groups.min(32768)
        || domain_size.max(n_vars) > policy.max_table_elements.min(1 << 20)
    {
        return Err(Error("import-element-policy"));
    }
    // All section lengths and aggregate scratch/retained storage precede allocations.
    for (id, n, w) in [
        (3, n_public + 1, 64),
        (5, n_vars, 64),
        (6, n_vars, 64),
        (7, n_vars, 128),
        (8, n_vars - n_public - 1, 64),
        (9, domain_size, 64),
    ] {
        exact_count(section(&s, id)?, n, w)?;
    }
    let mut c = Cursor(section(&s, 4)?);
    let count = c.u32()? as usize;
    if count > limits.coefficients() {
        return Err(Error("import-coefficient-limit"));
    }
    exact_count(c.0, count, 44)?;
    let estimate = n_vars
        .checked_mul(512)
        .and_then(|x| domain_size.checked_mul(128).and_then(|y| x.checked_add(y)))
        .and_then(|x| count.checked_mul(256).and_then(|y| x.checked_add(y)))
        .and_then(|x| x.checked_add(4096))
        .ok_or(Error("import-size-overflow"))?;
    limits.decoded(estimate)?;
    // Reserve against the caller's per-value policy before reading points or
    // materializing coefficient arrays. The raw coefficient count is a safe
    // upper bound even when duplicate entries later combine or cancel.
    for (n, width) in [
        (n_groups, std::mem::size_of::<G1>()),
        (n_vars, std::mem::size_of::<G2>()),
        (count, std::mem::size_of::<(u32, u32, Fr)>()),
    ] {
        let retained = n
            .checked_mul(width)
            .and_then(|x| x.checked_add(256))
            .ok_or(Error("import-size-overflow"))?;
        if retained > policy.max_value_bytes || policy.max_value_bytes < 512 {
            return Err(Error("import-value-policy"));
        }
    }
    let ri = Fq::from(2).pow([256]).inverse().unwrap();
    let rri2 = Fr::from(2).pow([256]).inverse().unwrap().square();
    let alpha1 = g1(h.take(64)?, ri)?;
    let beta1 = g1(h.take(64)?, ri)?;
    let beta2 = g2(h.take(128)?, ri)?;
    let gamma2 = g2(h.take(128)?, ri)?;
    let delta1 = g1(h.take(64)?, ri)?;
    let delta2 = g2(h.take(128)?, ri)?;
    h.finish()?;
    let mut a = reserve(count)?;
    let mut b = reserve(count)?;
    for _ in 0..count {
        let m = c.u32()?;
        let row = c.u32()?;
        let col = c.u32()?;
        let value = field::<Fr>(c.take(32)?)? * rri2;
        if m > 1 || row as usize >= domain_size || col as usize >= n_vars {
            return Err(Error("import-coefficient-index"));
        }
        (if m == 0 { &mut a } else { &mut b }).push((row, col, value));
    }
    c.finish()?;
    let p = PreparedKey {
        alpha1,
        beta1,
        beta2,
        gamma2,
        delta1,
        delta2,
        ic: points(section(&s, 3)?, n_public + 1, 64, |x| g1(x, ri))?,
        a_query: points(section(&s, 5)?, n_vars, 64, |x| g1(x, ri))?,
        b1_query: points(section(&s, 6)?, n_vars, 64, |x| g1(x, ri))?,
        b2_query: points(section(&s, 7)?, n_vars, 128, |x| g2(x, ri))?,
        l_query: points(section(&s, 8)?, n_vars - n_public - 1, 64, |x| g1(x, ri))?,
        h_query: points(section(&s, 9)?, domain_size, 64, |x| g1(x, ri))?,
        domain_size,
        n_public,
        n_vars,
        qap_a: matrix(a, domain_size, n_vars, policy)?,
        qap_b: matrix(b, domain_size, n_vars, policy)?,
        domain_root: Fr::get_root_of_unity(domain_size as u64)
            .ok_or(Error("import-domain-size"))?,
        coset_shift: Fr::get_root_of_unity((domain_size * 2) as u64)
            .ok_or(Error("import-domain-size"))?,
    };
    for value in p.values().values() {
        if value.retained_bytes() > policy.max_value_bytes {
            return Err(Error("import-value-policy"));
        }
    }
    Ok(p)
}
/// Decode canonical assignment bytes; rejects modular reduction and non-one constant.
pub fn decode_wtns(bytes: &[u8], limits: &Limits, policy: &Policy) -> Result<Witness> {
    let s = sections(bytes, b"wtns", 2, 2, limits)?;
    let mut h = Cursor(section(&s, 1)?);
    prime::<Fr>(&mut h)?;
    let n = h.u32()? as usize;
    h.finish()?;
    if n == 0 {
        return Err(Error("import-variable-count"));
    }
    if n > limits.variables() || n > policy.max_table_elements.min(1 << 20) {
        return Err(Error("import-variable-limit"));
    }
    let body = section(&s, 2)?;
    exact_count(body, n, 32)?;
    limits.decoded(
        n.checked_mul(32)
            .and_then(|x| x.checked_add(256))
            .ok_or(Error("import-size-overflow"))?,
    )?;
    if n * 32 + 256 > policy.max_value_bytes {
        return Err(Error("import-value-policy"));
    }
    let mut out = reserve(n)?;
    for b in body.as_chunks::<32>().0.iter() {
        out.push(field::<Fr>(b)?);
    }
    if out[0] != Fr::one() {
        return Err(Error("import-assignment-one"));
    }
    Ok(Witness(out.into()))
}

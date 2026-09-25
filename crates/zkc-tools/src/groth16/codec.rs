//! Explicit snarkjs 0.7.5 affine JSON adapter. This is not ZKCPRF01.
use super::{Error, Result};
use ark_bn254::{Fq, Fq2, Fr, G1Affine, G2Affine};
use ark_ff::PrimeField;
use ark_serialize::CanonicalDeserialize;
use serde::{Deserialize, Serialize};
use std::sync::Arc;
use zkc_arkworks::bn254::{self, G1, G2};
use zkc_backends::Value;

const FQ_MODULUS: &str =
    "21888242871839275222246405745257275088696311157297823662689037894645226208583";
pub const MAX_JSON_BYTES: usize = 16 * 1024 * 1024;

fn parse<T: serde::de::DeserializeOwned>(bytes: &[u8]) -> Result<T> {
    if bytes.len() > MAX_JSON_BYTES {
        return Err(Error::new("groth16-json-limit"));
    }
    serde_json::from_slice(bytes).map_err(|e| Error::detail("groth16-json", e))
}
fn fq(s: &str) -> Result<Fq> {
    if s.is_empty()
        || !s.bytes().all(|b| b.is_ascii_digit())
        || (s.len() > 1 && s.starts_with('0'))
        || s.len() > FQ_MODULUS.len()
        || (s.len() == FQ_MODULUS.len() && s >= FQ_MODULUS)
    {
        return Err(Error::new("groth16-noncanonical-coordinate"));
    }
    s.parse().map_err(|_| Error::new("groth16-coordinate"))
}
fn g1(p: &[String; 3]) -> Result<G1> {
    if p == &["0", "1", "0"] {
        return Ok(G1::identity());
    }
    if p[2] != "1" {
        return Err(Error::new("groth16-projective-coordinate"));
    }
    G1::from_affine(G1Affine::new_unchecked(fq(&p[0])?, fq(&p[1])?))
        .map_err(|e| Error::detail("groth16-invalid-g1", e))
}
fn g2(p: &[[String; 2]; 3]) -> Result<G2> {
    if p == &[["0", "0"], ["1", "0"], ["0", "0"]] {
        return Ok(G2::identity());
    }
    if p[2] != ["1", "0"] {
        return Err(Error::new("groth16-projective-coordinate"));
    }
    G2::from_affine(G2Affine::new_unchecked(
        Fq2::new(fq(&p[0][0])?, fq(&p[0][1])?),
        Fq2::new(fq(&p[1][0])?, fq(&p[1][1])?),
    ))
    .map_err(|e| Error::detail("groth16-invalid-g2", e))
}
fn dec<F: PrimeField>(x: F) -> String {
    x.into_bigint().to_string()
}
fn out_g1(p: G1) -> Result<[String; 3]> {
    let bytes = p
        .to_bytes()
        .map_err(|e| Error::detail("groth16-point-encoding", e))?;
    let a = G1Affine::deserialize_compressed(&bytes[..])
        .map_err(|e| Error::detail("groth16-point-encoding", e))?;
    Ok(if p == G1::identity() {
        ["0".into(), "1".into(), "0".into()]
    } else {
        [dec(a.x), dec(a.y), "1".into()]
    })
}
fn out_g2(p: G2) -> Result<[[String; 2]; 3]> {
    let bytes = p
        .to_bytes()
        .map_err(|e| Error::detail("groth16-point-encoding", e))?;
    let a = G2Affine::deserialize_compressed(&bytes[..])
        .map_err(|e| Error::detail("groth16-point-encoding", e))?;
    Ok(if p == G2::identity() {
        [
            ["0".into(), "0".into()],
            ["1".into(), "0".into()],
            ["0".into(), "0".into()],
        ]
    } else {
        [
            [dec(a.x.c0), dec(a.x.c1)],
            [dec(a.y.c0), dec(a.y.c1)],
            ["1".into(), "0".into()],
        ]
    })
}
fn protocol(protocol: &str, curve: &str) -> Result<()> {
    if protocol != "groth16" || curve != "bn128" {
        return Err(Error::new("groth16-protocol-or-curve"));
    }
    Ok(())
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct ProofJson {
    pi_a: [String; 3],
    pi_b: [[String; 2]; 3],
    pi_c: [String; 3],
    protocol: String,
    curve: String,
}
/// Canonical subgroup-checked proof points. Fresh proofs usually differ.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Proof {
    pub a: G1,
    pub b: G2,
    pub c: G1,
}
impl Proof {
    /// Require exactly five fields, exact affine shapes, canonical decimal
    /// coordinates, the BN254 prime-order subgroups, and no duplicate keys.
    pub fn from_json(bytes: &[u8]) -> Result<Self> {
        let p: ProofJson = parse(bytes)?;
        protocol(&p.protocol, &p.curve)?;
        Ok(Self {
            a: g1(&p.pi_a)?,
            b: g2(&p.pi_b)?,
            c: g1(&p.pi_c)?,
        })
    }
    /// Compact JSON in pi_a/pi_b/pi_c/protocol/curve order. Coordinate pairs
    /// are (c0,c1), as snarkjs JSON specifies; EVM calldata uses another order.
    pub fn to_json(&self) -> Result<Vec<u8>> {
        serde_json::to_vec(&ProofJson {
            pi_a: out_g1(self.a)?,
            pi_b: out_g2(self.b)?,
            pi_c: out_g1(self.c)?,
            protocol: "groth16".into(),
            curve: "bn128".into(),
        })
        .map_err(|e| Error::detail("groth16-json", e))
    }
    pub(super) fn values(&self) -> [Value; 3] {
        [
            Value::Bn254G1(self.a),
            Value::Bn254G2(self.b),
            Value::Bn254G1(self.c),
        ]
    }
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct KeyJson {
    protocol: String,
    curve: String,
    #[serde(rename = "nPublic")]
    n_public: usize,
    vk_alpha_1: [String; 3],
    vk_beta_2: [[String; 2]; 3],
    vk_gamma_2: [[String; 2]; 3],
    vk_delta_2: [[String; 2]; 3],
    #[serde(rename = "IC")]
    ic: Vec<[String; 3]>,
    // Redundant snarkjs export cache. We validate its finite shape/canonical
    // field elements but do not use it: PIR computes e(alpha,beta) itself.
    vk_alphabeta_12: Option<[[[String; 2]; 3]; 2]>,
}
/// Full effective public verification key; no witness or prover queries.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifyingKey {
    pub(super) alpha1: G1,
    pub(super) beta2: G2,
    pub(super) gamma2: G2,
    pub(super) delta2: G2,
    pub(super) ic: Arc<[G1]>,
}
impl VerifyingKey {
    pub fn from_json(bytes: &[u8]) -> Result<Self> {
        let k: KeyJson = parse(bytes)?;
        protocol(&k.protocol, &k.curve)?;
        if k.n_public >= 32768 || k.ic.len() != k.n_public + 1 {
            return Err(Error::new("groth16-public-count"));
        }
        if let Some(cache) = &k.vk_alphabeta_12 {
            for s in cache.iter().flatten().flatten() {
                fq(s)?;
            }
        }
        Ok(Self {
            alpha1: g1(&k.vk_alpha_1)?,
            beta2: g2(&k.vk_beta_2)?,
            gamma2: g2(&k.vk_gamma_2)?,
            delta2: g2(&k.vk_delta_2)?,
            ic: k.ic.iter().map(g1).collect::<Result<Vec<_>>>()?.into(),
        })
    }
    pub fn from_prepared(k: &crate::snarkjs::PreparedKey) -> Result<Self> {
        if k.n_public >= 32768 || k.ic.len() != k.n_public + 1 {
            return Err(Error::new("groth16-public-count"));
        }
        Ok(Self {
            alpha1: k.alpha1,
            beta2: k.beta2,
            gamma2: k.gamma2,
            delta2: k.delta2,
            ic: k.ic.clone(),
        })
    }
    pub fn n_public(&self) -> usize {
        self.ic.len() - 1
    }
    /// Canonical effective key bytes, excluding the redundant pairing cache.
    pub fn to_json(&self) -> Result<Vec<u8>> {
        serde_json::to_vec(&serde_json::json!({"protocol":"groth16", "curve":"bn128",
            "nPublic":self.n_public(), "vk_alpha_1":out_g1(self.alpha1)?, "vk_beta_2":out_g2(self.beta2)?,
            "vk_gamma_2":out_g2(self.gamma2)?, "vk_delta_2":out_g2(self.delta2)?,
            "IC":self.ic.iter().copied().map(out_g1).collect::<Result<Vec<_>>>()?}))
            .map_err(|e| Error::detail("groth16-json", e))
    }
    pub fn values(&self) -> std::collections::BTreeMap<String, Value> {
        [
            ("alpha1", Value::Bn254G1(self.alpha1)),
            ("beta2", Value::Bn254G2(self.beta2)),
            ("gamma2", Value::Bn254G2(self.gamma2)),
            ("delta2", Value::Bn254G2(self.delta2)),
            ("ic", Value::Bn254G1Vector(self.ic.clone())),
            ("n_public", Value::Index(self.n_public() as u64)),
        ]
        .into_iter()
        .map(|(k, v)| (k.into(), v))
        .collect()
    }
}

/// Ordered canonical public field elements. The key determines cardinality.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Statement(pub Arc<[Fr]>);
impl Statement {
    pub fn from_json(bytes: &[u8]) -> Result<Self> {
        let values: Vec<String> = parse(bytes)?;
        if values.len() >= 32768 {
            return Err(Error::new("groth16-public-count"));
        }
        Ok(Self(
            values
                .iter()
                .map(|s| {
                    bn254::parse_decimal(s)
                        .map_err(|e| Error::detail("groth16-noncanonical-scalar", e))
                })
                .collect::<Result<Vec<_>>>()?
                .into(),
        ))
    }
    pub fn to_json(&self) -> Result<Vec<u8>> {
        serde_json::to_vec(&self.0.iter().copied().map(dec).collect::<Vec<_>>())
            .map_err(|e| Error::detail("groth16-json", e))
    }
}

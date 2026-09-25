//! Immutable native-normalized R1CS adapter and exact snarkjs A/B cross-check.
//! No constraint interpreter: generated PIR checks products/residuals at run time.
use super::{Error, Result, compiler_output, policy};
use crate::snarkjs::PreparedKey;
use ark_bn254::Fr;
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::{path::Path, sync::Arc};
use zkc_backends::{Value, matrix::SparseCoo};

#[derive(Clone, Debug)]
pub struct PreparedRelation {
    identity: String,
    canonical: Arc<[u8]>,
    columns: usize,
    n_public: usize,
    rows: usize,
    matrices: [SparseCoo<Fr>; 3],
}
fn array(j: &Json, n: usize) -> Result<&[Json]> {
    j.as_array()
        .filter(|a| a.len() == n)
        .map(Vec::as_slice)
        .ok_or_else(|| Error::new("groth16-relation-shape"))
}
fn natural(j: &Json) -> Result<usize> {
    let s = j
        .as_str()
        .ok_or_else(|| Error::new("groth16-relation-shape"))?;
    let n = s
        .parse::<usize>()
        .ok()
        .filter(|n| n.to_string() == s)
        .ok_or_else(|| Error::new("groth16-relation-shape"))?;
    if n > 32768 {
        return Err(Error::new("groth16-relation-resource"));
    }
    Ok(n)
}
impl PreparedRelation {
    /// Use the installed compiler's bounded binary R1CS reader and normalization.
    pub fn read(compiler: impl AsRef<Path>, r1cs: impl AsRef<Path>) -> Result<Self> {
        Self::from_normalized(&compiler_output(
            compiler.as_ref(),
            "relation-read",
            r1cs.as_ref(),
        )?)
    }
    /// Native normalized interchange, with exact field, layout and canonical COO.
    pub fn from_normalized(bytes: &[u8]) -> Result<Self> {
        if bytes.len() > super::MAX_JSON_BYTES {
            return Err(Error::new("groth16-relation-limit"));
        }
        let j: Json =
            serde_json::from_slice(bytes).map_err(|e| Error::detail("groth16-relation-json", e))?;
        let a = array(&j, 6)?;
        if a[0] != "zkc.relation.r1cs/1" || a[1] != "bn254.fr" {
            return Err(Error::new("groth16-relation-field"));
        }
        let columns = natural(&a[2])?;
        let n_public = natural(&a[3])?
            .checked_add(natural(&a[4])?)
            .ok_or_else(|| Error::new("groth16-relation-shape"))?;
        let rows = a[5]
            .as_array()
            .ok_or_else(|| Error::new("groth16-relation-shape"))?;
        if rows.len() + n_public + 1 > 32768 {
            return Err(Error::new("groth16-relation-resource"));
        }
        if columns == 0 || columns <= n_public {
            return Err(Error::new("groth16-relation-shape"));
        }
        let mut entries: [Vec<(u32, u32, Fr)>; 3] = Default::default();
        for (row, j) in rows.iter().enumerate() {
            let triple = array(j, 3)?;
            for m in 0..3 {
                for term in triple[m]
                    .as_array()
                    .ok_or_else(|| Error::new("groth16-relation-shape"))?
                {
                    let term = array(term, 2)?;
                    let col = natural(&term[0])?;
                    let scalar = term[1]
                        .as_str()
                        .ok_or_else(|| Error::new("groth16-relation-shape"))?;
                    let scalar = zkc_arkworks::bn254::parse_decimal(scalar)
                        .map_err(|e| Error::detail("groth16-relation-scalar", e))?;
                    entries[m].push((row as u32, col as u32, scalar));
                }
            }
        }
        let mut matrices = Vec::new();
        for e in entries {
            let Value::Bn254Matrix(m) = Value::bn254_matrix(rows.len(), columns, &e, &policy())
                .map_err(|e| {
                    if e.code.starts_with("exhausted:") {
                        Error::detail("groth16-relation-resource", e)
                    } else {
                        super::backend_error(e)
                    }
                })?
            else {
                unreachable!()
            };
            matrices.push(m);
        }
        let mut hash = Sha256::new();
        hash.update(b"zkc.relation-subject/1\n");
        let canonical =
            serde_json::to_vec(&j).map_err(|e| Error::detail("groth16-relation-json", e))?;
        hash.update(&canonical);
        let identity = hash.finalize().iter().map(|x| format!("{x:02x}")).collect();
        Ok(Self {
            identity,
            canonical: canonical.into(),
            columns,
            n_public,
            rows: rows.len(),
            matrices: matrices
                .try_into()
                .map_err(|_| Error::new("groth16-relation-shape"))?,
        })
    }
    pub fn identity(&self) -> &str {
        &self.identity
    }
    /// Exact normalized descriptor, including separate public output/input
    /// counts. Whitespace is immaterial; scalar spellings, order and zero
    /// exclusion were checked before capture. Digest equality is not used here.
    pub fn canonical_descriptor(&self) -> &[u8] {
        &self.canonical
    }
    pub fn matrices(&self) -> &[SparseCoo<Fr>; 3] {
        &self.matrices
    }
    pub fn rows(&self) -> usize {
        self.rows
    }
    pub fn columns(&self) -> usize {
        self.columns
    }
    pub fn n_public(&self) -> usize {
        self.n_public
    }
    pub(super) fn values(&self) -> [Value; 3] {
        self.matrices.clone().map(Value::Bn254Matrix)
    }
    pub(super) fn match_key(&self, key: &PreparedKey) -> Result<()> {
        if key.n_vars != self.columns
            || key.n_public != self.n_public
            || key.domain_size != (self.rows + self.n_public + 1).next_power_of_two().max(2)
        {
            return Err(Error::new("groth16-relation-key-header"));
        }
        let mut a = self.matrices[0].entries().to_vec();
        for i in 0..=self.n_public {
            a.push(((self.rows + i) as u32, i as u32, Fr::from(1)));
        }
        if key.qap_a.entries() != a || key.qap_b.entries() != self.matrices[1].entries() {
            return Err(Error::new("groth16-relation-key-coefficients"));
        }
        Ok(())
    }
    pub(super) fn record(&self) -> Json {
        json!({"format":"zkc.groth16-key-binding/1", "relation":self.identity,
            "convention":"snarkjs-0.7.5-zkey/1",
            "computed":{"field":"bn254.fr","n_vars":self.columns,"n_public":self.n_public,
                "constraints":self.rows,"domain_size":(self.rows+self.n_public+1).next_power_of_two().max(2)},
            "cross_checked":{"zkey_AB_equals_R1CS_AB_with_public_rows":true},
            "external_premises":{"C_IC_H_key_derivation":"unverified",
                "group_queries_and_setup_consistency":"unverified","ceremony":"unverified"}})
    }
}

/// Bound to actual relation identity, not an input file's path spelling.
pub(super) fn valid_identity(s: &str) -> bool {
    s.len() == 64
        && s.bytes()
            .all(|c| c.is_ascii_digit() || (b'a'..=b'f').contains(&c))
}
pub(super) fn retained(relation: PreparedRelation) -> Arc<PreparedRelation> {
    Arc::new(relation)
}

use crate::{Result, codec::*, ensure, source::Source};
use serde_json::{Value, json};
use std::{collections::BTreeMap, path::Path, time::Instant};
use zkc_arkworks::{GroupPoint, ProverKey, Scalar, Table, VerifierKey};
pub struct Input {
    pub root: Value,
    pub groups: Option<[GroupPoint; 4]>,
    pub claim: Option<Scalar>,
    pub public: BTreeMap<String, Vec<u8>>,
    pub vk: Option<VerifierKey>,
    pub pk: Option<ProverKey>,
    pub f: Option<Table>,
    pub g: Option<Table>,
    pub x: Option<Scalar>,
    pub vk_load_ms: f64,
    pub pk_load_ms: f64,
}
impl Input {
    pub fn load(s: &Source, path: &Path, producer: bool) -> Result<Self> {
        let v = json_file(path)?;
        ensure(
            arr(&v)?.len() == 5 && v[0] == "zkc.artifact-inputs/1",
            "input-envelope",
        )?;
        unhex(string(&v[1])?)?;
        let config = arr(&v[4])?;
        ensure(
            config.len() == 4 && config[0] == "zkc.public-configuration/1",
            "configuration",
        )?;
        let keys = arr(&config[1])?;
        let mut vk_load_ms = 0.0;
        let vk = if let Some(n) = s.n {
            ensure(
                config[2] == json!([["V", "expected_f", "vk"], ["V", "expected_g", "vk"]])
                    && config[3] == crate::source::receive_setups(),
                "configuration-setup-selection",
            )?;
            ensure(
                keys.len() == 1
                    && arr(&keys[0])?.len() == 3
                    && keys[0][0] == "vk"
                    && keys[0][1] == "verifier_key:multilinear.kzg.bls12-381/1",
                "configuration-ports",
            )?;
            let bytes = unhex(string(&keys[0][2])?)?;
            // Full VK is APPLICATION input, never read from a candidate proof.
            let now = Instant::now();
            let id = bytes.get(49..81).ok_or("verifier-key-header")?.try_into()?;
            let vk = VerifierKey::from_bytes(&bytes, id, &BOUNDS)?;
            ensure(
                vk.metadata().arity() == n && vk.to_bytes(&BOUNDS)? == bytes,
                "verifier-key-shape",
            )?;
            vk_load_ms = now.elapsed().as_secs_f64() * 1000.0;
            Some(vk)
        } else {
            ensure(
                keys.is_empty() && config[2] == json!([]) && config[3] == json!([]),
                "configuration-ports",
            )?;
            None
        };
        let mut public = BTreeMap::new();
        let mut groups = Vec::new();
        let mut claim = None;
        let mut owned = BTreeMap::new();
        let mut root_public = Vec::new();
        let rows = arr(&v[2])?;
        let declarations = arr(&s.descriptor[4])?;
        ensure(rows.len() == declarations.len(), "public-coverage")?;
        let role = if producer { "P" } else { "V" };
        for (r, d) in rows.iter().zip(declarations) {
            ensure(arr(r)?.len() == 3 && r[0] == d[0], "public-order")?;
            let kind = if s.n.is_some() {
                if r[0] == "claim" {
                    "field:bls12-381.fr"
                } else {
                    "commitment:multilinear.kzg.bls12-381/1"
                }
            } else {
                "group:bls12-381.g1"
            };
            ensure(r[1] == kind, "public-type")?;
            let b = unhex(string(&r[2])?)?;
            match kind {
                "field:bls12-381.fr" => {
                    claim = Some(field(&b)?);
                }
                "group:bls12-381.g1" => {
                    groups.push(point(&b)?);
                }
                _ => {
                    vk.as_ref()
                        .ok_or("missing-vk")?
                        .decode_commitment(body(&b, 6)?, &BOUNDS)?;
                }
            }
            for target in arr(&d[1])? {
                if target[0] == role {
                    owned.insert(string(&target[1])?.to_owned(), (kind.to_owned(), b.clone()));
                }
            }
            public.insert(string(&r[0])?.to_owned(), b);
            root_public.push(json!([r[0], r[1], r[2]]));
        }
        let mut records = BTreeMap::new();
        for r in arr(&v[3])? {
            ensure(arr(r)?.len() >= 3, "input-record")?;
            ensure(
                records.insert(string(&r[0])?.to_owned(), r).is_none(),
                "duplicate-input",
            )?;
        }
        let mut pk = None;
        let mut f = None;
        let mut g = None;
        let mut x = None;
        let mut pk_load_ms = 0.0;
        for (name, r) in &records {
            let kind = string(&r[1])?;
            if let Some((expected_kind, expected)) = owned.get(name) {
                ensure(
                    arr(r)?.len() == 3
                        && kind == expected_kind
                        && unhex(string(&r[2])?)? == *expected,
                    "public-equality",
                )?;
            } else if !producer && name == "vk" && s.n.is_some() {
                ensure(
                    arr(r)?.len() == 3
                        && kind == "verifier_key:multilinear.kzg.bls12-381/1"
                        && r[2] == keys[0][2],
                    "configuration-equality",
                )?;
            } else if producer && s.n.is_some() {
                match name.as_str() {
                    "pk" => {
                        ensure(
                            arr(r)?.len() == 5 && kind == "prover_key_file" && r[4] == "vk",
                            "prover-record",
                        )?;
                        let pin = unhex(string(&r[3])?)?
                            .try_into()
                            .map_err(|_| "material-pin-length")?;
                        let now = Instant::now();
                        // Match host: absolute paths or paths relative to process CWD.
                        let bytes = read(Path::new(string(&r[2])?), LIMIT)?;
                        pk = Some(ProverKey::from_bytes(
                            &bytes,
                            pin,
                            vk.as_ref().ok_or("missing-vk")?,
                            &BOUNDS,
                        )?);
                        pk_load_ms = now.elapsed().as_secs_f64() * 1000.0;
                    }
                    "f" | "g" => {
                        ensure(
                            arr(r)?.len() == 3 && kind == "table:bls12-381.fr",
                            "table-record",
                        )?;
                        let t = decode_table(&unhex(string(&r[2])?)?)?;
                        ensure(Some(t.arity()) == s.n, "table-arity")?;
                        if name == "f" {
                            f = Some(t)
                        } else {
                            g = Some(t)
                        }
                    }
                    _ => return Err("unknown-input".into()),
                }
            } else if producer && s.n.is_none() {
                ensure(arr(r)?.len() == 3, "input-record")?;
                match name.as_str() {
                    "x" => {
                        ensure(kind == "field:bls12-381.fr", "witness-type")?;
                        x = Some(field(&unhex(string(&r[2])?)?)?);
                    }
                    "nonce_first" | "nonce_second" => {
                        ensure(kind == "nonce", "nonce-type")?;
                        let text = string(&r[2])?;
                        let n: u64 = text.parse()?;
                        ensure(
                            (2..=1_000_000).contains(&n) && n.to_string() == text,
                            "nonce-budget",
                        )?;
                    }
                    _ => return Err("unknown-input".into()),
                }
            } else {
                return Err("validator-private-or-unknown-input".into());
            }
        }
        if producer {
            if s.n.is_some() {
                ensure(
                    pk.is_some() && f.is_some() && g.is_some(),
                    "missing-producer-input",
                )?;
            } else {
                ensure(
                    x.is_some()
                        && records.contains_key("nonce_first")
                        && records.contains_key("nonce_second"),
                    "missing-producer-input",
                )?;
            }
        }
        let root = json!([
            "zkc.artifact-binding/1",
            s.source,
            s.descriptor,
            v[1],
            root_public,
            v[4]
        ]);
        let groups = if s.n.is_none() {
            Some(groups.try_into().map_err(|_| "group-input-count")?)
        } else {
            None
        };
        Ok(Self {
            root,
            groups,
            claim,
            public,
            vk,
            pk,
            f,
            g,
            x,
            vk_load_ms,
            pk_load_ms,
        })
    }
    pub fn public(&self, name: &str) -> Result<&[u8]> {
        Ok(self.public.get(name).ok_or("public-missing")?)
    }
}

use crate::{Result, codec::*, source::Source};
use serde_json::{Value, json};
use std::{fs, path::Path, time::Instant};
use zkc_arkworks::{GroupPoint, Keys, Scalar, Table};
pub fn generate(
    s: &Source,
    source_path: &Path,
    descriptor_path: &Path,
    dir: &Path,
) -> Result<Value> {
    fs::create_dir(dir)?;
    fs::create_dir(dir.join("producer"))?;
    fs::create_dir(dir.join("validator"))?;
    fs::copy(source_path, dir.join("source.json"))?;
    fs::copy(descriptor_path, dir.join("descriptor.json"))?;
    let start = Instant::now();
    let (public, records, config, detail) = if let Some(n) = s.n {
        let keys = Keys::setup_for_development(n, &BOUNDS)?;
        let f = Table::from_logical_vec(
            (0..1usize << n)
                .map(|i| Scalar::from((i * i + 3 * i + 5) as u64))
                .collect(),
            &BOUNDS,
        )?;
        let g = Table::from_logical_vec(
            (0..1usize << n)
                .map(|i| Scalar::from((2 * i * i + 7 * i + 11) as u64))
                .collect(),
            &BOUNDS,
        )?;
        let cf = keys.prover_key().commit(&f)?;
        let cg = keys.prover_key().commit(&g)?;
        let vk = keys.verifier_key().to_bytes(&BOUNDS)?;
        let pk = keys.prover_key().to_bytes(&BOUNDS)?;
        fs::write(dir.join("producer/prover-key.bin"), &pk)?;
        let pin = hex(&keys.prover_key().material_fingerprint());
        (
            json!([
                [
                    "claim",
                    "field:bls12-381.fr",
                    hex(&scalar(f.product_boolean_sum(&g)?)?)
                ],
                [
                    "expected_f",
                    "commitment:multilinear.kzg.bls12-381/1",
                    hex(&wire(6, &cf.commitment().to_bytes(&BOUNDS)?))
                ],
                [
                    "expected_g",
                    "commitment:multilinear.kzg.bls12-381/1",
                    hex(&wire(6, &cg.commitment().to_bytes(&BOUNDS)?))
                ]
            ]),
            json!([
                [
                    "pk",
                    "prover_key_file",
                    fs::canonicalize(dir.join("producer/prover-key.bin"))?
                        .to_str()
                        .ok_or("key-path-utf8")?,
                    pin,
                    "vk"
                ],
                ["f", "table:bls12-381.fr", hex(&table(&f)?)],
                ["g", "table:bls12-381.fr", hex(&table(&g)?)]
            ]),
            json!([
                "zkc.public-configuration/1",
                [["vk", "verifier_key:multilinear.kzg.bls12-381/1", hex(&vk)]],
                [["V", "expected_f", "vk"], ["V", "expected_g", "vk"]],
                crate::source::receive_setups()
            ]),
            json!({"n":n,"f":"i*i+3*i+5","g":"2*i*i+7*i+11","logical_layout":"MSB-first, library bit reversal on ingress","material_fingerprint":pin,"pk_sha256":hash(&pk),"vk_sha256":hash(&vk),"key_id":hex(&keys.verifier_key().metadata().key_id())}),
        )
    } else {
        let x = Scalar::from(19u64);
        let b0 = GroupPoint::generator().scale(Scalar::from(7u64));
        let b1 = GroupPoint::generator().scale(Scalar::from(11u64));
        (
            json!([
                ["base_0", "group:bls12-381.g1", hex(&group(b0)?)],
                ["base_1", "group:bls12-381.g1", hex(&group(b1)?)],
                ["image_0", "group:bls12-381.g1", hex(&group(b0.scale(x))?)],
                ["image_1", "group:bls12-381.g1", hex(&group(b1.scale(x))?)]
            ]),
            json!([
                ["x", "field:bls12-381.fr", hex(&scalar(x)?)],
                ["nonce_first", "nonce", "2"],
                ["nonce_second", "nonce", "2"]
            ]),
            json!(["zkc.public-configuration/1", [], [], []]),
            json!({"public_fixture_witness":"19","base_multipliers":[7,11],"native_nonces":"OS issuance; commit and response consume two transitions each","direct_development_nonces":{"encoding":"64BE-mod-Fr","first":hex(&[0xa5;64]),"second":hex(&[0x5a;64])}}),
        )
    };
    let context = hex(b"zkc Goal2 public development fixture v1");
    write_json(
        &dir.join("producer/inputs.json"),
        &json!(["zkc.artifact-inputs/1", context, public, records, config]),
    )?;
    write_json(
        &dir.join("validator/inputs.json"),
        &json!(["zkc.artifact-inputs/1", context, public, [], config]),
    )?;
    let report = json!({"status":"fixture-generated","development_only":true,"source_sha256":s.source_hash,"descriptor_sha256":s.descriptor_hash,"setup_and_fixture_ms":start.elapsed().as_secs_f64()*1000.0,"detail":detail,"setup":if s.n.is_some(){"OS development setup persisted once; fresh generation changes PK/VK and roots; retained fixture supports exact deterministic proof reproduction"}else{"no setup; native OS nonce issuance; direct public deterministic development fixture"}});
    write_json(&dir.join("fixture.json"), &report)?;
    Ok(report)
}

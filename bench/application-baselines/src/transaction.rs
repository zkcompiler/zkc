//! Direct upstream range proof followed by actual excess and owner proofs.
mod matched;

use crate::*;
use bulletproofs::{BulletproofGens, PedersenGens, RangeProof};
use curve25519_dalek::{
    ristretto::{CompressedRistretto, RistrettoPoint},
    scalar::Scalar,
    traits::Identity,
};
use rand_core::OsRng;
use std::{collections::BTreeSet, time::Instant};
const MAGIC: &[u8] = b"ZKCTXD01";
const SOURCE: &[u8] =
    b"direct-tx/1;bp=5.0.0;dalek=4.1.3;range+excessH+ownersG;prior-ranged-ledger;no-wire-interop";
fn read_tx<T: for<'de> Deserialize<'de>>(path: &str) -> Result<T> {
    Ok(serde_json::from_slice(&bounded_bytes(path, 4 << 20)?)?)
}
#[derive(Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Parameters {
    bits: usize,
    outputs: usize,
    inputs: usize,
}
#[derive(Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Entry {
    id: String,
    commitment: String,
    owner: String,
    range_bits: usize,
}
#[derive(Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Ledger {
    snapshot: String,
    network: String,
    entries: Vec<Entry>,
}
#[derive(Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Transaction {
    version: u32,
    network: String,
    context: String,
    ledger_snapshot: String,
    bits: usize,
    input_ids: Vec<String>,
    outputs: Vec<String>,
    fee: String,
}
#[derive(Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Witness {
    input_values: Vec<String>,
    input_blindings: Vec<String>,
    values: Vec<String>,
    blindings: Vec<String>,
    secrets: Vec<String>,
}
fn natural(s: &str) -> Result<u64> {
    ensure(
        !s.is_empty()
            && (s.len() == 1 || !s.starts_with('0'))
            && s.bytes().all(|v| v.is_ascii_digit()),
        "tx-natural",
    )?;
    Ok(s.parse()?)
}
fn point(data: &[u8]) -> Result<RistrettoPoint> {
    let compressed = CompressedRistretto(data.try_into().map_err(|_| "tx-point-length")?);
    let p = compressed.decompress().ok_or("tx-point")?;
    ensure(p.compress() == compressed, "tx-canonical-point")?;
    Ok(p)
}
fn scalar(data: &[u8]) -> Result<Scalar> {
    Option::from(Scalar::from_canonical_bytes(
        data.try_into().map_err(|_| "tx-scalar-length")?,
    ))
    .ok_or_else(|| "tx-scalar".into())
}
fn label(s: &str) -> Result<()> {
    ensure(
        !s.is_empty() && s.len() <= 256 && s.bytes().all(|b| b.is_ascii_graphic()),
        "tx-label",
    )
}
struct Public {
    p: Parameters,
    bp: BulletproofGens,
    pc: PedersenGens,
    outputs: Vec<CompressedRistretto>,
    owners: Vec<RistrettoPoint>,
    excess: RistrettoPoint,
    root: Vec<u8>,
    generator_setup_seconds: f64,
}
impl Public {
    fn new(p: Parameters, ledger: &Ledger, tx: &Transaction) -> Result<Self> {
        ensure(
            [8, 16, 32, 64].contains(&p.bits)
                && p.outputs.is_power_of_two()
                && p.outputs >= 2
                && p.outputs <= 16384 / p.bits
                && (1..=256).contains(&p.inputs),
            "tx-parameters",
        )?;
        ensure(
            tx.bits == p.bits && tx.outputs.len() == p.outputs && tx.input_ids.len() == p.inputs,
            "tx-shape",
        )?;
        for s in [
            &tx.network,
            &tx.context,
            &tx.ledger_snapshot,
            &ledger.snapshot,
            &ledger.network,
        ] {
            label(s)?;
        }
        ensure(
            tx.version == 1
                && tx.network == ledger.network
                && tx.ledger_snapshot == ledger.snapshot,
            "tx-context",
        )?;
        let fee = natural(&tx.fee)?;
        let max = (1u128 << p.bits) - 1;
        ensure(
            u128::from(fee) <= max
                && p.inputs as u128 * max < 1u128 << 80
                && (p.outputs as u128 + 1) * max < 1u128 << 80,
            "tx-integer-bound",
        )?;
        ensure(ledger.entries.len() <= 4096, "tx-ledger-size")?;
        let mut ids = BTreeSet::new();
        for e in &ledger.entries {
            label(&e.id)?;
            ensure(ids.insert(&e.id), "tx-duplicate-ledger")?;
            point(&unhex(&e.commitment)?)?;
            ensure(
                point(&unhex(&e.owner)?)? != RistrettoPoint::identity(),
                "tx-owner-identity",
            )?;
            ensure([8, 16, 32, 64].contains(&e.range_bits), "tx-prior-range")?;
        }
        let mut seen = BTreeSet::new();
        let mut selected = Vec::new();
        for id in &tx.input_ids {
            label(id)?;
            ensure(seen.insert(id), "tx-duplicate-input")?;
            let e = ledger
                .entries
                .iter()
                .find(|e| &e.id == id)
                .ok_or("tx-missing-input")?;
            ensure(e.range_bits <= p.bits, "tx-prior-range")?;
            selected.push(e);
        }
        let start = Instant::now();
        let pc = PedersenGens::default();
        let bp = BulletproofGens::new(p.bits, p.outputs);
        let generator_setup_seconds = start.elapsed().as_secs_f64();
        let mut excess = -Scalar::from(fee) * pc.B;
        let mut owners = Vec::new();
        for e in &selected {
            excess += point(&unhex(&e.commitment)?)?;
            owners.push(point(&unhex(&e.owner)?)?);
        }
        let mut outputs = Vec::new();
        for c in &tx.outputs {
            let c = point(&unhex(c)?)?;
            excess -= c;
            outputs.push(c.compress());
        }
        // Canonical typed serialization binds all selected ledger facts and parameters.
        let root = serde_json::to_vec(&(
            hex(SOURCE),
            &p,
            tx,
            selected,
            hex(pc.B.compress().as_bytes()),
            hex(pc.B_blinding.compress().as_bytes()),
            "bulletproofs-5.0.0-default",
        ))?;
        Ok(Self {
            p,
            bp,
            pc,
            outputs,
            owners,
            excess,
            root,
            generator_setup_seconds,
        })
    }
    fn transcript(&self) -> Transcript {
        let mut t = Transcript::new(b"zkc-direct-transaction/1");
        t.append_message(b"public-root", &self.root);
        t
    }
}
struct Private {
    values: Vec<u64>,
    blindings: Vec<Scalar>,
    excess: Scalar,
    input_blindings: Vec<Scalar>,
    owners: Vec<Scalar>,
}
impl Private {
    fn new(p: &Parameters, w: &Witness) -> Result<Self> {
        ensure(
            w.values.len() == p.outputs
                && w.blindings.len() == p.outputs
                && w.input_values.len() == p.inputs
                && w.input_blindings.len() == p.inputs
                && w.secrets.len() == p.inputs,
            "tx-witness-shape",
        )?;
        // Syntax only; no conservation, opening, range, or owner relation gate.
        for v in &w.input_values {
            natural(v)?;
        }
        let values = w
            .values
            .iter()
            .map(|v| natural(v))
            .collect::<Result<Vec<_>>>()?;
        let blindings = w
            .blindings
            .iter()
            .map(|v| scalar(&unhex(v)?))
            .collect::<Result<Vec<_>>>()?;
        let inputs = w
            .input_blindings
            .iter()
            .map(|v| scalar(&unhex(v)?))
            .collect::<Result<Vec<_>>>()?;
        let owners = w
            .secrets
            .iter()
            .map(|v| scalar(&unhex(v)?))
            .collect::<Result<Vec<_>>>()?;
        let excess = inputs.iter().sum::<Scalar>() - blindings.iter().sum::<Scalar>();
        Ok(Self {
            values,
            blindings,
            excess,
            input_blindings: inputs,
            owners,
        })
    }
}
fn challenge(t: &mut Transcript) -> Scalar {
    let mut b = [0u8; 64];
    t.challenge_bytes(b"schnorr-challenge", &mut b);
    Scalar::from_bytes_mod_order_wide(&b)
}
fn prove(p: &Public, w: &Private) -> Result<Vec<u8>> {
    let mut t = p.transcript();
    let mut out = MAGIC.to_vec();
    // Upstream performs fused range/IPA. Its transcript is a domain-separated fork;
    // the whole serialized range proof then enters the application transcript.
    let mut range_t = t.clone();
    range_t.append_message(b"component", b"output-range");
    let (range, _) = RangeProof::prove_multiple_with_rng(
        &p.bp,
        &p.pc,
        &mut range_t,
        &w.values,
        &w.blindings,
        p.p.bits,
        &mut OsRng,
    )?;
    // Ignore returned commitments: verification always uses public statement commitments.
    send(&mut out, &mut t, b"range", &range.to_bytes());
    for (i, (base, subject, secret)) in std::iter::once((p.pc.B_blinding, p.excess, w.excess))
        .chain(
            p.owners
                .iter()
                .zip(&w.owners)
                .map(|(pk, sk)| (p.pc.B, *pk, *sk)),
        )
        .enumerate()
    {
        t.append_u64(b"schnorr-component", i as u64);
        t.append_message(b"base", base.compress().as_bytes());
        t.append_message(b"subject", subject.compress().as_bytes());
        let nonce = Scalar::random(&mut OsRng);
        let r = nonce * base;
        ensure(r != RistrettoPoint::identity(), "tx-zero-nonce")?;
        send(&mut out, &mut t, b"nonce", r.compress().as_bytes());
        let c = challenge(&mut t);
        let response = nonce + c * secret;
        send(&mut out, &mut t, b"response", response.as_bytes());
    }
    Ok(out)
}
fn verify(p: &Public, proof: &[u8]) -> Result<()> {
    let mut r = Reader::new(proof, MAGIC)?;
    let mut t = p.transcript();
    let mut range_t = t.clone();
    range_t.append_message(b"component", b"output-range");
    let range = RangeProof::from_bytes(r.message(&mut t, b"range")?)?;
    range
        .verify_multiple_with_rng(&p.bp, &p.pc, &mut range_t, &p.outputs, p.p.bits, &mut OsRng)
        .map_err(|_| "tx-range")?;
    for (i, (base, subject)) in std::iter::once((p.pc.B_blinding, p.excess))
        .chain(p.owners.iter().map(|pk| (p.pc.B, *pk)))
        .enumerate()
    {
        t.append_u64(b"schnorr-component", i as u64);
        t.append_message(b"base", base.compress().as_bytes());
        t.append_message(b"subject", subject.compress().as_bytes());
        let nonce = point(r.message(&mut t, b"nonce")?)?;
        ensure(nonce != RistrettoPoint::identity(), "tx-zero-nonce")?;
        let c = challenge(&mut t);
        let response = scalar(r.message(&mut t, b"response")?)?;
        ensure(
            response * base == nonce + c * subject,
            if i == 0 {
                "tx-balance"
            } else {
                "tx-authorization"
            },
        )?;
    }
    r.end()
}
pub fn run(args: &[String], matched: bool) -> Result<Value> {
    ensure(args.len() >= 5, "tx arguments")?;
    let start = Instant::now();
    let p: Parameters = read_tx(&args[1])?;
    let ledger: Ledger = read_tx(&args[2])?;
    let tx: Transaction = read_tx(&args[3])?;
    let p = Public::new(p, &ledger, &tx)?;
    let selected = if matched {
        Some(matched::Prepared::new(&p, &ledger, &tx)?)
    } else {
        None
    };
    let algorithm = if matched {
        "pir-matched/1"
    } else {
        "upstream-bulletproofs/1"
    };
    let prove = |p: &Public, w: &Private| match &selected {
        Some(selected) => matched::prove(p, selected, w),
        None => prove(p, w),
    };
    let verify = |p: &Public, data: &[u8]| match &selected {
        Some(selected) => matched::verify(p, selected, data),
        None => verify(p, data),
    };
    let public_setup_seconds = start.elapsed().as_secs_f64();
    if args[0] == "trace" {
        ensure(args.len() == 6 && matched, "tx-matched trace arguments")?;
        let data = bytes(&args[4])?;
        verify(&p, &data)?;
        let trace = matched::trace(&p, selected.as_ref().ok_or("tx-matched trace mode")?, &data)?;
        write(&args[5], &trace)?;
        return Ok(
            json!({"accepted":true,"algorithm":algorithm,"witness_read":false,
            "scope":"validated direct proof public messages; diagnostic equation cross-check only"}),
        );
    }
    if args[0] == "verify" {
        ensure(args.len() == 5, "tx verify arguments")?;
        let data = bytes(&args[4])?;
        let start = Instant::now();
        verify(&p, &data)?;
        return Ok(
            json!({"accepted":true,"algorithm":algorithm,"public_setup_seconds":public_setup_seconds,"verify_seconds":start.elapsed().as_secs_f64(),"proof_bytes":data.len(),"witness_read":false}),
        );
    }
    let start = Instant::now();
    let w = Private::new(&p.p, &read_tx(&args[4])?)?;
    let private_input_seconds = start.elapsed().as_secs_f64();
    if args[0] == "prove" {
        ensure(args.len() == 6, "tx prove arguments")?;
        let start = Instant::now();
        let proof = prove(&p, &w)?;
        let seconds = start.elapsed().as_secs_f64();
        fs::write(&args[5], &proof)?;
        return Ok(
            json!({"produced":true,"algorithm":algorithm,"public_setup_seconds":public_setup_seconds,"private_input_seconds":private_input_seconds,"prove_seconds":seconds,"proof_bytes":proof.len()}),
        );
    }
    ensure(args[0] == "bench" && args.len() == 7, "tx bench arguments")?;
    let n: usize = args[6].parse()?;
    ensure(n >= 3, "three-samples-required")?;
    fs::create_dir_all(&args[5])?;
    let mut samples = Vec::new();
    for i in 0..n {
        let start = Instant::now();
        let proof = prove(&p, &w)?;
        let prove_seconds = start.elapsed().as_secs_f64();
        let start = Instant::now();
        verify(&p, &proof)?;
        let verify_seconds = start.elapsed().as_secs_f64();
        fs::write(
            Path::new(&args[5]).join(format!("sample-{i}.proof")),
            &proof,
        )?;
        samples.push(json!({"prove_seconds":prove_seconds,"verify_seconds":verify_seconds,"proof_bytes":proof.len()}));
    }
    let report = json!({"application":"transaction","algorithm":algorithm,"parameters":p.p,"generator_setup_seconds":p.generator_setup_seconds + selected.as_ref().map_or(0.0, |s|s.generator_setup_seconds),"public_setup_seconds":public_setup_seconds,"private_input_seconds":private_input_seconds,"warm_samples":samples,"scope":"whole direct application; cached public generators and parsed inputs; proof serialization/parse included; file I/O excluded"});
    write(Path::new(&args[5]).join("warm.json"), &report)?;
    Ok(report)
}

#[cfg(test)]
mod tests {
    use super::*;
    pub(super) fn fixture() -> (Parameters, Ledger, Transaction, Witness) {
        let pc = PedersenGens::default();
        let ib = [Scalar::from(10u64), Scalar::from(20u64)];
        let ob = [Scalar::from(7u64), Scalar::from(23u64)];
        let p = Parameters {
            bits: 8,
            outputs: 2,
            inputs: 2,
        };
        let ledger = Ledger {
            snapshot: "snapshot".into(),
            network: "test".into(),
            entries: (0..2)
                .map(|i| Entry {
                    id: format!("in{i}"),
                    commitment: hex(pc.commit(Scalar::from(10u64), ib[i]).compress().as_bytes()),
                    owner: hex(((Scalar::from(i as u64 + 2)) * pc.B).compress().as_bytes()),
                    range_bits: 8,
                })
                .collect(),
        };
        let tx = Transaction {
            version: 1,
            network: "test".into(),
            context: "test1".into(),
            ledger_snapshot: "snapshot".into(),
            bits: 8,
            input_ids: vec!["in0".into(), "in1".into()],
            outputs: [9u64, 10]
                .iter()
                .zip(ob)
                .map(|(v, b)| hex(pc.commit(Scalar::from(*v), b).compress().as_bytes()))
                .collect(),
            fee: "1".into(),
        };
        let w = Witness {
            input_values: vec!["10".into(); 2],
            input_blindings: ib.iter().map(|b| hex(b.as_bytes())).collect(),
            values: vec!["9".into(), "10".into()],
            blindings: ob.iter().map(|b| hex(b.as_bytes())).collect(),
            secrets: [2u64, 3]
                .iter()
                .map(|s| hex(Scalar::from(*s).as_bytes()))
                .collect(),
        };
        (p, ledger, tx, w)
    }
    #[test]
    fn canonical_public_admission() {
        for case in 0..15 {
            let (mut p, mut l, mut t, _) = fixture();
            match case {
                0 => p.bits = 0,
                1 => p.outputs = 3,
                2 => p.inputs = 0,
                3 => t.version = 2,
                4 => t.network.push('x'),
                5 => t.context.clear(),
                6 => t.fee = "01".into(),
                7 => t.fee = "256".into(),
                8 => l.entries[1].id = l.entries[0].id.clone(),
                9 => t.input_ids[1] = t.input_ids[0].clone(),
                10 => t.input_ids[0] = "absent".into(),
                11 => l.entries[0].owner = "00".repeat(32),
                12 => l.entries[0].range_bits = 7,
                13 => l.entries[0].range_bits = 16,
                _ => t.outputs[0] = "ff".repeat(32),
            }
            assert!(Public::new(p, &l, &t).is_err(), "case {case}");
        }
        assert!(scalar(&[0xff; 32]).is_err());
        assert!(scalar(&[0; 31]).is_err());
        assert!(natural("18446744073709551616").is_err());
        assert!(point(&[0; 31]).is_err());
    }
    #[test]
    fn honest_zero_excess_and_freshness() {
        let (p, l, t, w) = fixture();
        let p = Public::new(p, &l, &t).unwrap();
        assert_eq!(p.excess, RistrettoPoint::identity());
        let w = Private::new(&p.p, &w).unwrap();
        let a = prove(&p, &w).unwrap();
        let b = prove(&p, &w).unwrap();
        verify(&p, &a).unwrap();
        verify(&p, &b).unwrap();
        assert_ne!(a, b);
    }
    #[test]
    fn hostile_private_witnesses_reach_verifier() {
        for case in 0..4 {
            let (p, l, mut t, mut w) = fixture();
            match case {
                0 => w.secrets[0] = hex(Scalar::from(99u64).as_bytes()),
                1 => w.input_blindings[0] = hex(Scalar::from(99u64).as_bytes()),
                2 => {
                    w.values[0] = "8".into();
                    t.outputs[0] = hex(PedersenGens::default()
                        .commit(Scalar::from(8u64), Scalar::from(7u64))
                        .compress()
                        .as_bytes());
                }
                _ => {
                    w.values[0] = "256".into();
                    t.outputs[0] = hex(PedersenGens::default()
                        .commit(Scalar::from(256u64), Scalar::from(7u64))
                        .compress()
                        .as_bytes());
                }
            }
            let p = Public::new(p, &l, &t).unwrap();
            let w = Private::new(&p.p, &w).unwrap();
            let proof = prove(&p, &w).unwrap();
            assert!(verify(&p, &proof).is_err(), "case {case}");
        }
    }
    #[test]
    fn malformed_and_public_bindings() {
        let (p, l, t, w) = fixture();
        let original = Public::new(p.clone(), &l, &t).unwrap();
        let proof = prove(&original, &Private::new(&p, &w).unwrap()).unwrap();
        for case in 0..7 {
            let (mut l, mut t) = (l.clone(), t.clone());
            match case {
                0 => t.context.push('x'),
                1 => t.fee = "2".into(),
                2 => l.entries[0].owner = l.entries[1].owner.clone(),
                3 => t.input_ids.swap(0, 1),
                4 => t.outputs.swap(0, 1),
                5 => l.entries[0].commitment = l.entries[1].commitment.clone(),
                _ => {
                    t.network = "other".into();
                    l.network = "other".into();
                }
            }
            assert!(verify(&Public::new(p.clone(), &l, &t).unwrap(), &proof).is_err());
        }
        let mut extra = proof.clone();
        extra.push(0);
        assert!(verify(&original, &extra).is_err());
        assert!(verify(&original, &proof[..proof.len() - 1]).is_err());
        for offset in [20, proof.len() - 1, proof.len() - 40] {
            let mut bad = proof.clone();
            bad[offset] ^= 1;
            assert!(verify(&original, &bad).is_err());
        }
    }
}

//! Sparse R1CS composition over one original commitment; no PIR interpreter.
use crate::*;
use std::time::Instant;
use zkc_arkworks::{
    Bounds, CommittedTable, ProverKey, Scalar as F, Table, VerifierKey, decode_scalar,
    encode_scalar, parse_decimal, scalar_from_wide_be,
};
const MAGIC: &[u8] = b"ZKCEXD01";
const SOURCE: &[u8]=b"direct-execution/1;MSB;one-original;public-coordinates;cpu,memory,link;cubic-outer;quadratic-inner;three-original-openings;coefficient*value=residual";
fn bounds() -> Bounds {
    Bounds::new(16, 65536, 64 << 20, 8 * 65536)
}
#[derive(Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct PublicData {
    version: String,
    wires: usize,
    rows: usize,
    columns: usize,
    statement: Vec<String>,
    config: Value,
    source_sha256: String,
    matrices: Vec<Vec<Vec<(usize, usize, String)>>>,
}
struct Entry {
    row: usize,
    col: usize,
    value: F,
}
struct Public {
    data: PublicData,
    matrices: Vec<Vec<Vec<Entry>>>,
    statement: Vec<F>,
    vk: VerifierKey,
    root: Vec<u8>,
}
impl Public {
    fn new(data: PublicData, vk: VerifierKey) -> Result<Self> {
        ensure(
            data.version == "zkc-direct-execution-public/1"
                && data.wires > 0
                && data.columns <= 65536
                && data.wires <= data.columns
                && data.columns == data.wires.max(2).next_power_of_two()
                && data.rows.is_power_of_two()
                && (2..=65536).contains(&data.rows),
            "execution-shape",
        )?;
        ensure(
            vk.metadata().arity() == data.columns.ilog2() as usize,
            "execution-key-arity",
        )?;
        ensure(
            data.statement.len() < data.wires && data.matrices.len() == 3,
            "execution-public-shape",
        )?;
        pin(&data.source_sha256)?;
        let statement = data
            .statement
            .iter()
            .map(|s| Ok(parse_decimal(s)?))
            .collect::<Result<Vec<_>>>()?;
        let mut matrices = Vec::new();
        for view in &data.matrices {
            ensure(view.len() == 3, "execution-three-matrices")?;
            let mut triple = Vec::new();
            for matrix in view {
                let mut entries = Vec::new();
                let mut previous = None;
                ensure(matrix.len() <= 8 * 65536, "execution-matrix-capacity")?;
                for (row, col, value) in matrix {
                    ensure(
                        *row < data.rows
                            && *col < data.wires
                            && previous.is_none_or(|p| p < (*row, *col)),
                        "execution-matrix-canonical",
                    )?;
                    let value = parse_decimal(value)?;
                    ensure(value != F::from(0u64), "execution-matrix-zero-entry")?;
                    entries.push(Entry {
                        row: *row,
                        col: *col,
                        value,
                    });
                    previous = Some((*row, *col));
                }
                triple.push(entries);
            }
            matrices.push(triple);
        }
        let root = serde_json::to_vec(&(
            hex(SOURCE),
            &data,
            hex(&vk.to_bytes(&bounds())?),
            zkc_arkworks::PROFILE,
        ))?;
        Ok(Self {
            data,
            matrices,
            statement,
            vk,
            root,
        })
    }
    fn transcript(&self) -> Transcript {
        let mut t = Transcript::new(b"zkc-direct-execution/1");
        t.append_message(b"public-root", &self.root);
        t
    }
    fn arity(&self) -> usize {
        self.data.columns.ilog2() as usize
    }
}
fn challenge(t: &mut Transcript) -> F {
    let mut b = [0u8; 64];
    t.challenge_bytes(b"field-challenge", &mut b);
    scalar_from_wide_be(&b)
}
fn encode(values: &[F]) -> Result<Vec<u8>> {
    let mut out = Vec::with_capacity(32 * values.len());
    for v in values {
        out.extend_from_slice(&encode_scalar(v)?);
    }
    Ok(out)
}
fn decode(data: &[u8], count: usize) -> Result<Vec<F>> {
    ensure(
        data.len() == 32 * count,
        "execution-scalar-message-degree-or-length",
    )?;
    data.as_chunks::<32>()
        .0
        .iter()
        .map(|s| Ok(decode_scalar(s)?))
        .collect()
}
fn weights(point: &[F]) -> Vec<F> {
    let mut out = vec![F::from(1u64)];
    for r in point {
        out = out
            .iter()
            .flat_map(|w| [*w * (F::from(1u64) - r), *w * r])
            .collect();
    }
    out
}
fn fold(values: &mut Vec<F>, r: F) {
    let half = values.len() / 2;
    for i in 0..half {
        let next = values[i] + r * (values[i + half] - values[i]);
        values[i] = next;
    }
    values.truncate(half);
}
fn evaluate(q: &[F], x: F) -> F {
    q.iter().rev().fold(F::from(0u64), |v, c| v * x + c)
}
fn boundary(q: &[F]) -> F {
    q[0] + q.iter().sum::<F>()
}
fn coordinate(index: usize, k: usize) -> Vec<F> {
    (0..k)
        .map(|b| F::from(((index >> (k - 1 - b)) & 1) as u64))
        .collect()
}
fn cubic(e: &[F], a: &[F], b: &[F], c: &[F]) -> Vec<F> {
    let mut q = vec![F::from(0u64); 4];
    let half = e.len() / 2;
    for i in 0..half {
        let de = e[i + half] - e[i];
        let da = a[i + half] - a[i];
        let db = b[i + half] - b[i];
        let dc = c[i + half] - c[i];
        let ab0 = a[i] * b[i] - c[i];
        let ab1 = a[i] * db + da * b[i] - dc;
        let ab2 = da * db;
        q[0] += e[i] * ab0;
        q[1] += e[i] * ab1 + de * ab0;
        q[2] += e[i] * ab2 + de * ab1;
        q[3] += de * ab2;
    }
    q
}
fn quadratic(a: &[F], b: &[F]) -> Vec<F> {
    let mut q = vec![F::from(0u64); 3];
    let half = a.len() / 2;
    for i in 0..half {
        let da = a[i + half] - a[i];
        let db = b[i + half] - b[i];
        q[0] += a[i] * b[i];
        q[1] += a[i] * db + da * b[i];
        q[2] += da * db;
    }
    q
}
fn products(p: &Public, view: usize, z: &[F]) -> Vec<Vec<F>> {
    p.matrices[view]
        .iter()
        .map(|matrix| {
            let mut out = vec![F::from(0u64); p.data.rows];
            for e in matrix {
                out[e.row] += e.value * z[e.col];
            }
            out
        })
        .collect()
}
fn contraction(p: &Public, view: usize, r: &[F], mix: &[F]) -> Vec<F> {
    let rw = weights(r);
    let mut out = vec![F::from(0u64); p.data.columns];
    for (m, alpha) in p.matrices[view].iter().zip(mix) {
        for e in m {
            out[e.col] += *alpha * e.value * rw[e.row];
        }
    }
    out
}
// Verifier evaluates the public matrix polynomial independently, using both
// equality vectors; it never obtains a contracted table from the producer.
fn coefficient(p: &Public, view: usize, r: &[F], s: &[F], mix: &[F]) -> F {
    let rw = weights(r);
    let sw = weights(s);
    let mut value = F::from(0u64);
    for (m, alpha) in p.matrices[view].iter().zip(mix) {
        for e in m {
            value += *alpha * e.value * rw[e.row] * sw[e.col];
        }
    }
    value
}
fn send_open(
    out: &mut Vec<u8>,
    t: &mut Transcript,
    original: &CommittedTable,
    point: &[F],
) -> Result<()> {
    let (value, proof) = original.open(point)?;
    send(out, t, b"opening-value", &encode(&[value])?);
    send(out, t, b"opening-proof", &proof.to_bytes(&bounds())?);
    Ok(())
}
fn read_open(
    r: &mut Reader<'_>,
    t: &mut Transcript,
    p: &Public,
    commitment: &zkc_arkworks::Commitment,
    point: &[F],
) -> Result<F> {
    let value = decode(r.message(t, b"opening-value")?, 1)?[0];
    let proof =
        p.vk.decode_proof(r.message(t, b"opening-proof")?, &bounds())?;
    ensure(
        p.vk.check(commitment, point, value, &proof)?,
        "execution-pcs",
    )?;
    Ok(value)
}
fn assignment(path: &str, p: &Public) -> Result<Vec<F>> {
    let input: Vec<String> = read(path)?;
    ensure(input.len() == p.data.wires, "execution-assignment-shape")?;
    let mut z = input
        .iter()
        .map(|v| Ok(parse_decimal(v)?))
        .collect::<Result<Vec<_>>>()?;
    z.resize(p.data.columns, F::from(0u64));
    Ok(z)
}
fn prove(p: &Public, pk: &ProverKey, z: &[F]) -> Result<Vec<u8>> {
    prove_inner(p, pk, z, None)
}
// Test-only caller can make a consistent recurrence-preserving last-round
// attack. No relation checking occurs on the producer path, including attacks.
fn prove_inner(p: &Public, pk: &ProverKey, z: &[F], attack: Option<usize>) -> Result<Vec<u8>> {
    ensure(z.len() == p.data.columns, "execution-assignment-length")?;
    let mut t = p.transcript();
    let mut out = MAGIC.to_vec();
    let original = pk.commit(&Table::from_logical(z, &bounds())?)?;
    send(
        &mut out,
        &mut t,
        b"original-commitment",
        &original.commitment().to_bytes(&bounds())?,
    );
    for i in 0..=p.statement.len() {
        send_open(&mut out, &mut t, &original, &coordinate(i, p.arity()))?;
    }
    let mut points = Vec::new();
    for view in 0..3 {
        t.append_u64(b"view", view as u64);
        let tau: Vec<_> = (0..p.data.rows.ilog2())
            .map(|_| challenge(&mut t))
            .collect();
        let mut e = weights(&tau);
        let mut abc = products(p, view, z);
        let mut r = Vec::new();
        while e.len() > 1 {
            let q = cubic(&e, &abc[0], &abc[1], &abc[2]);
            send(&mut out, &mut t, b"outer-cubic", &encode(&q)?);
            let x = challenge(&mut t);
            r.push(x);
            fold(&mut e, x);
            for v in &mut abc {
                fold(v, x);
            }
        }
        let reports: Vec<_> = abc.iter().map(|v| v[0]).collect();
        send(&mut out, &mut t, b"outer-reports", &encode(&reports)?);
        let mix: Vec<_> = (0..3).map(|_| challenge(&mut t)).collect();
        let mut a = contraction(p, view, &r, &mix);
        let mut b = z.to_vec();
        let mut s = Vec::new();
        while a.len() > 1 {
            let mut q = quadratic(&a, &b);
            if attack == Some(view) && a.len() == 2 {
                q[0] += F::from(1u64);
                q[1] -= F::from(2u64);
            }
            send(&mut out, &mut t, b"inner-quadratic", &encode(&q)?);
            let x = challenge(&mut t);
            s.push(x);
            fold(&mut a, x);
            fold(&mut b, x);
        }
        points.push(s);
    }
    // All residuals exist before any of the three original openings.
    for s in points {
        send_open(&mut out, &mut t, &original, &s)?;
    }
    Ok(out)
}
fn terminal(coefficient: F, value: F, residual: F) -> Result<()> {
    ensure(
        coefficient * value == residual,
        "execution-terminal-connection",
    )
}
fn verify(p: &Public, proof: &[u8]) -> Result<()> {
    let mut reader = Reader::new(proof, MAGIC)?;
    let mut t = p.transcript();
    let commitment =
        p.vk.decode_commitment(reader.message(&mut t, b"original-commitment")?, &bounds())?;
    for i in 0..=p.statement.len() {
        let value = read_open(
            &mut reader,
            &mut t,
            p,
            &commitment,
            &coordinate(i, p.arity()),
        )?;
        ensure(
            value
                == if i == 0 {
                    F::from(1u64)
                } else {
                    p.statement[i - 1]
                },
            "execution-public-coordinate",
        )?;
    }
    let mut residuals = Vec::new();
    for view in 0..3 {
        t.append_u64(b"view", view as u64);
        let tau: Vec<_> = (0..p.data.rows.ilog2())
            .map(|_| challenge(&mut t))
            .collect();
        let mut claim = F::from(0u64);
        let mut r = Vec::new();
        for _ in 0..p.data.rows.ilog2() {
            let q = decode(reader.message(&mut t, b"outer-cubic")?, 4)?;
            ensure(boundary(&q) == claim, "execution-outer-recurrence")?;
            let x = challenge(&mut t);
            claim = evaluate(&q, x);
            r.push(x);
        }
        let abc = decode(reader.message(&mut t, b"outer-reports")?, 3)?;
        let equality = tau
            .iter()
            .zip(&r)
            .map(|(a, b)| a * b + (F::from(1u64) - a) * (F::from(1u64) - b))
            .product::<F>();
        ensure(
            equality * (abc[0] * abc[1] - abc[2]) == claim,
            "execution-outer-terminal",
        )?;
        let mix: Vec<_> = (0..3).map(|_| challenge(&mut t)).collect();
        claim = abc.iter().zip(&mix).map(|(a, b)| *a * b).sum();
        let mut s = Vec::new();
        for _ in 0..p.arity() {
            let q = decode(reader.message(&mut t, b"inner-quadratic")?, 3)?;
            ensure(boundary(&q) == claim, "execution-inner-recurrence")?;
            let x = challenge(&mut t);
            claim = evaluate(&q, x);
            s.push(x);
        }
        let coefficient = coefficient(p, view, &r, &s, &mix);
        residuals.push((s, coefficient, claim));
    }
    let mut values = Vec::new();
    for (s, _, _) in &residuals {
        values.push(read_open(&mut reader, &mut t, p, &commitment, s)?);
    }
    for ((_, coefficient, claim), value) in residuals.into_iter().zip(values) {
        terminal(coefficient, value, claim)?;
    }
    reader.end()
}
fn load(public: &str, setup: &str) -> Result<(Public, Value)> {
    let data = read(public)?;
    let setup: Value = read(setup)?;
    let vk = VerifierKey::from_bytes(
        &unhex(setup["verifier_key"].as_str().ok_or("setup-vk")?)?,
        pin(setup["verifier_key_id"].as_str().ok_or("setup-vk-pin")?)?,
        &bounds(),
    )?;
    Ok((Public::new(data, vk)?, setup))
}
fn load_pk(p: &Public, setup: &Value) -> Result<ProverKey> {
    Ok(ProverKey::from_bytes(
        &bytes(setup["prover_key_file"].as_str().ok_or("setup-pk")?)?,
        pin(setup["material_fingerprint"]
            .as_str()
            .ok_or("setup-pk-pin")?)?,
        &p.vk,
        &bounds(),
    )?)
}
pub fn run(args: &[String]) -> Result<Value> {
    if args.first().is_some_and(|v| v == "setup-bench") {
        ensure(args.len() == 3, "execution setup-bench ARITY SAMPLES")?;
        let arity: usize = args[1].parse()?;
        let count: usize = args[2].parse()?;
        ensure((1..=16).contains(&arity) && count >= 3, "setup-bench-shape")?;
        let mut samples = Vec::new();
        for _ in 0..count {
            let start = Instant::now();
            let keys = zkc_arkworks::Keys::setup_for_development(arity, &bounds())?;
            let seconds = start.elapsed().as_secs_f64();
            samples.push(json!({"setup_seconds":seconds,"key_id":hex(&keys.verifier_key().metadata().key_id())}));
        }
        return Ok(
            json!({"arity":arity,"samples":samples,"scope":"fresh OS-generated development setups at matched arity; proof benchmarks reuse the original fixture key"}),
        );
    }
    ensure(args.len() >= 4, "execution arguments")?;
    let start = Instant::now();
    let (p, setup) = load(&args[1], &args[2])?;
    let public_setup_seconds = start.elapsed().as_secs_f64();
    if args[0] == "verify" {
        ensure(args.len() == 4, "execution verify arguments")?;
        let proof = bytes(&args[3])?;
        let start = Instant::now();
        verify(&p, &proof)?;
        return Ok(
            json!({"accepted":true,"public_setup_seconds":public_setup_seconds,"verify_seconds":start.elapsed().as_secs_f64(),"proof_bytes":proof.len(),"witness_read":false}),
        );
    }
    let start = Instant::now();
    let pk = load_pk(&p, &setup)?;
    let key_import_seconds = start.elapsed().as_secs_f64();
    let start = Instant::now();
    let z = assignment(&args[3], &p)?;
    let private_input_seconds = start.elapsed().as_secs_f64();
    if args[0] == "prove" {
        ensure(args.len() == 5, "execution prove arguments")?;
        let start = Instant::now();
        let proof = prove(&p, &pk, &z)?;
        let seconds = start.elapsed().as_secs_f64();
        fs::write(&args[4], &proof)?;
        return Ok(
            json!({"produced":true,"public_setup_seconds":public_setup_seconds,"key_import_seconds":key_import_seconds,"private_input_seconds":private_input_seconds,"prove_seconds":seconds,"proof_bytes":proof.len()}),
        );
    }
    ensure(
        args[0] == "bench" && args.len() == 6,
        "execution bench arguments",
    )?;
    let n: usize = args[5].parse()?;
    ensure(n >= 3, "three-samples-required")?;
    fs::create_dir_all(&args[4])?;
    let mut samples = Vec::new();
    for i in 0..n {
        let start = Instant::now();
        let proof = prove(&p, &pk, &z)?;
        let prove_seconds = start.elapsed().as_secs_f64();
        let start = Instant::now();
        verify(&p, &proof)?;
        let verify_seconds = start.elapsed().as_secs_f64();
        fs::write(
            Path::new(&args[4]).join(format!("sample-{i}.proof")),
            &proof,
        )?;
        samples.push(json!({"prove_seconds":prove_seconds,"verify_seconds":verify_seconds,"proof_bytes":proof.len()}));
    }
    let report = json!({"application":"execution","rows":p.data.rows,"columns":p.data.columns,"views":3,"outer_rounds_per_view":p.data.rows.ilog2(),"inner_rounds_per_view":p.arity(),"original_commitments":1,"original_openings":p.statement.len()+4,"public_setup_seconds":public_setup_seconds,"key_import_seconds":key_import_seconds,"private_input_seconds":private_input_seconds,"development_setup_seconds":setup["baseline"]["setup_seconds"],"warm_samples":samples,"scope":"whole direct application; cached authenticated keys, public matrices, input assignment; input table copy, all transcript/algebra/PCS, serialization/parse included; file I/O excluded"});
    write(Path::new(&args[4]).join("warm.json"), &report)?;
    Ok(report)
}
#[cfg(test)]
mod tests {
    use super::*;
    use zkc_arkworks::Keys;
    fn fixture(zero: bool) -> (Public, ProverKey, Vec<F>) {
        let keys = Keys::setup_for_development(2, &bounds()).unwrap();
        let m = if zero {
            vec![vec![], vec![], vec![]]
        } else {
            vec![
                vec![(0, 1, "1".into())],
                vec![(0, 0, "1".into())],
                vec![(0, 1, "1".into())],
            ]
        };
        let data = PublicData {
            version: "zkc-direct-execution-public/1".into(),
            wires: 3,
            rows: 2,
            columns: 4,
            statement: vec!["7".into()],
            config: json!({"test":true}),
            source_sha256: "00".repeat(32),
            matrices: vec![m.clone(), m.clone(), m],
        };
        (
            Public::new(data, keys.verifier_key().clone()).unwrap(),
            keys.prover_key().clone(),
            [1u64, 7, 3, 0].map(F::from).to_vec(),
        )
    }
    #[test]
    fn canonical_public_admission_and_capacity() {
        let (p, _, _) = fixture(false);
        for case in 0..12 {
            let mut d = p.data.clone();
            match case {
                0 => {
                    d.wires = usize::MAX;
                    d.columns = usize::MAX;
                }
                1 => d.rows = 0,
                2 => d.wires = 0,
                3 => d.columns = 8,
                4 => d.statement = vec!["1".into(); 3],
                5 => d.statement[0] = "01".into(),
                6 => d.matrices.pop().map(|_| ()).unwrap(),
                7 => d.matrices[0].pop().map(|_| ()).unwrap(),
                8 => d.matrices[0][0][0].0 = 2,
                9 => d.matrices[0][0][0].1 = 3,
                10 => d.matrices[0][0][0].2 = "0".into(),
                _ => {
                    let e = d.matrices[0][0][0].clone();
                    d.matrices[0][0].push(e);
                }
            }
            assert!(Public::new(d, p.vk.clone()).is_err(), "case {case}");
        }
        assert!(decode(&[0xff; 32], 1).is_err());
        assert!(decode(&[0; 64], 1).is_err());
    }
    #[test]
    fn honest_and_zero_coefficients() {
        for zero in [false, true] {
            let (p, pk, z) = fixture(zero);
            let proof = prove(&p, &pk, &z).unwrap();
            verify(&p, &proof).unwrap();
        }
        terminal(F::from(0u64), F::from(19u64), F::from(0u64)).unwrap();
        assert!(terminal(F::from(0u64), F::from(0u64), F::from(1u64)).is_err());
    }
    #[test]
    fn each_terminal_guard_after_valid_pcs() {
        for zero in [false, true] {
            let (p, pk, z) = fixture(zero);
            for view in 0..3 {
                let proof = prove_inner(&p, &pk, &z, Some(view)).unwrap();
                assert_eq!(
                    verify(&p, &proof).unwrap_err().to_string(),
                    "execution-terminal-connection"
                );
            }
        }
    }
    #[test]
    fn consistent_false_output_and_private_invalid() {
        let (p, pk, mut z) = fixture(false);
        let mut data = p.data.clone();
        data.matrices[0][2] = vec![(0, 0, "7".into())];
        let valid = Public::new(data.clone(), p.vk.clone()).unwrap();
        verify(&valid, &prove(&valid, &pk, &z).unwrap()).unwrap();
        data.statement[0] = "8".into();
        z[1] = F::from(8u64);
        let false_public = Public::new(data, p.vk.clone()).unwrap();
        let proof = prove(&false_public, &pk, &z).unwrap();
        assert_eq!(
            verify(&false_public, &proof).unwrap_err().to_string(),
            "execution-outer-recurrence"
        );
        z[0] = F::from(2u64);
        let proof = prove(&p, &pk, &z).unwrap();
        assert_eq!(
            verify(&p, &proof).unwrap_err().to_string(),
            "execution-public-coordinate"
        );
    }
    #[test]
    fn transcript_context_eof_and_messages() {
        let (p, pk, z) = fixture(false);
        let proof = prove(&p, &pk, &z).unwrap();
        let mut data = p.data.clone();
        data.config = json!({"test":false});
        let changed = Public::new(data, p.vk.clone()).unwrap();
        assert!(verify(&changed, &proof).is_err());
        let mut extra = proof.clone();
        extra.push(0);
        assert!(verify(&p, &extra).is_err());
        assert!(verify(&p, &proof[..proof.len() - 1]).is_err());
        let mut offset = 8;
        let mut count = 0;
        while offset < proof.len() {
            let n = u32::from_le_bytes(proof[offset..offset + 4].try_into().unwrap()) as usize;
            let mut bad = proof.clone();
            bad[offset + 4 + n - 1] ^= 1;
            assert!(verify(&p, &bad).is_err(), "message {count}");
            offset += 4 + n;
            count += 1;
        }
        assert!(count > 20);
    }
}

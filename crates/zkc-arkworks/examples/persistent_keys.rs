//! Three independent development processes: setup once, produce, validate.
//! Local config files are trusted setup outputs, never candidate-supplied pins.
//! This is a PCS custody/transport example, not a protocol or Fiat-Shamir proof.
use std::{fs, io::Read, path::Path, time::Instant};
use zkc_arkworks::{
    Bounds, Error, Keys, ProverKey, Scalar, Table, VerifierKey, decode_scalar, encode_scalar,
};

type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;

// Explicit example policy only; the library imposes no arbitrary rank cap.
const MAX_BYTES: usize = 2 << 20;
const BOUNDS: Bounds = Bounds::new(12, 4096, MAX_BYTES, 12 * 4096);

// Bound file ingestion too: the byte-slice codec cannot control its caller's
// I/O buffer. This example uses a finite read ceiling, including one extra byte
// to detect oversize files even if the file changes during the read.
fn read(path: &Path, limit: usize) -> Result<Vec<u8>> {
    let file = fs::File::open(path)?;
    if file.metadata()?.len() > limit as u64 {
        return Err(Error::ByteLimit.into());
    }
    let mut bytes = Vec::new();
    file.take(limit as u64 + 1).read_to_end(&mut bytes)?;
    if bytes.len() > limit {
        return Err(Error::ByteLimit.into());
    }
    Ok(bytes)
}

fn pin(path: &Path) -> Result<[u8; 32]> {
    read(path, 32)?
        .try_into()
        .map_err(|_| Error::InvalidEncoding.into())
}

fn load_verifier(config: &Path) -> Result<VerifierKey> {
    Ok(VerifierKey::from_bytes(
        &read(&config.join("verifier.key"), MAX_BYTES)?,
        pin(&config.join("verifier.pin"))?,
        &BOUNDS,
    )?)
}

fn point(n: usize) -> Vec<Scalar> {
    // Fixed public PCS query for this example, not a transcript challenge.
    (0..n).map(|i| Scalar::from(i as u64 + 7)).collect()
}

fn setup(root: &Path, n: usize) -> Result<()> {
    let started = Instant::now();
    let keys = Keys::setup_for_development(n, &BOUNDS)?;
    let setup_us = started.elapsed().as_micros();
    let started = Instant::now();
    let prover = keys.prover_key().to_bytes(&BOUNDS)?;
    let prover_export_us = started.elapsed().as_micros();
    let verifier = keys.verifier_key().to_bytes(&BOUNDS)?;
    // Fail if the destination exists: do not silently replace the local pins.
    fs::create_dir(root)?;
    let config = root.join("config");
    fs::create_dir(&config)?;
    fs::write(root.join("prover.key"), &prover)?;
    fs::write(config.join("verifier.key"), &verifier)?;
    fs::write(
        config.join("verifier.pin"),
        keys.verifier_key().metadata().key_id(),
    )?;
    fs::write(
        config.join("prover.pin"),
        keys.prover_key().material_fingerprint(),
    )?;
    println!(
        "stage=setup n={n} setup_us={setup_us} prover_export_us={prover_export_us} prover_bytes={} verifier_bytes={}",
        prover.len(),
        verifier.len()
    );
    Ok(())
}

fn produce(root: &Path) -> Result<()> {
    let config = root.join("config");
    let started = Instant::now();
    let verifier = load_verifier(&config)?;
    let verifier_load_including_io_us = started.elapsed().as_micros();
    let bytes = read(&root.join("prover.key"), MAX_BYTES)?;
    let expected = pin(&config.join("prover.pin"))?;
    let started = Instant::now();
    let prover = ProverKey::from_bytes(&bytes, expected, &verifier, &BOUNDS)?;
    let prover_import_us = started.elapsed().as_micros();
    let n = prover.metadata().arity();
    let values: Vec<_> = (0..1usize << n)
        .map(|i| Scalar::from((i * i + 3 * i + 5) as u64))
        .collect();
    let table = Table::from_logical_vec(values, &BOUNDS)?;
    let started = Instant::now();
    let committed = prover.commit(&table)?;
    let commit_us = started.elapsed().as_micros();
    let started = Instant::now();
    let (value, proof) = committed.open(&point(n))?;
    let open_us = started.elapsed().as_micros();
    // Complete all candidate encoding before publishing files. This small
    // example's multi-file writes are not an atomic publication protocol.
    let commitment_bytes = committed.commitment().to_bytes(&BOUNDS)?;
    let proof_bytes = proof.to_bytes(&BOUNDS)?;
    let value_bytes = encode_scalar(&value)?;
    let candidate = root.join("candidate");
    fs::create_dir(&candidate)?;
    fs::write(candidate.join("commitment"), commitment_bytes)?;
    fs::write(candidate.join("proof"), proof_bytes)?;
    fs::write(candidate.join("value"), value_bytes)?;
    println!(
        "stage=produce n={n} verifier_load_including_io_us={verifier_load_including_io_us} prover_import_us={prover_import_us} commit_us={commit_us} open_including_tensor_eval_us={open_us}"
    );
    Ok(())
}

fn validate(root: &Path) -> Result<()> {
    let verifier = load_verifier(&root.join("config"))?;
    let candidate = root.join("candidate");
    let commitment =
        verifier.decode_commitment(&read(&candidate.join("commitment"), MAX_BYTES)?, &BOUNDS)?;
    let proof = verifier.decode_proof(&read(&candidate.join("proof"), MAX_BYTES)?, &BOUNDS)?;
    let value = decode_scalar(&read(&candidate.join("value"), 32)?)?;
    let started = Instant::now();
    let accepted = verifier.check(
        &commitment,
        &point(verifier.metadata().arity()),
        value,
        &proof,
    )?;
    let check_us = started.elapsed().as_micros();
    println!(
        "stage=validate n={} check_us={check_us} accepted={accepted}",
        verifier.metadata().arity()
    );
    if !accepted {
        return Err("opening rejected".into());
    }
    Ok(())
}

fn main() -> Result<()> {
    let args: Vec<_> = std::env::args().collect();
    match args.as_slice() {
        [_, command, root, n] if command == "setup" => setup(Path::new(root), n.parse()?),
        [_, command, root] if command == "produce" => produce(Path::new(root)),
        [_, command, root] if command == "validate" => validate(Path::new(root)),
        _ => Err("usage: persistent_keys setup DIR RANK | produce DIR | validate DIR".into()),
    }
}

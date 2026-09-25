//! Single-run cost diagnostics, not a benchmark or compiled protocol.
use std::{hint::black_box, time::Instant};
use zkc_arkworks::{Bounds, Keys, RandomSource, Scalar, Table, VerifierKey};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let n: usize = std::env::args()
        .nth(1)
        .map(|s| s.parse())
        .transpose()?
        .unwrap_or(8);
    // This example's explicit finite profile. The library has no such default.
    let bounds = Bounds::new(12, 4096, 1 << 20, 12 * 4096);
    let started = Instant::now();
    let keys = Keys::setup_for_development(n, &bounds)?;
    let setup_us = started.elapsed().as_micros();
    let logical: Vec<_> = (0..1usize << n)
        .map(|i| Scalar::from((i * i + 3 * i + 5) as u64))
        .collect();
    let started = Instant::now();
    let table = Table::from_logical(&logical, &bounds)?;
    let conversion_us = started.elapsed().as_micros();
    let started = Instant::now();
    for _ in 0..100 {
        black_box(Table::from_logical(black_box(&logical), &bounds)?);
    }
    let conversion_mean_ns = started.elapsed().as_nanos() / 100;
    let started = Instant::now();
    let original = keys.prover_key().commit(&table)?;
    let commit_us = started.elapsed().as_micros();
    let mut random = RandomSource::from_os()?;
    let point = random.point(n, &bounds)?;
    let started = Instant::now();
    let (value, proof) = original.open(&point)?;
    let open_us = started.elapsed().as_micros();
    let verifier_bytes = keys.verifier_key().to_bytes(&bounds)?;
    let pin = keys.verifier_key().metadata().key_id();
    let started = Instant::now();
    let verifier = VerifierKey::from_bytes(&verifier_bytes, pin, &bounds)?;
    let key_import_us = started.elapsed().as_micros();
    let started = Instant::now();
    let accepted = verifier.check(original.commitment(), &point, value, &proof)?;
    let check_us = started.elapsed().as_micros();
    if !accepted {
        return Err("honest opening failed".into());
    }
    println!(
        "arkworks=0.6.0 field=BLS12-381::Fr hiding=false setup=local-os-seeded compiled_protocol=false"
    );
    println!(
        "n={n} setup_us={setup_us} conversion_us={conversion_us} conversion_mean_ns={conversion_mean_ns} commit_us={commit_us} open_including_tensor_eval_us={open_us} key_import_us={key_import_us} check_us={check_us}"
    );
    println!(
        "native_table_payload_bytes={} verifier_bytes={} commitment_bytes={} proof_bytes={} accepted={accepted}",
        table.len() * std::mem::size_of::<Scalar>(),
        verifier_bytes.len(),
        original.commitment().to_bytes(&bounds)?.len(),
        proof.to_bytes(&bounds)?.len()
    );
    Ok(())
}

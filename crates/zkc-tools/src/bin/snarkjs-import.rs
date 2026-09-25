//! Convert bounded snarkjs artifacts into ordinary typed kernel wire values.
use std::{collections::BTreeMap, io::Write};
use zkc_backends::{Domain, EntryPolicy, NativeBackend, Policy, PublicInputs, Value};
use zkc_runtime::interactive::Value as RuntimeValue;
use zkc_tools::snarkjs::{Limits, read_wtns, read_zkey};
fn run() -> Result<(), Box<dyn std::error::Error>> {
    let args = std::env::args_os().skip(1).collect::<Vec<_>>();
    if args.len() != 3 {
        return Err("usage: snarkjs-import KEY.zkey WITNESS.wtns OUTPUT.json".into());
    }
    let limits = Limits::default();
    let policy = Policy {
        max_groups: 32768,
        ..Policy::default()
    };
    let key = read_zkey(&args[0], &limits, &policy)?;
    let witness = read_wtns(&args[1], &limits, &policy)?;
    let mut values: BTreeMap<String, Value> = key.values();
    values.insert("assignment".into(), key.assignment(&witness)?);
    let backend = NativeBackend::new(
        policy,
        EntryPolicy::new(
            Domain::new("import", "import", "import", None),
            None,
            PublicInputs::LocalOnly,
        ),
        None,
    )
    .map_err(|e| e.code)?;
    let mut rows = Vec::new();
    for (name, value) in values {
        let wire = backend.encode_value(&value).map_err(|e| e.code)?;
        let mut hex = String::new();
        hex.try_reserve_exact(wire.len() * 2)?;
        const DIGITS: &[u8] = b"0123456789abcdef";
        for b in wire {
            hex.push(DIGITS[(b >> 4) as usize] as char);
            hex.push(DIGITS[(b & 15) as usize] as char);
        }
        rows.push(serde_json::json!([
            name,
            value.physical_type().spelling(),
            hex
        ]));
    }
    let output = std::fs::File::create(&args[2])?;
    let mut out = std::io::BufWriter::new(output);
    serde_json::to_writer(
        &mut out,
        &serde_json::json!(["zkc.snarkjs.prepared/1", rows]),
    )?;
    out.write_all(b"\n")?;
    out.flush()?;
    Ok(())
}
fn main() {
    if let Err(e) = run() {
        eprintln!("{e}");
        std::process::exit(1)
    }
}

//! Whole application evaluation references, with independent public verifiers.
mod execution;
mod transaction;

use merlin::Transcript;
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use std::{fs, io::Read, path::Path};

type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;
const LIMIT: usize = 64 << 20;
fn ensure(ok: bool, code: &'static str) -> Result<()> {
    if ok { Ok(()) } else { Err(code.into()) }
}
fn bytes(path: impl AsRef<Path>) -> Result<Vec<u8>> {
    bounded_bytes(path, LIMIT)
}
fn bounded_bytes(path: impl AsRef<Path>, limit: usize) -> Result<Vec<u8>> {
    let mut data = Vec::new();
    fs::File::open(path)?
        .take((limit + 1) as u64)
        .read_to_end(&mut data)?;
    ensure(data.len() <= limit, "input-size")?;
    Ok(data)
}
fn read<T: for<'de> Deserialize<'de>>(path: impl AsRef<Path>) -> Result<T> {
    Ok(serde_json::from_slice(&bytes(path)?)?)
}
fn write(path: impl AsRef<Path>, value: &impl Serialize) -> Result<()> {
    fs::write(path, serde_json::to_vec_pretty(value)?)?;
    Ok(())
}
fn hex(data: &[u8]) -> String {
    data.iter().map(|v| format!("{v:02x}")).collect()
}
fn unhex(s: &str) -> Result<Vec<u8>> {
    ensure(
        s.len().is_multiple_of(2)
            && s.bytes()
                .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b)),
        "canonical-hex",
    )?;
    s.as_bytes()
        .as_chunks::<2>()
        .0
        .iter()
        .map(|p| Ok(u8::from_str_radix(std::str::from_utf8(p)?, 16)?))
        .collect()
}
fn pin(s: &str) -> Result<[u8; 32]> {
    unhex(s)?.try_into().map_err(|_| "pin-length".into())
}
fn send(out: &mut Vec<u8>, t: &mut Transcript, label: &'static [u8], msg: &[u8]) {
    out.extend_from_slice(&(msg.len() as u32).to_le_bytes());
    out.extend_from_slice(msg);
    t.append_message(label, msg);
}
struct Reader<'a> {
    data: &'a [u8],
}
impl<'a> Reader<'a> {
    fn new(data: &'a [u8], magic: &[u8]) -> Result<Self> {
        ensure(data.starts_with(magic), "proof-version")?;
        Ok(Self {
            data: &data[magic.len()..],
        })
    }
    fn take(&mut self, n: usize) -> Result<&'a [u8]> {
        ensure(n <= self.data.len(), "proof-truncated")?;
        let (v, tail) = self.data.split_at(n);
        self.data = tail;
        Ok(v)
    }
    fn message(&mut self, t: &mut Transcript, label: &'static [u8]) -> Result<&'a [u8]> {
        let n = u32::from_le_bytes(self.take(4)?.try_into()?) as usize;
        let data = self.take(n)?;
        t.append_message(label, data);
        Ok(data)
    }
    fn end(self) -> Result<()> {
        ensure(self.data.is_empty(), "proof-trailing-bytes")
    }
}
fn main() {
    let args: Vec<_> = std::env::args().skip(1).collect();
    let result: Result<Value> = match args.split_first() {
        Some((app, args)) if app == "tx" => transaction::run(args, false),
        Some((app, args)) if app == "tx-matched" => transaction::run(args, true),
        Some((app, args)) if app == "execution" => execution::run(args),
        _ => Err(
            "usage: zkc-application-baselines tx|tx-matched|execution prove|verify|bench ... (README.md)"
                .into(),
        ),
    };
    match result {
        Ok(v) => println!("{v}"),
        Err(e) => {
            println!("{}", json!({"accepted":false,"error":e.to_string()}));
            std::process::exit(1);
        }
    }
}

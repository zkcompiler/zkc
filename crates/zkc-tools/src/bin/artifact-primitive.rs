//! One public request in, one exact answer out. No proof or source interpreter.
use std::io::Read;
use zkc_tools::artifact::primitive::{MAX_REQUEST_BYTES, parse_request, respond};

fn run() -> Result<serde_json::Value, &'static str> {
    let [path] = std::env::args()
        .skip(1)
        .collect::<Vec<_>>()
        .try_into()
        .map_err(|_| "usage: artifact-primitive REQUEST_JSON")?;
    let file = std::fs::File::open(&path).map_err(|_| "primitive-io")?;
    let mut bytes = Vec::new();
    file.take(MAX_REQUEST_BYTES as u64 + 1)
        .read_to_end(&mut bytes)
        .map_err(|_| "primitive-io")?;
    respond(&parse_request(&bytes)?)
}
fn main() {
    match run() {
        Ok(reply) => println!("{reply}"),
        Err(code) => {
            println!("{}", serde_json::json!(["error", code]));
            std::process::exit(1);
        }
    }
}

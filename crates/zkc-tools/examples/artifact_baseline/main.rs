//! Public development fixture and same-computation direct-library baseline.
mod bench;
mod codec;
mod dleq;
mod fixture;
mod input;
mod source;
mod transcript;
mod two_factor;
use serde_json::{Value, json};
use std::path::Path;
type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;
fn ensure(ok: bool, code: &'static str) -> Result<()> {
    if ok { Ok(()) } else { Err(code.into()) }
}
fn run() -> Result<Value> {
    let a: Vec<_> = std::env::args().collect();
    match a.as_slice() {
        [_,cmd,s,d,dir] if cmd=="fixture" => fixture::generate(&source::Source::load(Path::new(s),Path::new(d))?,Path::new(s),Path::new(d),Path::new(dir)),
        [_,cmd,s,d,i,p,reps] if cmd=="prove-development" || cmd=="validate" => bench::run(&source::Source::load(Path::new(s),Path::new(d))?,Path::new(i),Path::new(p),cmd=="prove-development",reps.parse()?),
        _=>Err("usage: artifact_baseline fixture SOURCE DESCRIPTOR NEW_DIRECTORY | {prove-development|validate} SOURCE DESCRIPTOR INPUTS PROOF REPETITIONS".into())
    }
}
fn main() {
    match run() {
        Ok(v) => {
            println!("{v}");
            if v["status"] == "refused" {
                std::process::exit(1);
            }
        }
        Err(e) => {
            println!("{}", json!({"status":"refused","code":e.to_string()}));
            std::process::exit(1);
        }
    }
}

#[cfg(test)]
mod tests;

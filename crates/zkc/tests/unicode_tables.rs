// Exercise the actual build-time reader's refusal paths independently of Cargo.
#[allow(dead_code)]
#[path = "../build.rs"]
mod generator;

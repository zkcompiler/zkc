//! Public cryptography for the independent Lean source interpreter.
//!
//! This service implements individual public primitive requests, never a
//! protocol verifier. It does not run the compiler, Runner, or NativeBackend and
//! never receives proving material or a private witness. Lean owns source
//! control, arithmetic, framing and request construction. The same upstream
//! arkworks/Merlin/spongefish cryptography is explicitly trusted in both paths.
mod bn254;
mod codec;
mod koala_bear;
mod public;
mod ristretto;
mod transcript;

#[cfg(test)]
mod tests;

use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};

type Result<T> = std::result::Result<T, &'static str>;
pub const MAX_REQUEST_BYTES: usize = 64 * 1024 * 1024;

/// Evaluate one complete public request. Callers associate this answer with the
/// exact request, not its position in a sequence. Configuration in a request
/// comes from the application's expected public configuration through Lean;
/// evaluating this function does not authenticate an arbitrary request's source.
pub fn respond(request: &Json) -> Result<Json> {
    let record = codec::array(request)?;
    match record {
        [tag, algorithm, input] if codec::text(tag)? == "zkc.hash/1" => {
            if codec::text(algorithm)? != "sha256" {
                return Err("primitive-hash");
            }
            let bytes = codec::unhex(codec::text(input)?)?;
            Ok(json!(codec::hex(&Sha256::digest(bytes))))
        }
        [tag, suite, steps] if codec::text(tag)? == "zkc.duplex-request/1" => {
            transcript::duplex(suite, steps)
        }
        [tag, suite, domain, steps] if codec::text(tag)? == "zkc.transcript-request/3" => {
            transcript::bytes(suite, domain, steps)
        }
        [tag, keys, operation, arguments, attrs, inputs]
            if codec::text(tag)? == "zkc.public-primitive/1" =>
        {
            match public::evaluate_explicit(keys, operation, arguments, attrs, inputs) {
                Ok(values) => {
                    let mut response = vec![json!("ok")];
                    response.extend(values);
                    Ok(Json::Array(response))
                }
                Err(code) => Ok(json!(["error", code])),
            }
        }
        _ => Err("primitive-request"),
    }
}

/// Bounded JSON parsing; serde's recursion limit remains enabled. Arrays and
/// strings are further restricted by each exact request schema.
pub fn parse_request(bytes: &[u8]) -> Result<Json> {
    if bytes.len() > MAX_REQUEST_BYTES {
        return Err("primitive-request-limit");
    }
    // The public service allows longer replay histories than a source carrier,
    // but still bounds allocation-bearing nodes before constructing any tree.
    super::json::preflight(bytes, 500_000, 100_000).map_err(|_| "primitive-json-limit")?;
    serde_json::from_slice(bytes).map_err(|_| "primitive-json")
}

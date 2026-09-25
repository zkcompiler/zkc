use super::{Result, codec};
use serde_json::Value as Json;
/// Execute the reference's explicit Merlin calls and return bytes. Field
/// reduction and all protocol history construction belong to Lean.
pub(super) fn bytes(suite: &Json, domain: &Json, steps: &Json) -> Result<Json> {
    fn label(value: &Json) -> Result<&'static [u8]> {
        match codec::unhex(codec::text(value)?)?.as_slice() {
            b"zkc.artifact/1" => Ok(b"zkc.artifact/1"),
            b"binding" => Ok(b"binding"),
            b"origin" => Ok(b"origin"),
            b"value" => Ok(b"value"),
            b"challenge" => Ok(b"challenge"),
            b"query-bound" => Ok(b"query-bound"),
            b"query-index" => Ok(b"query-index"),
            _ => Err("primitive-transcript-label"),
        }
    }
    if !matches!(
        codec::text(suite)?,
        "merlin3.bls12-381.fr64be/1"
            | "merlin3.ristretto255.scalar64le/1"
            | "merlin3.koala-bear.ext8-binomial3.rejection31le/1"
    ) {
        return Err("primitive-suite");
    }
    let steps = codec::array(steps)?;
    if steps.is_empty() || steps.len() > 200001 {
        return Err("primitive-history-length");
    }
    let mut transcript = merlin::Transcript::new(label(domain)?);
    let mut result = None;
    for step in steps {
        result = None;
        match codec::array(step)? {
            [tag, name, value] if codec::text(tag)? == "append" => {
                transcript.append_message(label(name)?, &codec::unhex(codec::text(value)?)?);
            }
            [tag, name, width]
                if codec::text(tag)? == "challenge" && codec::text(width)? == "64" =>
            {
                let mut bytes = [0u8; 64];
                transcript.challenge_bytes(label(name)?, &mut bytes);
                result = Some(bytes);
            }
            _ => return Err("primitive-transcript-step"),
        }
    }
    Ok(serde_json::json!([
        "ok",
        codec::hex(&result.ok_or("primitive-history-last")?)
    ]))
}

/// The independent Lean reference owns every absorbed byte, including framing.
/// This service supplies only the pinned permutation/duplex computation. It
/// does not authenticate source, context, codecs or proof-system assumptions.
pub(super) fn duplex(suite: &Json, steps: &Json) -> Result<Json> {
    use spongefish::{DuplexSpongeInterface, instantiations::Keccak};
    if codec::text(suite)? != "spongefish0.7.4.keccak.bls12-381.fr64be/1" {
        return Err("primitive-suite");
    }
    let steps = codec::array(steps)?;
    if steps.is_empty() || steps.len() > 300003 {
        return Err("primitive-history-length");
    }
    let mut sponge = Keccak::default();
    let mut result = None;
    for step in steps {
        result = None;
        match codec::array(step)? {
            [tag, data] if codec::text(tag)? == "absorb" => {
                sponge.absorb(&codec::unhex(codec::text(data)?)?);
            }
            [tag, width] if codec::text(tag)? == "squeeze" && codec::text(width)? == "64" => {
                let mut bytes = [0; 64];
                sponge.squeeze(&mut bytes);
                result = Some(bytes);
            }
            _ => return Err("primitive-transcript-step"),
        }
    }
    Ok(serde_json::json!([
        "ok",
        codec::hex(&result.ok_or("primitive-history-last")?)
    ]))
}

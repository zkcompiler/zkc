//! Canonical ABI encoding for the target's single verifier function.
use super::*;

/// Canonical native public wire values, invocation context, and native framed
/// proof. This adapter does not decode or reinterpret the cryptographic bytes.
pub struct Invocation<'a> {
    pub public_inputs: &'a [&'a [u8]],
    pub context: &'a [u8],
    pub proof: &'a [u8],
}

pub(super) fn abi() -> Value {
    serde_json::json!([{
        "type":"function", "name":"verify", "stateMutability":"view",
        "inputs":[{"name":"publicInputs","type":"bytes[]"},
                  {"name":"context","type":"bytes"},
                  {"name":"proof","type":"bytes"}],
        "outputs":[{"name":"accepted","type":"bool"}]
    }])
}

fn word(out: &mut Vec<u8>, value: usize) {
    out.extend_from_slice(&[0; 24]);
    out.extend_from_slice(&(value as u64).to_be_bytes());
}
fn padded(length: usize) -> Result<usize> {
    length
        .checked_add(31)
        .map(|n| n & !31)
        .ok_or_else(|| "evm-calldata-limit".into())
}
fn blob(out: &mut Vec<u8>, value: &[u8]) -> Result<()> {
    word(out, value.len());
    out.extend_from_slice(value);
    out.resize(out.len() + padded(value.len())? - value.len(), 0);
    Ok(())
}
impl Artifact {
    /// Encode verify(publicInputs, context, proof), with sequential offsets,
    /// zero padding and no trailing data. The immutable deployment byte caps
    /// apply before allocation; logical types and frames are checked on-chain.
    pub fn calldata(&self, invocation: Invocation<'_>) -> Result<Vec<u8>> {
        let source = self.source()?;
        let limits = &source.metadata()["limits"];
        let cap = |key: &str, maximum: u64| -> Result<usize> {
            limits[key]
                .as_u64()
                .filter(|v| *v > 0 && *v <= maximum)
                .and_then(|v| usize::try_from(v).ok())
                .ok_or_else(|| "evm-source-limits".into())
        };
        let public_bytes = invocation
            .public_inputs
            .iter()
            .try_fold(0usize, |n, value| n.checked_add(value.len()))
            .ok_or("evm-calldata-limit")?;
        if public_bytes > cap("public_bytes", 131072)?
            || invocation.context.len() > cap("context_bytes", 4096)?
            || invocation.proof.len() > cap("proof_bytes", 65536)?
        {
            return Err("evm-calldata-limit".into());
        }
        // Derive the complete size with checked arithmetic before allocating.
        let count = invocation.public_inputs.len();
        let heads = count.checked_mul(32).ok_or("evm-calldata-limit")?;
        let mut array_size = 32usize.checked_add(heads).ok_or("evm-calldata-limit")?;
        for value in invocation.public_inputs {
            array_size = array_size
                .checked_add(32)
                .and_then(|n| n.checked_add(padded(value.len()).ok()?))
                .ok_or("evm-calldata-limit")?;
        }
        let context_size = 32usize
            .checked_add(padded(invocation.context.len())?)
            .ok_or("evm-calldata-limit")?;
        let proof_size = 32usize
            .checked_add(padded(invocation.proof.len())?)
            .ok_or("evm-calldata-limit")?;
        let size = 100usize
            .checked_add(array_size)
            .and_then(|n| n.checked_add(context_size))
            .and_then(|n| n.checked_add(proof_size))
            .ok_or("evm-calldata-limit")?;
        if size > cap("calldata_bytes", 262144)? {
            return Err("evm-calldata-limit".into());
        }
        let mut out = Vec::with_capacity(size);
        // First four bytes of Keccak-256("verify(bytes[],bytes,bytes)").
        out.extend_from_slice(&[0xa4, 0x88, 0xe1, 0xe4]);
        word(&mut out, 96);
        word(&mut out, 96 + array_size);
        word(&mut out, 96 + array_size + context_size);
        word(&mut out, count);
        let mut offset = heads;
        for value in invocation.public_inputs {
            word(&mut out, offset);
            offset += 32 + padded(value.len())?;
        }
        for value in invocation.public_inputs {
            blob(&mut out, value)?;
        }
        blob(&mut out, invocation.context)?;
        blob(&mut out, invocation.proof)?;
        Ok(out)
    }
}

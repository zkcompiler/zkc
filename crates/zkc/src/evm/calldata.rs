//! Canonical ABI encoding for the target's single verifier function.
use super::*;

/// Canonical native public wire values, invocation context, and native framed
/// proof. This adapter does not decode or reinterpret the cryptographic bytes.
pub struct Invocation<'a> {
    pub public_inputs: &'a [&'a [u8]],
    pub context: &'a [u8],
    pub proof: &'a [u8],
}

/// The declared verifier ABI.
pub(super) static ABI: std::sync::LazyLock<Value> = std::sync::LazyLock::new(|| {
    serde_json::from_str(crate::evm_target::ABI_JSON).expect("generated ABI JSON")
});

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

// Order does not affect ABI size. Named transport can therefore preflight the
// complete call before allocating its name index or descriptor-ordered slots.
fn calldata_size<'a>(
    source: &Source,
    public_inputs: impl Iterator<Item = &'a [u8]>,
    context: &[u8],
    proof: &[u8],
) -> Result<usize> {
    let limits = &source.metadata()["limits"];
    let cap = |key: &str| -> Result<usize> {
        let limit = crate::evm_target::LIMITS
            .iter()
            .find(|limit| limit.name == key)
            .expect("declared deployment ceiling");
        limits[key]
            .as_u64()
            .filter(|v| (limit.minimum..=limit.maximum).contains(v))
            .and_then(|v| usize::try_from(v).ok())
            .ok_or_else(|| "evm-source-limits".into())
    };
    let (mut public_bytes, mut array_size) = (0usize, 32usize);
    for value in public_inputs {
        public_bytes = public_bytes
            .checked_add(value.len())
            .ok_or("evm-calldata-limit")?;
        // One offset, length word and padded payload per native value.
        array_size = array_size
            .checked_add(64)
            .and_then(|n| n.checked_add(padded(value.len()).ok()?))
            .ok_or("evm-calldata-limit")?;
        if public_bytes > cap("public_bytes")? || array_size > cap("calldata_bytes")? {
            return Err("evm-calldata-limit".into());
        }
    }
    if context.len() > cap("context_bytes")? || proof.len() > cap("proof_bytes")? {
        return Err("evm-calldata-limit".into());
    }
    let size = 164usize
        .checked_add(array_size)
        .and_then(|n| n.checked_add(padded(context.len()).ok()?))
        .and_then(|n| n.checked_add(padded(proof.len()).ok()?))
        .ok_or("evm-calldata-limit")?;
    if size > cap("calldata_bytes")? {
        return Err("evm-calldata-limit".into());
    }
    Ok(size)
}

impl Artifact {
    /// Prepare public arguments by their exact admitted invocation aliases.
    /// Each alias supplies its native leaves in schema order as canonical wire
    /// frames. Products may have multiple leaves; empty inputs require `&[]`.
    /// Map order is immaterial. No logical values or cryptographic frames are
    /// encoded here; the deployed verifier retains its decoding/refusal policy.
    ///
    /// The independently admitted package Interface must match the artifact's
    /// source subject, proof policy and complete public native port/type map.
    /// Trust in compiler correspondence and descriptor codecs still rests on
    /// the caller-authenticated artifact and package publications.
    ///
    /// For an Interface whose public aliases are `statement` and `empty`:
    /// ```no_run
    /// # use zkc::{entry::BoundInterface, evm::{Artifact, Error}};
    /// # fn prepare(artifact: &Artifact, interface: &BoundInterface,
    /// #     statement_wires: &[&[u8]], proof: &[u8]) -> Result<Vec<u8>, Error> {
    /// artifact.calldata_named(interface, &[
    ///     ("empty", &[]), ("statement", statement_wires),
    /// ], b"application", proof)
    /// # }
    /// ```
    pub fn calldata_named(
        &self,
        interface: &crate::entry::BoundInterface,
        public_inputs: &[(&str, &[&[u8]])],
        context: &[u8],
        proof: &[u8],
    ) -> Result<Vec<u8>> {
        let source = self.source()?;
        let record = source.metadata();
        if record["original"] != interface.original()
            || source.entry() != interface.entry()
            || record["capture"] != interface.capture()
            || record["compiler"] != interface.toolchain()
        {
            return Err("evm-calldata-subject".into());
        }
        if !interface.is_proof() {
            return Err("evm-calldata-policy".into());
        }
        let roster = interface.evm_public_inputs();
        if public_inputs.len() != roster.len() {
            return Err("evm-calldata-names".into());
        }
        let rows = record["descriptor"][4]
            .as_array()
            .expect("captured public descriptor");
        // Bound names, counts and all ABI bytes before allocating adapter state.
        let (mut names_bytes, mut count) = (0usize, 0usize);
        for (name, wires) in public_inputs {
            names_bytes = names_bytes
                .checked_add(name.len())
                .filter(|&n| n <= crate::entry::inputs::MAX_REQUEST_BYTES)
                .ok_or("evm-calldata-limit")?;
            count = count
                .checked_add(wires.len())
                .filter(|&n| n <= rows.len())
                .ok_or("evm-calldata-width")?;
        }
        if count != rows.len() {
            return Err("evm-calldata-width".into());
        }
        calldata_size(
            &source,
            public_inputs
                .iter()
                .flat_map(|(_, wires)| wires.iter().copied()),
            context,
            proof,
        )?;
        interface
            .check_evm_policy(&record["policy"])
            .map_err(|_| "evm-calldata-policy")?;
        let mut named = std::collections::BTreeMap::new();
        for &(name, wires) in public_inputs {
            if named.insert(name, wires).is_some() {
                return Err("evm-calldata-names".into());
            }
        }
        let mut ordered = vec![None; rows.len()];
        for (name, schema, native) in roster {
            let wires = named.remove(name).ok_or("evm-calldata-names")?;
            if wires.len() != native.len() || native.len() != schema.leaves.len() {
                return Err("evm-calldata-width".into());
            }
            for ((&original, ty), &wire) in native.iter().zip(&schema.leaves).zip(wires) {
                // Captured rows and policy ports are strictly increasing. Locate
                // the original coordinate; caller order never determines it.
                let index = rows
                    .binary_search_by_key(&u64::from(original), |row| {
                        zkc_format::logical::natural_index(row[1].as_str().unwrap()).unwrap()
                    })
                    .map_err(|_| "evm-calldata-descriptor")?;
                if rows[index][2] != *ty || ordered[index].replace(wire).is_some() {
                    return Err("evm-calldata-descriptor".into());
                }
            }
        }
        if !named.is_empty() || ordered.iter().any(Option::is_none) {
            return Err("evm-calldata-descriptor".into());
        }
        let ordered: Vec<_> = ordered.into_iter().map(Option::unwrap).collect();
        self.calldata(Invocation {
            public_inputs: &ordered,
            context,
            proof,
        })
    }

    /// Encode verify(publicInputs, context, proof), with sequential offsets,
    /// zero padding and no trailing data. The immutable deployment byte caps
    /// apply before allocation; logical types and frames are checked on-chain.
    pub fn calldata(&self, invocation: Invocation<'_>) -> Result<Vec<u8>> {
        let source = self.source()?;
        let size = calldata_size(
            &source,
            invocation.public_inputs.iter().copied(),
            invocation.context,
            invocation.proof,
        )?;
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
        let mut out = Vec::with_capacity(size);
        // The declared selector of the declared verifier signature.
        out.extend_from_slice(&crate::evm_target::ABI_SELECTOR);
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

#[cfg(test)]
mod tests;

//! SHAKE128 snapshots with an explicit read cursor and no wire representation.
//!
//! The abstract state is (M, k): absorb(x) gives (M || x, 0), while
//! squeeze(n) returns SHAKE128(M)[k..k+n] and advances k. Neither read positions
//! nor absorb boundaries are encoded into M. Library code owns all framing.
use crate::{Policy, Result, Value, exhausted, refused, value::size};
use shake::{
    Shake128, Shake128Reader,
    digest::{ExtendableOutput, Update, XofReader},
};
use std::{fmt, sync::Arc};
use zkc_runtime::interactive::{
    AttributeRule, BoundSignature, Identity, KernelSignature, LogicalType, OperationBinding,
    PhysicalType, Type,
};

/// Immutable, copyable local state. There is deliberately no equality or codec.
#[derive(Clone, Default)]
pub struct Shake128State {
    absorb: Shake128,
    reader: Option<Shake128Reader>,
}
impl fmt::Debug for Shake128State {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("Shake128State")
    }
}
impl Shake128State {
    pub(crate) const RETAINED_BYTES: usize = std::mem::size_of::<Self>() + 256;

    fn absorb(&self, input: &[u8]) -> Self {
        let mut next = self.clone();
        // Empty observations reset the cursor too; this is observable behavior.
        next.reader = None;
        next.absorb.update(input);
        next
    }
    fn squeeze(&self, output: &mut [u8]) -> Self {
        let mut next = self.clone();
        next.reader
            .get_or_insert_with(|| next.absorb.clone().finalize_xof())
            .read(output);
        next
    }
}

pub(crate) fn signature(binding: &OperationBinding) -> Option<BoundSignature> {
    use Type::{Bytes, Index, Shake128State};
    if !binding.arguments.is_empty()
        || binding.implementation != format!("native/{}", binding.contract)
    {
        return None;
    }
    let (inputs, outputs): (&[Type], &[Type]) = match binding.contract.as_str() {
        "shake128.init" => (&[], &[Shake128State]),
        "shake128.absorb" => (&[Shake128State, Bytes], &[Shake128State]),
        "shake128.squeeze" => (&[Shake128State, Index], &[Shake128State, Bytes]),
        _ => return None,
    };
    let port = |kind| PhysicalType::default_for(LogicalType::new(kind, Identity::None).ok()?).ok();
    Some(KernelSignature {
        inputs: inputs.iter().copied().map(port).collect::<Option<_>>()?,
        outputs: outputs.iter().copied().map(port).collect::<Option<_>>()?,
        attributes: AttributeRule::None,
    })
}

pub(crate) fn apply(
    name: &str,
    args: &[Value],
    attributes: &[String],
    policy: &Policy,
    available: usize,
    budget: &mut crate::external_kernels::Budget,
) -> Result<Vec<Value>> {
    if !attributes.is_empty() {
        return Err(refused("shake128-attributes"));
    }
    let charge = |n: usize, budget: &mut crate::external_kernels::Budget| {
        budget.charge(crate::external::Work {
            hash_bytes: n as u64,
            // Covers the current partial block and finalization on first read.
            permutations: (n as u64).div_ceil(168) + 1,
            ..Default::default()
        })
    };
    let state = |value| Value::Shake128State(Arc::new(value));
    match (name, args) {
        ("shake128.init", []) => {
            policy.output(Shake128State::RETAINED_BYTES, available)?;
            charge(0, budget)?;
            Ok(vec![state(Shake128State::default())])
        }
        ("shake128.absorb", [Value::Shake128State(s), Value::Bytes(bytes)]) => {
            policy.bytes(bytes.len())?;
            policy.output(Shake128State::RETAINED_BYTES, available)?;
            charge(bytes.len(), budget)?;
            Ok(vec![state(s.absorb(bytes))])
        }
        ("shake128.squeeze", [Value::Shake128State(s), Value::Index(n)]) => {
            let n = usize::try_from(*n).map_err(|_| exhausted("wire-bytes"))?;
            policy.bytes(n)?;
            // Include the temporary Vec during conversion to shared storage.
            let retained = size(n, 2)?
                .checked_add(Shake128State::RETAINED_BYTES)
                .ok_or_else(|| exhausted("size-overflow"))?;
            policy.output(retained, available)?;
            charge(n, budget)?;
            let mut bytes = crate::kernels::arithmetic::reserve(n)?;
            bytes.resize(n, 0);
            let next = s.squeeze(&mut bytes);
            Ok(vec![state(next), Value::Bytes(bytes.into())])
        }
        _ => Err(refused("shake128-operands")),
    }
}

pub(crate) const IMPLEMENTATIONS: &[(&str, &str)] = &[
    ("native/shake128.init", "shake128.init"),
    ("native/shake128.absorb", "shake128.absorb"),
    ("native/shake128.squeeze", "shake128.squeeze"),
];

#[cfg(test)]
mod tests {
    use super::*;

    fn sample(state: &Shake128State, n: usize) -> (Shake128State, Vec<u8>) {
        let mut output = vec![0; n];
        (state.squeeze(&mut output), output)
    }
    fn model(message: &[u8], cursor: usize, n: usize) -> Vec<u8> {
        let mut hash = Shake128::default();
        hash.update(message);
        let mut output = vec![0; cursor + n];
        hash.finalize_xof().read(&mut output);
        output[cursor..].to_vec()
    }

    #[test]
    fn known_answer_and_snapshot_state_machine() {
        // NIST SHAKE128, empty input, first 256 output bits.
        let expected = "7f9c2ba4e88f827d616045507605853ed73b8093f6efbc88eb1a6eacfa66ef26";
        let (_, output) = sample(&Shake128State::default(), 32);
        let actual: String = output.iter().map(|b| format!("{b:02x}")).collect();
        assert_eq!(actual, expected);

        let mut state = Shake128State::default();
        let mut message = Vec::new();
        let mut cursor = 0;
        // Cross the Keccak rate and exercise repeated reads, zero reads, empty
        // absorbs, interleaved observations, and forks of a partly read stream.
        for step in 0..128usize {
            let n = [0, 1, 167, 168, 169, 1025][step % 6];
            if step % 3 == 0 {
                let bytes = vec![step as u8; n];
                state = state.absorb(&bytes);
                message.extend_from_slice(&bytes);
                cursor = 0;
            } else {
                let (next, output) = sample(&state, n);
                assert_eq!(output, model(&message, cursor, n));
                assert_eq!(sample(&state, n).1, output, "original snapshot mutated");
                assert_eq!(
                    sample(&state.absorb(b"fork"), 33).1,
                    model(&[message.as_slice(), b"fork"].concat(), 0, 33)
                );
                state = next;
                cursor += n;
            }
        }
        let base = Shake128State::default().absorb(b"ab");
        let (read, first) = sample(&base, 169);
        assert_eq!(sample(&read.absorb(&[]), 169).1, first);
        assert_eq!(
            sample(&base, 200).1,
            sample(&Shake128State::default().absorb(b"a").absorb(b"b"), 200).1
        );
    }

    #[test]
    fn pinned_spongefish_schnorr_transcript_vector() {
        use ark_ff::{BigInteger, PrimeField};
        // Independently generated with Spongefish 0.7.4 and arkworks 0.6.
        // This tests the primitive composition, not the source/Host path.
        // Upstream places the 64-byte protocol ID in a full 168-byte rate block.
        let mut domain = [0u8; 168];
        domain[..b"fiat-shamir/session-id".len()].copy_from_slice(b"fiat-shamir/session-id");
        let session_state = Shake128State::default()
            .absorb(&domain)
            .absorb(b"spongefish examples");
        let mut session = [0u8; 64];
        session_state.squeeze(&mut session[32..]);
        domain.fill(0);
        domain[..b"schnorr proof".len()].copy_from_slice(b"schnorr proof");
        let base = crate::GroupPoint::generator();
        let point = base.scale(crate::Scalar::from(7u64));
        let commitment = base.scale(crate::Scalar::from(11u64));
        let state = Shake128State::default()
            .absorb(&domain)
            .absorb(&session)
            .absorb(
                &[
                    base.to_bytes().unwrap().as_slice(),
                    point.to_bytes().unwrap().as_slice(),
                ]
                .concat(),
            )
            .absorb(&commitment.to_bytes().unwrap());
        let mut wide = [0u8; 64];
        let state = state.squeeze(&mut wide);
        let challenge = zkc_arkworks::scalar_from_wide_be(&wide);
        let response = crate::Scalar::from(11u64) + challenge * crate::Scalar::from(7u64);
        let response_bytes = response.into_bigint().to_bytes_be();
        let final_state = state.absorb(&response_bytes);
        final_state.squeeze(&mut wide);
        let next_challenge = zkc_arkworks::scalar_from_wide_be(&wide);
        let hex = |bytes: &[u8]| bytes.iter().map(|b| format!("{b:02x}")).collect::<String>();
        assert_eq!(
            hex(&challenge.into_bigint().to_bytes_be()),
            "53e1693a463c54111a66934519788ad36090083235dfae1c1d2a4b5d30c9e3c8"
        );
        assert_eq!(
            hex(&next_challenge.into_bigint().to_bytes_be()),
            "26b54ddcd1ccd27e02653f0af810e79ee631c44913d49778161c5c0743c70aff"
        );
        let proof = [
            commitment.to_bytes().unwrap().as_slice(),
            response_bytes.as_slice(),
        ]
        .concat();
        assert_eq!(
            hex(&proof),
            "80fd75ebcc0a21649e3177bcce15426da0e4f25d6828fbf4038d4d7ed3bd4421de3ef61d70f794687b12b2d571971a5507859bf81b92da0eb8accebb822293ad013c05507925f6c9cc280f9155853a7e"
        );
    }

    #[test]
    fn admission_and_charging_precede_work() {
        let policy = Policy::default();
        let mut budget = crate::external_kernels::Budget::default();
        let state = Value::Shake128State(Arc::new(Shake128State::default()));
        assert!(
            apply(
                "shake128.squeeze",
                &[state.clone(), Value::Index(u64::MAX)],
                &[],
                &policy,
                usize::MAX,
                &mut budget
            )
            .is_err()
        );
        assert_eq!(budget.spent, 0);
        assert!(
            apply(
                "shake128.absorb",
                &[state.clone(), Value::Bytes(vec![0; 168].into())],
                &[],
                &policy,
                0,
                &mut budget
            )
            .is_err()
        );
        assert_eq!(budget.spent, 0);
        budget.limit = 170;
        let args = [state, Value::Index(168)];
        assert!(
            apply(
                "shake128.squeeze",
                &args,
                &[],
                &policy,
                usize::MAX,
                &mut budget
            )
            .is_ok()
        );
        assert_eq!(budget.spent, 170);
        assert!(
            apply(
                "shake128.squeeze",
                &args,
                &[],
                &policy,
                usize::MAX,
                &mut budget
            )
            .is_err()
        );
        assert_eq!(budget.spent, 170);
        let ty = LogicalType::parse("shake128_state").unwrap();
        assert!(ty.is_duplicable() && ty.is_discardable());
        assert!(!ty.is_native_message_data());
        assert!(ty.codec().is_none());
    }
}

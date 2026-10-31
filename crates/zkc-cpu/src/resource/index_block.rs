//! Authenticated block transitions. Numerical snapshots never leave Resources.
use super::{Capability, Resources, Slot, State};
use crate::{Policy, Result, Value, exhausted, numerical::Call, refused};
use zkc_kernels::transcript::{KeccakChain, search::NonceInput};
use zkc_runtime::vm::{Identity, Invocation, Type};

#[derive(Clone, Copy)]
pub(crate) enum Mode {
    Ungated,
    Search,
    Check(u64),
}

pub(crate) struct Parameters {
    bound: u64,
    count: usize,
    difficulty: u8,
}
impl Parameters {
    pub(crate) fn parse(attributes: &[String], gated: bool) -> Result<Self> {
        if attributes.len() != if gated { 4 } else { 3 } {
            return Err(refused("kernel-attributes"));
        }
        // Validate the original template; converting arbitrary logical bytes
        // into an occurrence first could erase invalid template provenance.
        zkc_format::logical::native_query_template(&attributes[..1], "indices")
            .map_err(|_| refused("kernel-attributes"))?;
        let natural = |position| {
            let text: &String = &attributes[position];
            let value = text
                .parse::<u64>()
                .map_err(|_| refused("kernel-attributes"))?;
            if value.to_string() != *text {
                return Err(refused("kernel-attributes"));
            }
            Ok(value)
        };
        let bound = natural(1)?;
        let count = natural(2)?;
        let difficulty = if gated { natural(3)? } else { 0 };
        if !bound.is_power_of_two()
            || bound > 1 << 63
            || !(1..=1 << 20).contains(&count)
            || difficulty > 64
        {
            return Err(refused("kernel-attributes"));
        }
        Ok(Self {
            bound,
            count: usize::try_from(count).map_err(|_| refused("kernel-attributes"))?,
            difficulty: difficulty as u8,
        })
    }

    fn prefix(&self, chain: &mut KeccakChain, origin: &[u8]) {
        chain.append_message(b"origin", origin);
        chain.append_message(b"bound", &self.bound.to_le_bytes());
        chain.append_message(b"count", &(self.count as u64).to_le_bytes());
        if self.difficulty != 0 {
            chain.append_message(b"difficulty", &u64::from(self.difficulty).to_le_bytes());
        }
    }

    fn prefix_work(&self, origin_length: usize) -> Result<u64> {
        let work = absorb_work(b"origin", origin_length)?
            + absorb_work(b"bound", 8)?
            + absorb_work(b"count", 8)?;
        Ok(work
            + if self.difficulty == 0 {
                0
            } else {
                absorb_work(b"difficulty", 8)?
            })
    }
}

fn permutations(parts: &[usize]) -> Result<u64> {
    let length = parts
        .iter()
        .try_fold(0usize, |sum, part| sum.checked_add(*part))
        .ok_or_else(|| exhausted("numerical-work"))?;
    u64::try_from(length / 136 + 1).map_err(|_| exhausted("numerical-work"))
}
fn absorb_work(label: &[u8], length: usize) -> Result<u64> {
    permutations(&[
        b"zkc.hash-chain.absorb/0\0".len(),
        32,
        17,
        label.len(),
        length,
    ])
}

// Same refusal order as transition, without changing any authoritative field.
fn preflight(slot: &Slot) -> Result<()> {
    slot.budget
        .checked_sub(1)
        .ok_or_else(|| exhausted("resource-budget"))?;
    slot.generation
        .checked_add(1)
        .filter(|generation| *generation != u64::MAX)
        .ok_or_else(|| exhausted("generation"))?;
    slot.draws
        .checked_add(1)
        .ok_or_else(|| exhausted("draw-counter"))?;
    Ok(())
}
fn chain(slot: &mut Slot) -> Result<&mut KeccakChain> {
    let State::Transcript(transcript, suite) = &mut slot.state else {
        return Err(refused("transcript-suite"));
    };
    if !matches!(
        suite,
        Identity::HashChainKeccak256KoalaBearExt4 | Identity::HashChainKeccak256KoalaBearExt8
    ) {
        return Err(refused("transcript-suite"));
    }
    let crate::transcript::Transcript::HashChain(chain) = transcript.as_mut() else {
        return Err(refused("transcript-suite"));
    };
    Ok(chain)
}

impl Resources {
    pub(crate) fn transcript_indices(
        &mut self,
        token: &Capability,
        coordinates: &[u64],
        invocation: &Invocation<'_>,
        policy: &Policy,
        mode: Mode,
    ) -> Result<Vec<Value>> {
        let parameters = Parameters::parse(invocation.attributes, !matches!(mode, Mode::Ungated))?;
        if parameters.difficulty == 0 && matches!(mode, Mode::Check(witness) if witness != 0) {
            return Err(refused("gate-witness"));
        }
        policy.vector_width(parameters.count, 8)?;
        let index_bytes = parameters
            .count
            .checked_mul(8)
            .ok_or_else(|| exhausted("output-bytes"))?;
        let result_bytes = index_bytes
            .checked_add(if matches!(mode, Mode::Search) {
                1280
            } else {
                768
            })
            .ok_or_else(|| exhausted("output-bytes"))?;
        policy.output(result_bytes, invocation.max_output_bytes)?;
        let origin = zkc_format::logical::indexed_native_origin(
            &invocation.attributes[..1],
            "query",
            coordinates,
        )
        .map_err(|_| refused("transcript-origin"))?;
        let positive = parameters.difficulty != 0;
        let request_bytes = index_bytes + if positive { 8 } else { 0 };
        let label: &[u8] = if positive {
            b"gated-indices"
        } else {
            b"indices"
        };
        let prefix_work = parameters.prefix_work(origin.len())?;
        let replay_work = prefix_work
            + if positive {
                absorb_work(b"gate-witness", 14)?
            } else {
                0
            }
            + (request_bytes as u64).div_ceil(32)
                * permutations(&[
                    b"zkc.hash-chain.request/0\0".len(),
                    32,
                    17,
                    label.len(),
                    8,
                    8,
                ])?
            + absorb_work(label, 8)?;

        // Authority, frame view, custody and generation precede numerical
        // storage or prefix cloning. No live transcript snapshot API is exposed.
        let slot = self.active_slot(invocation.frame, token, Type::Transcript)?;
        preflight(slot)?;
        chain(slot)?;
        let searching = positive && matches!(mode, Mode::Search);
        let call = if searching {
            Call::with_search_nonce(policy, invocation.max_output_bytes)?
        } else {
            Call::new(policy, invocation.max_output_bytes)
        };
        // Reserve all public results before the helper's private nonce. The
        // conservative output constructor also charges final-freeze overlap.
        let mut output = call.output(parameters.count, 0u64, result_bytes)?;
        let mut request = call.scratch(request_bytes, 0u8)?;
        if searching && policy.max_search_attempts == 0 {
            return Err(exhausted("search-attempts"));
        }
        let witness = match mode {
            Mode::Search if positive => {
                call.work(prefix_work)?;
                let mut prefix = chain(slot)?.clone();
                parameters.prefix(&mut prefix, &origin);
                call.search_nonce(
                    &NonceInput {
                        chain: &prefix,
                        witness_label: b"gate-witness",
                        prefix: b"ZKCV\0\x1f",
                        suffix: b"",
                        request_label: label,
                        total_output_bytes: request_bytes as u64,
                    },
                    policy.max_search_attempts,
                    parameters.difficulty,
                )?
                .ok_or_else(|| exhausted("search-attempts"))?
            }
            Mode::Check(witness) => witness,
            _ => 0,
        };

        // Exclusive Resources access spans reauthentication, work admission,
        // atomic debit and full replay. Numerical failure cannot advance state.
        preflight(self.active_slot(invocation.frame, token, Type::Transcript)?)?;
        call.work(replay_work)?;
        let slot = self.transition(invocation.frame, token, Type::Transcript, 1)?;
        let live = chain(slot)?;
        parameters.prefix(live, &origin);
        if positive {
            let mut wire = [0u8; 14];
            wire[..6].copy_from_slice(b"ZKCV\0\x1f");
            wire[6..].copy_from_slice(&witness.to_le_bytes());
            live.append_message(b"gate-witness", &wire);
        }
        live.request(label, request.as_mut());
        let answer = request.as_ref();
        if positive
            && u64::from_le_bytes(answer[..8].try_into().expect("gate window")).trailing_zeros()
                < u32::from(parameters.difficulty)
        {
            return Err(zkc_runtime::vm::BackendError::new("rejected:require"));
        }
        for (index, bytes) in output
            .as_mut_slice()
            .iter_mut()
            .zip(answer[if positive { 8 } else { 0 }..].as_chunks::<8>().0)
        {
            *index = u64::from_le_bytes(*bytes) & (parameters.bound - 1);
        }
        let mut successor = token.clone();
        successor.generation = slot.generation;
        output.finish(|indices| {
            let mut values = vec![Value::Indices(indices.into())];
            if matches!(mode, Mode::Search) {
                values.push(Value::Index(witness));
            }
            values.push(Value::Transcript(successor));
            Ok(values)
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn attributes() -> Vec<String> {
        let tree = serde_json::json!([
            "zkc.native-origin-template/0",
            "main",
            [],
            [],
            [
                "query",
                "Source",
                "query",
                "input_0",
                "random.koala-bear.ext4-binomial3/0",
                "indices",
                "V"
            ]
        ]);
        vec![
            zkc_test_support::hex(&zkc_format::logical::encode_tree(&tree).unwrap()),
            "9223372036854775808".into(),
            "1048576".into(),
            "64".into(),
        ]
    }

    #[test]
    fn preparation_accepts_full_u64_bound_and_refuses_noncanonical_or_invalid_parameters() {
        let valid = attributes();
        let parsed = Parameters::parse(&valid, true).unwrap();
        assert_eq!(
            (parsed.bound, parsed.count, parsed.difficulty),
            (1 << 63, 1 << 20, 64)
        );
        assert!(Parameters::parse(&valid[..3], false).is_ok());
        for (position, values) in [
            (
                1,
                vec![
                    "0",
                    "3",
                    "18446744073709551615",
                    "18446744073709551616",
                    "+1",
                    "01",
                    "1 ",
                    "-1",
                ],
            ),
            (2, vec!["0", "1048577", "01", "-1"]),
            (3, vec!["65", "064", "-1", "18446744073709551616"]),
        ] {
            for value in values {
                let mut invalid = valid.clone();
                invalid[position] = value.into();
                assert_eq!(
                    Parameters::parse(&invalid, true).err().unwrap().code,
                    "refused:kernel-attributes"
                );
            }
        }
        for size in [0, 1, 2, 3] {
            assert!(Parameters::parse(&valid[..size], true).is_err());
        }
        let mut too_many = valid.clone();
        too_many.push("0".into());
        assert!(Parameters::parse(&too_many, true).is_err());
        let mut original =
            zkc_format::logical::decode_tree(&zkc_test_support::unhex(&valid[0])).unwrap();
        for method in ["draw", "index"] {
            original[4][5] = serde_json::json!(method);
            let mut invalid = valid.clone();
            invalid[0] =
                zkc_test_support::hex(&zkc_format::logical::encode_tree(&original).unwrap());
            assert!(Parameters::parse(&invalid, true).is_err());
        }
        original[4][5] = serde_json::json!("indices");
        original[0] = serde_json::json!("zkc.native-origin/0");
        let mut invalid = valid.clone();
        invalid[0] = zkc_test_support::hex(&zkc_format::logical::encode_tree(&original).unwrap());
        assert!(Parameters::parse(&invalid, true).is_err());
    }

    #[test]
    fn atomic_block_preflight_preserves_overflowing_counters_and_refusal_order() {
        let mut resources = Resources::new(Policy::default());
        let root = zkc_format::logical::encode_tree(&serde_json::json!(["fixture"])).unwrap();
        let value = resources
            .issue_transcript_for(
                Identity::HashChainKeccak256KoalaBearExt4,
                crate::Domain::new("P", "session", "main", None),
                1,
                &root,
            )
            .unwrap();
        let token = value.capability().unwrap();
        let slot = resources.slots.get_mut(&token.id).unwrap();
        for (budget, generation, draws, expected) in [
            (0, u64::MAX, u64::MAX, "exhausted:resource-budget"),
            (1, u64::MAX - 1, u64::MAX, "exhausted:generation"),
            (1, 0, u64::MAX, "exhausted:draw-counter"),
        ] {
            slot.budget = budget;
            slot.generation = generation;
            slot.draws = draws;
            assert_eq!(preflight(slot).unwrap_err().code, expected);
            assert_eq!(
                (slot.budget, slot.generation, slot.draws),
                (budget, generation, draws)
            );
        }
    }
}

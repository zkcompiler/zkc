//! Suite-specific byte state. The capability store owns this non-Clone wrapper.
//! zkc defines the byte framing; upstream supplies the duplex, permutation or
//! byte hash. This is not spongefish's default SHAKE/DomainSeparator protocol.
//! The hash-chain suites are zkc's own construction over a byte hash; see
//! docs/spec/ir/construction.md#native-hash-chain-suites.
use crate::{Result, refused};
use spongefish::{DuplexSpongeInterface, instantiations::Keccak};
use zkc_kernels::transcript::{KeccakChain, write_frame as frame_into};
use zkc_runtime::vm::Identity;

pub(crate) enum Transcript {
    Merlin(merlin::Transcript),
    Spongefish(Keccak),
    HashChain(KeccakChain),
}

// Frame kinds: fixed domain data, an absorbed message and a request. Each frame
// is tag:u8 || label_len:u64be || label || data_len:u64be || data, so a
// concatenation of frames parses uniquely.
const FIXED: u8 = 0;
const MESSAGE: u8 = 1;
const REQUEST: u8 = 2;

// absorb is associative in spongefish: call boundaries carry no information.
fn frame(sponge: &mut Keccak, tag: u8, label: &[u8], data: &[u8]) {
    frame_into(
        |bytes| {
            sponge.absorb(bytes);
        },
        tag,
        label,
        data,
    );
}

// Canonical framing does not authenticate the root's provenance.
fn check_root(root: &[u8]) -> Result<()> {
    zkc_format::logical::decode_tree(root).map_err(|_| refused("transcript-root"))?;
    Ok(())
}

impl Transcript {
    pub(crate) fn new(suite: Identity, root: &[u8]) -> Result<Self> {
        let mut result = match suite {
            Identity::Merlin3Fr64Be
            | Identity::Merlin3Ristretto64Le
            | Identity::Merlin3KoalaBearExt8
            | Identity::Merlin3BabyBearExt4
            | Identity::Merlin3GoldilocksExt2 => {
                Self::Merlin(merlin::Transcript::new(b"zkc.artifact/0"))
            }
            Identity::Spongefish080KeccakFr64Be => {
                let mut sponge = Keccak::default();
                frame(&mut sponge, FIXED, b"domain", b"zkc.artifact/0");
                frame(&mut sponge, FIXED, b"suite", suite.name().as_bytes());
                Self::Spongefish(sponge)
            }
            Identity::HashChainKeccak256Fr64Be
            | Identity::HashChainKeccak256KoalaBearExt8
            | Identity::HashChainKeccak256KoalaBearExt4 => {
                check_root(root)?;
                // The binding is the chain's initial input, not a later event.
                return Ok(Self::HashChain(KeccakChain::bind(suite.name(), root)));
            }
            _ => return Err(refused("transcript-suite")),
        };
        check_root(root)?;
        if matches!(
            suite,
            Identity::Merlin3BabyBearExt4 | Identity::Merlin3GoldilocksExt2
        ) {
            result.append_message(b"suite", suite.name().as_bytes());
        }
        result.append_message(b"binding", root);
        Ok(result)
    }
    pub(crate) fn append_message(&mut self, label: &'static [u8], value: &[u8]) {
        match self {
            Self::Merlin(t) => t.append_message(label, value),
            Self::Spongefish(t) => frame(t, MESSAGE, label, value),
            Self::HashChain(t) => t.append_message(label, value),
        }
    }
    pub(crate) fn challenge_bytes(&mut self, label: &'static [u8], output: &mut [u8; 64]) {
        match self {
            Self::Merlin(t) => t.challenge_bytes(label, output),
            Self::Spongefish(t) => {
                frame(t, REQUEST, label, &64u64.to_be_bytes());
                t.squeeze(output);
            }
            Self::HashChain(t) => t.request(label, output),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn resident_canonical_frames_preserve_transcript_bytes_and_successor_state() {
        use crate::{Bls12381G2, CpuBackend, Domain, EntryPolicy, G1, Policy, Scalar, Value};
        use zkc_runtime::host::wire::WireBackend;
        use zkc_runtime::vm::Value as _;
        let codec = CpuBackend::new(
            Policy::default(),
            EntryPolicy::new(Domain::new("P", "session", "main", None), None),
            Default::default(),
        )
        .unwrap();
        let root =
            zkc_format::logical::encode_tree(&serde_json::json!(["transcript-fixture"])).unwrap();
        let samples = [
            Value::Field(Scalar::from(7)),
            Value::Vector(vec![Scalar::from(0), Scalar::from(7)].into()),
            Value::Curve((G1::generator()).into()),
            Value::Groups(vec![G1::identity(), G1::generator()].into()),
            Value::Bls12381G2((Bls12381G2::generator()).into()),
            Value::Bls12381G2Vector(vec![Bls12381G2::identity(), Bls12381G2::generator()].into()),
        ];
        for suite in [
            Identity::Merlin3Fr64Be,
            Identity::Spongefish080KeccakFr64Be,
            Identity::HashChainKeccak256Fr64Be,
        ] {
            let mut ark_state = Transcript::new(suite, &root).unwrap();
            let mut resident_state = Transcript::new(suite, &root).unwrap();
            for ark in &samples {
                let ty = ark.physical_type();
                let logical = ty.logical();
                let representation = match logical.identity() {
                    Identity::Bls12381Fr => "blst/fr",
                    Identity::Bls12381G1 => "blst/g1",
                    Identity::Bls12381G2 => "blst/g2",
                    _ => unreachable!(),
                };
                let ty = crate::cpu_contracts()
                    .physical_type(&format!("{}@{representation}", logical.spelling()))
                    .unwrap();
                let ark_bytes = codec.encode_wire(ark).unwrap();
                let resident = codec.decode_wire(&ty, &ark_bytes).unwrap();
                let resident_bytes = codec.encode_wire(&resident).unwrap();
                assert_eq!(ark_bytes, resident_bytes);
                // Use the existing framing and state transitions. Each request
                // advances both actual suite states, including the second draw.
                ark_state.append_message(b"origin", b"same-origin");
                ark_state.append_message(b"value", &ark_bytes);
                resident_state.append_message(b"origin", b"same-origin");
                resident_state.append_message(b"value", &resident_bytes);
                let mut previous = None;
                for _ in 0..2 {
                    let mut ark_challenge = [0; 64];
                    let mut resident_challenge = [0; 64];
                    ark_state.challenge_bytes(b"challenge", &mut ark_challenge);
                    resident_state.challenge_bytes(b"challenge", &mut resident_challenge);
                    assert_eq!(ark_challenge, resident_challenge);
                    assert_ne!(previous, Some(ark_challenge));
                    previous = Some(ark_challenge);
                }
            }
        }
    }

    /// Every primitive step against the independent reference, including two
    /// requests with no event between them, which differ because a request
    /// advances the state.
    #[test]
    fn chain_states_and_outputs_match_the_reference_vectors() {
        let mut vectors: serde_json::Value = serde_json::from_str(
            &std::fs::read_to_string(zkc_test_support::source("hash-chain-vectors.json")).unwrap(),
        )
        .unwrap();
        vectors["suites"].as_array_mut().unwrap().push(
            serde_json::from_str(include_str!("../tests/common/quartic-hash-chain.json")).unwrap(),
        );
        let hex = |v: &serde_json::Value| zkc_test_support::unhex(v.as_str().unwrap());
        for vector in vectors["suites"].as_array().unwrap() {
            let suite = Identity::parse(vector["suite"].as_str().unwrap()).unwrap();
            let Transcript::HashChain(mut chain) =
                Transcript::new(suite, &hex(&vector["root"])).unwrap()
            else {
                panic!("hash-chain suite")
            };
            let steps = vector["steps"].as_array().unwrap();
            assert_eq!(chain.state().to_vec(), hex(&steps[0]["state"]));
            let mut outputs = Vec::new();
            for step in &steps[1..] {
                if let Some([label, data]) = step["absorb"].as_array().map(Vec::as_slice) {
                    chain.append_message(label.as_str().unwrap().as_bytes(), &hex(data));
                } else {
                    let request = step["request"].as_array().unwrap();
                    let mut output = vec![0; request[1].as_u64().unwrap() as usize];
                    chain.request(request[0].as_str().unwrap().as_bytes(), &mut output);
                    assert_eq!(output, hex(&step["output"]));
                    outputs.push(output);
                }
                assert_eq!(chain.state().to_vec(), hex(&step["state"]));
            }
            assert!(outputs.windows(2).all(|w| w[0] != w[1]));
        }
    }

    #[test]
    fn short_and_long_requests_use_counter_blocks() {
        let root = zkc_format::logical::encode_tree(&serde_json::json!(["root"])).unwrap();
        let fresh = || {
            let Transcript::HashChain(chain) =
                Transcript::new(Identity::HashChainKeccak256Fr64Be, &root).unwrap()
            else {
                panic!("hash-chain suite")
            };
            chain
        };
        let start = *fresh().state();
        let mut long = fresh();
        let mut output = [0; 70];
        long.request(b"label", &mut output);
        let length = 70u64.to_be_bytes();
        let block = |counter: u64| {
            use sha3::{Digest, Keccak256};
            let mut hash = Keccak256::new();
            hash.update(b"zkc.hash-chain.request/0\0");
            hash.update(start);
            hash.update([2]);
            hash.update(5u64.to_be_bytes());
            hash.update(b"label");
            hash.update(8u64.to_be_bytes());
            hash.update(length);
            hash.update(counter.to_be_bytes());
            <[u8; 32]>::from(hash.finalize())
        };
        assert_eq!(&output[..32], &block(0));
        assert_eq!(&output[32..64], &block(1));
        assert_eq!(&output[64..], &block(2)[..6]);
        // The requested length is part of the request: a shorter request is
        // not a prefix of a longer one.
        let mut short = fresh();
        let mut prefix = [0; 32];
        short.request(b"label", &mut prefix);
        assert_ne!(prefix, output[..32]);
        assert_ne!(short.state(), long.state());
    }
}

#[cfg(test)]
mod residue_profile_tests {
    use super::*;
    #[test]
    fn exact_merlin_bytes_replay_and_separate_new_suites() {
        let root =
            zkc_format::logical::encode_tree(&serde_json::json!(["residue-profile-fixture"]))
                .unwrap();
        let mut first = Vec::new();
        for (suite, field) in [
            (Identity::Merlin3BabyBearExt4, Identity::BabyBearExt4),
            (Identity::Merlin3GoldilocksExt2, Identity::GoldilocksExt2),
        ] {
            assert_eq!(suite.scalar_field(), Some(field));
            let mut actual = Transcript::new(suite, &root).unwrap();
            let mut upstream = merlin::Transcript::new(b"zkc.artifact/0");
            upstream.append_message(b"suite", suite.name().as_bytes());
            upstream.append_message(b"binding", &root);
            for _ in 0..3 {
                actual.append_message(b"origin", b"draw");
                upstream.append_message(b"origin", b"draw");
                let (mut x, mut y) = ([0; 64], [0; 64]);
                actual.challenge_bytes(b"challenge", &mut x);
                upstream.challenge_bytes(b"challenge", &mut y);
                assert_eq!(x, y);
                first.push(x);
            }
        }
        assert_ne!(first[0], first[3]);
        assert_ne!(first[0], first[1]);
    }
}

//! Suite-specific byte state. The capability store owns this non-Clone wrapper.
//! zkc defines the byte framing; upstream supplies the duplex, permutation or
//! byte hash. This is not spongefish's default SHAKE/DomainSeparator protocol.
//! The hash-chain suites are zkc's own construction over a byte hash; see
//! docs/spec/ir/construction.md#native-hash-chain-suites.
use crate::{Result, refused};
use sha3::{Digest, Keccak256};
use spongefish::{DuplexSpongeInterface, instantiations::Keccak};
use zkc_runtime::interactive::Identity;

pub(crate) enum Transcript {
    Merlin(merlin::Transcript),
    Spongefish(Keccak),
    HashChain(HashChain),
}

// Frame kinds: fixed domain data, an absorbed message and a request. Each frame
// is tag:u8 || label_len:u64be || label || data_len:u64be || data, so a
// concatenation of frames parses uniquely.
const FIXED: u8 = 0;
const MESSAGE: u8 = 1;
const REQUEST: u8 = 2;

fn frame_into(mut write: impl FnMut(&[u8]), tag: u8, label: &[u8], data: &[u8]) {
    write(&[tag]);
    write(&(label.len() as u64).to_be_bytes());
    write(label);
    write(&(data.len() as u64).to_be_bytes());
    write(data);
}

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

/// The byte hash of a hash-chain suite. Every instance has a 32-byte digest,
/// which is also the size of a chain state.
#[derive(Clone, Copy)]
pub(crate) enum ChainHash {
    Keccak256,
}

// Every primitive input starts with one of these role tags. No tag is a prefix
// of another, so binding, absorption and request inputs never coincide.
const BIND_TAG: &[u8] = b"zkc.hash-chain.bind/0\0";
const ABSORB_TAG: &[u8] = b"zkc.hash-chain.absorb/0\0";
const REQUEST_TAG: &[u8] = b"zkc.hash-chain.request/0\0";

/// A chain whose state is one full digest. The initial state hashes the
/// binding, an event hashes the current state with the framed event, and the
/// answer to a request hashes the state with the framed request and a block
/// counter. A request then advances the state by absorbing its request frame.
pub(crate) struct HashChain {
    hash: ChainHash,
    state: [u8; 32],
}

impl HashChain {
    fn digest(hash: ChainHash, input: impl FnOnce(&mut dyn FnMut(&[u8]))) -> [u8; 32] {
        match hash {
            ChainHash::Keccak256 => {
                let mut h = Keccak256::new();
                input(&mut |bytes: &[u8]| h.update(bytes));
                h.finalize().into()
            }
        }
    }
    fn bind(hash: ChainHash, suite: &str, root: &[u8]) -> Self {
        let state = Self::digest(hash, |write| {
            write(BIND_TAG);
            frame_into(&mut *write, FIXED, b"domain", b"zkc.artifact/0");
            frame_into(&mut *write, FIXED, b"suite", suite.as_bytes());
            frame_into(&mut *write, MESSAGE, b"binding", root);
        });
        Self { hash, state }
    }
    fn absorb(&mut self, tag: u8, label: &[u8], data: &[u8]) {
        let state = self.state;
        self.state = Self::digest(self.hash, |write| {
            write(ABSORB_TAG);
            write(&state);
            frame_into(&mut *write, tag, label, data);
        });
    }
    /// Output longer than one digest is the concatenation of the blocks for
    /// counters 0, 1, ..., truncated to the requested length.
    fn request(&mut self, label: &[u8], output: &mut [u8]) {
        let length = (output.len() as u64).to_be_bytes();
        let state = self.state;
        for (counter, block) in output.chunks_mut(32).enumerate() {
            let digest = Self::digest(self.hash, |write| {
                write(REQUEST_TAG);
                write(&state);
                frame_into(&mut *write, REQUEST, label, &length);
                write(&(counter as u64).to_be_bytes());
            });
            block.copy_from_slice(&digest[..block.len()]);
        }
        self.absorb(REQUEST, label, &length);
    }
}

// Canonical framing does not authenticate the root's provenance.
fn check_root(root: &[u8]) -> Result<()> {
    zkc_runtime::logical::decode_tree(root).map_err(|_| refused("transcript-root"))?;
    Ok(())
}

impl Transcript {
    pub(crate) fn new(suite: Identity, root: &[u8]) -> Result<Self> {
        let mut result = match suite {
            Identity::Merlin3Fr64Be
            | Identity::Merlin3Ristretto64Le
            | Identity::Merlin3KoalaBearExt8 => {
                Self::Merlin(merlin::Transcript::new(b"zkc.artifact/0"))
            }
            Identity::Spongefish080KeccakFr64Be => {
                let mut sponge = Keccak::default();
                frame(&mut sponge, FIXED, b"domain", b"zkc.artifact/0");
                frame(&mut sponge, FIXED, b"suite", suite.name().as_bytes());
                Self::Spongefish(sponge)
            }
            Identity::HashChainKeccak256Fr64Be | Identity::HashChainKeccak256KoalaBearExt8 => {
                check_root(root)?;
                // The binding is the chain's initial input, not a later event.
                return Ok(Self::HashChain(HashChain::bind(
                    ChainHash::Keccak256,
                    suite.name(),
                    root,
                )));
            }
            _ => return Err(refused("transcript-suite")),
        };
        check_root(root)?;
        result.append_message(b"binding", root);
        Ok(result)
    }
    pub(crate) fn append_message(&mut self, label: &'static [u8], value: &[u8]) {
        match self {
            Self::Merlin(t) => t.append_message(label, value),
            Self::Spongefish(t) => frame(t, MESSAGE, label, value),
            Self::HashChain(t) => t.absorb(MESSAGE, label, value),
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

    /// Every primitive step against the independent reference, including two
    /// requests with no event between them, which differ because a request
    /// advances the state.
    #[test]
    fn chain_states_and_outputs_match_the_reference_vectors() {
        let vectors: serde_json::Value = serde_json::from_str(
            &std::fs::read_to_string(zkc_test_support::source("hash-chain-vectors.json")).unwrap(),
        )
        .unwrap();
        let hex = |v: &serde_json::Value| zkc_test_support::unhex(v.as_str().unwrap());
        for vector in vectors["suites"].as_array().unwrap() {
            let suite = Identity::parse(vector["suite"].as_str().unwrap()).unwrap();
            let Transcript::HashChain(mut chain) =
                Transcript::new(suite, &hex(&vector["root"])).unwrap()
            else {
                panic!("hash-chain suite")
            };
            let steps = vector["steps"].as_array().unwrap();
            assert_eq!(chain.state.to_vec(), hex(&steps[0]["state"]));
            let mut outputs = Vec::new();
            for step in &steps[1..] {
                if let Some([label, data]) = step["absorb"].as_array().map(Vec::as_slice) {
                    chain.absorb(MESSAGE, label.as_str().unwrap().as_bytes(), &hex(data));
                } else {
                    let request = step["request"].as_array().unwrap();
                    let mut output = vec![0; request[1].as_u64().unwrap() as usize];
                    chain.request(request[0].as_str().unwrap().as_bytes(), &mut output);
                    assert_eq!(output, hex(&step["output"]));
                    outputs.push(output);
                }
                assert_eq!(chain.state.to_vec(), hex(&step["state"]));
            }
            assert!(outputs.windows(2).all(|w| w[0] != w[1]));
        }
    }

    #[test]
    fn short_and_long_requests_use_counter_blocks() {
        let root = zkc_runtime::logical::encode_tree(&serde_json::json!(["root"])).unwrap();
        let fresh = || {
            let Transcript::HashChain(chain) =
                Transcript::new(Identity::HashChainKeccak256Fr64Be, &root).unwrap()
            else {
                panic!("hash-chain suite")
            };
            chain
        };
        let start = fresh().state;
        let mut long = fresh();
        let mut output = [0; 70];
        long.request(b"label", &mut output);
        let length = 70u64.to_be_bytes();
        let block = |counter: u64| {
            HashChain::digest(ChainHash::Keccak256, |write| {
                write(REQUEST_TAG);
                write(&start);
                frame_into(&mut *write, REQUEST, b"label", &length);
                write(&counter.to_be_bytes());
            })
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
        assert_ne!(short.state, long.state);
    }
}

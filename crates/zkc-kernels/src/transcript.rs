//! Pure hash-chain byte operations. A state is numerical data, not a transcript
//! capability: admission, custody, binding provenance and live successor
//! publication belong to the caller.
use sha3::{Digest, Keccak256};

pub mod search;

const FIXED: u8 = 0;
const MESSAGE: u8 = 1;
const REQUEST: u8 = 2;
const BIND_TAG: &[u8] = b"zkc.hash-chain.bind/0\0";
const ABSORB_TAG: &[u8] = b"zkc.hash-chain.absorb/0\0";
const REQUEST_TAG: &[u8] = b"zkc.hash-chain.request/0\0";

fn write_frame_header(mut write: impl FnMut(&[u8]), tag: u8, label: &[u8], length: u64) {
    write(&[tag]);
    write(&(label.len() as u64).to_be_bytes());
    write(label);
    write(&length.to_be_bytes());
}

/// Unambiguous framing shared by the byte-chain and duplex implementations.
pub fn write_frame(mut write: impl FnMut(&[u8]), tag: u8, label: &[u8], data: &[u8]) {
    write_frame_header(&mut write, tag, label, data.len() as u64);
    write(data);
}

fn write_request(
    mut write: impl FnMut(&[u8]),
    state: &[u8; 32],
    label: &[u8],
    length: u64,
    counter: u64,
) {
    write(REQUEST_TAG);
    write(state);
    write_frame(&mut write, REQUEST, label, &length.to_be_bytes());
    write(&counter.to_be_bytes());
}

fn digest(input: impl FnOnce(&mut dyn FnMut(&[u8]))) -> [u8; 32] {
    let mut hash = Keccak256::new();
    input(&mut |bytes| hash.update(bytes));
    hash.finalize().into()
}

/// Immutable snapshots may be copied for private numerical evaluation. They do
/// not authorize runtime operations or replace a live-context recheck.
#[derive(Clone)]
pub struct KeccakChain {
    state: [u8; 32],
}

impl KeccakChain {
    /// Bind exact caller-supplied suite and root bytes. Canonical root admission
    /// and authentication remain the caller's responsibility.
    pub fn bind(suite: &str, root: &[u8]) -> Self {
        Self {
            state: digest(|write| {
                write(BIND_TAG);
                write_frame(&mut *write, FIXED, b"domain", b"zkc.artifact/0");
                write_frame(&mut *write, FIXED, b"suite", suite.as_bytes());
                write_frame(&mut *write, MESSAGE, b"binding", root);
            }),
        }
    }

    pub fn state(&self) -> &[u8; 32] {
        &self.state
    }

    fn absorb(&mut self, tag: u8, label: &[u8], data: &[u8]) {
        let state = self.state;
        self.state = digest(|write| {
            write(ABSORB_TAG);
            write(&state);
            write_frame(&mut *write, tag, label, data);
        });
    }

    pub fn append_message(&mut self, label: &[u8], data: &[u8]) {
        self.absorb(MESSAGE, label, data);
    }

    /// Bind the final requested length, concatenate counter blocks, then absorb
    /// the request once. Even an empty output advances the state.
    pub fn request(&mut self, label: &[u8], output: &mut [u8]) {
        let output_length = output.len() as u64;
        let length = output_length.to_be_bytes();
        let state = self.state;
        for (counter, block) in output.chunks_mut(32).enumerate() {
            let value = digest(|write| {
                write_request(write, &state, label, output_length, counter as u64);
            });
            block.copy_from_slice(&value[..block.len()]);
        }
        self.absorb(REQUEST, label, &length);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn exact_states_and_request_blocks_match_independent_vectors() {
        let vectors: serde_json::Value = serde_json::from_str(
            &std::fs::read_to_string(zkc_test_support::source("hash-chain-vectors.json")).unwrap(),
        )
        .unwrap();
        let bytes = |value: &serde_json::Value| zkc_test_support::unhex(value.as_str().unwrap());
        for vector in vectors["suites"].as_array().unwrap() {
            let mut chain =
                KeccakChain::bind(vector["suite"].as_str().unwrap(), &bytes(&vector["root"]));
            let steps = vector["steps"].as_array().unwrap();
            assert_eq!(chain.state().as_slice(), bytes(&steps[0]["state"]));
            for step in &steps[1..] {
                if let Some([label, data]) = step["absorb"].as_array().map(Vec::as_slice) {
                    chain.append_message(label.as_str().unwrap().as_bytes(), &bytes(data));
                } else {
                    let request = step["request"].as_array().unwrap();
                    let mut output = vec![0; request[1].as_u64().unwrap() as usize];
                    chain.request(request[0].as_str().unwrap().as_bytes(), &mut output);
                    assert_eq!(output, bytes(&step["output"]));
                }
                assert_eq!(chain.state().as_slice(), bytes(&step["state"]));
            }
        }
    }

    #[test]
    fn numerical_snapshots_do_not_advance_the_original_state() {
        let original = KeccakChain::bind("quartic-test-only", b"independent-root-bytes");
        let state = *original.state();
        let mut snapshot = original.clone();
        snapshot.append_message(b"message", b"payload");
        snapshot.request(b"empty", &mut []);
        assert_eq!(*original.state(), state);
        assert_ne!(snapshot.state(), original.state());
    }
}

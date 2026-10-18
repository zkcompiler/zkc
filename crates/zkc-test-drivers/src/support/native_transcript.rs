//! Independent transcript/framing oracle. It calls upstream Merlin/Spongefish,
//! Keccak-256 and Arkworks arithmetic, without the host's root/origin/transition
//! constructors.
use ark_ff::PrimeField;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use serde_json::{Value as Json, json};
use spongefish::{DuplexSpongeInterface, instantiations::Keccak};
use zkc_backends::{GroupPoint, Scalar};

pub fn tree(v: &Json) -> Vec<u8> {
    match v {
        Json::String(s) => [
            vec![0],
            (s.len() as u64).to_le_bytes().to_vec(),
            s.as_bytes().to_vec(),
        ]
        .concat(),
        Json::Array(a) => [
            vec![1],
            (a.len() as u64).to_le_bytes().to_vec(),
            a.iter().flat_map(tree).collect(),
        ]
        .concat(),
        _ => panic!("fixture tree"),
    }
}
pub fn scalar_wire(value: Scalar) -> Vec<u8> {
    let mut bytes = b"ZKCV\x00\x01".to_vec();
    value.serialize_compressed(&mut bytes).unwrap();
    bytes
}
pub fn scalar(bytes: &[u8]) -> Scalar {
    assert_eq!(&bytes[..6], b"ZKCV\x00\x01");
    assert_eq!(bytes.len(), 38);
    Scalar::deserialize_compressed(&bytes[6..]).unwrap()
}
pub fn group(bytes: &[u8]) -> GroupPoint {
    assert_eq!(&bytes[..6], b"ZKCV\x00\x09");
    GroupPoint::from_bytes(&bytes[6..]).unwrap()
}
pub enum Transcript {
    Merlin(Box<merlin::Transcript>),
    Spongefish(Box<Keccak>),
    /// The current full Keccak-256 state of a hash-chain suite.
    HashChain([u8; 32]),
}
fn framed(tag: u8, label: &[u8], value: &[u8]) -> Vec<u8> {
    [
        &[tag][..],
        &(label.len() as u64).to_be_bytes(),
        label,
        &(value.len() as u64).to_be_bytes(),
        value,
    ]
    .concat()
}
fn frame(sponge: &mut Keccak, tag: u8, label: &[u8], value: &[u8]) {
    sponge.absorb(&framed(tag, label, value));
}
fn keccak256(parts: &[&[u8]]) -> [u8; 32] {
    use sha3::Digest;
    sha3::Keccak256::digest(parts.concat()).into()
}
const CHAIN_ABSORB: &[u8] = b"zkc.hash-chain.absorb/0\0";
const CHAIN_REQUEST: &[u8] = b"zkc.hash-chain.request/0\0";
impl Transcript {
    pub fn new(suite: &str, root: &[u8]) -> Self {
        if suite.starts_with("hash-chain.keccak256.") {
            return Self::HashChain(keccak256(&[
                b"zkc.hash-chain.bind/0\0",
                &framed(0, b"domain", b"zkc.artifact/0"),
                &framed(0, b"suite", suite.as_bytes()),
                &framed(1, b"binding", root),
            ]));
        }
        let mut t = if suite.starts_with("merlin") {
            Self::Merlin(Box::new(merlin::Transcript::new(b"zkc.artifact/0")))
        } else {
            let mut sponge = Keccak::default();
            frame(&mut sponge, 0, b"domain", b"zkc.artifact/0");
            frame(&mut sponge, 0, b"suite", suite.as_bytes());
            Self::Spongefish(Box::new(sponge))
        };
        t.absorb(b"binding", root);
        t
    }
    pub fn absorb(&mut self, label: &'static [u8], value: &[u8]) {
        match self {
            Self::Merlin(t) => t.append_message(label, value),
            Self::Spongefish(t) => frame(t, 1, label, value),
            Self::HashChain(state) => {
                *state = keccak256(&[CHAIN_ABSORB, state, &framed(1, label, value)])
            }
        }
    }
    /// One 64-byte request under `label`.
    pub fn challenge_bytes(&mut self, label: &'static [u8], bytes: &mut [u8; 64]) {
        match self {
            Self::Merlin(t) => t.challenge_bytes(label, bytes),
            Self::Spongefish(t) => {
                frame(t, 2, label, &64u64.to_be_bytes());
                t.squeeze(bytes);
            }
            Self::HashChain(state) => {
                // Two counter blocks answer the 64-byte request; the request
                // frame is then absorbed as the next event.
                let request = framed(2, label, &64u64.to_be_bytes());
                for (counter, half) in bytes.chunks_mut(32).enumerate() {
                    let counter = (counter as u64).to_be_bytes();
                    half.copy_from_slice(&keccak256(&[CHAIN_REQUEST, state, &request, &counter]));
                }
                *state = keccak256(&[CHAIN_ABSORB, state, &request]);
            }
        }
    }
    pub fn draw(&mut self) -> Scalar {
        let mut bytes = [0; 64];
        self.challenge_bytes(b"challenge", &mut bytes);
        Scalar::from_be_bytes_mod_order(&bytes)
    }
}
pub fn root(envelope: &Json, input: &Json) -> Vec<u8> {
    let policy = &envelope[2][1];
    let public = input[1]
        .as_array()
        .unwrap()
        .iter()
        .zip(envelope[2][4].as_array().unwrap())
        .map(|(v, p)| json!([v[0], v[1], p[2], v[2]]))
        .collect::<Vec<_>>();
    tree(&json!([
        "zkc.native-proof-binding/0",
        "sha256",
        "zkc.native-origin/0",
        envelope[1],
        policy[1],
        policy[2],
        policy[3],
        envelope[2],
        public,
        input[3]
    ]))
}

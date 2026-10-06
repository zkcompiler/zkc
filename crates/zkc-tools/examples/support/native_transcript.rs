//! Independent transcript/framing oracle. It calls upstream Merlin/Spongefish and
//! Arkworks arithmetic, without the host's root/origin/transition constructors.
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
    let mut bytes = b"ZKCV\x01\x01".to_vec();
    value.serialize_compressed(&mut bytes).unwrap();
    bytes
}
pub fn scalar(bytes: &[u8]) -> Scalar {
    assert_eq!(&bytes[..6], b"ZKCV\x01\x01");
    assert_eq!(bytes.len(), 38);
    Scalar::deserialize_compressed(&bytes[6..]).unwrap()
}
pub fn group(bytes: &[u8]) -> GroupPoint {
    assert_eq!(&bytes[..6], b"ZKCV\x01\x09");
    GroupPoint::from_bytes(&bytes[6..]).unwrap()
}
pub enum Transcript {
    Merlin(Box<merlin::Transcript>),
    Spongefish(Box<Keccak>),
}
fn frame(sponge: &mut Keccak, tag: u8, label: &[u8], value: &[u8]) {
    let bytes = [
        &[tag][..],
        &(label.len() as u64).to_be_bytes(),
        label,
        &(value.len() as u64).to_be_bytes(),
        value,
    ]
    .concat();
    sponge.absorb(&bytes);
}
impl Transcript {
    pub fn new(suite: &str, root: &[u8]) -> Self {
        let mut t = if suite.starts_with("merlin") {
            Self::Merlin(Box::new(merlin::Transcript::new(b"zkc.artifact/1")))
        } else {
            let mut sponge = Keccak::default();
            frame(&mut sponge, 0, b"domain", b"zkc.artifact/1");
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
        }
    }
    pub fn draw(&mut self) -> Scalar {
        let mut bytes = [0; 64];
        match self {
            Self::Merlin(t) => t.challenge_bytes(b"challenge", &mut bytes),
            Self::Spongefish(t) => {
                frame(t, 2, b"challenge", &64u64.to_be_bytes());
                t.squeeze(&mut bytes);
            }
        }
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
    let version = envelope[0].as_str().unwrap().rsplit('/').next().unwrap();
    let iterated = version != "1";
    tree(&json!([
        format!("zkc.native-proof-binding/{version}"),
        "sha256",
        if iterated {
            "zkc.native-origin/2"
        } else {
            "zkc.native-origin/1"
        },
        envelope[1],
        policy[1],
        policy[2],
        policy[3],
        envelope[2],
        public,
        input[3],
        [],
        [],
        []
    ]))
}

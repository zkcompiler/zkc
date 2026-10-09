//! Reference equations and byte framing, independent of compiler lowering and
//! native kernel dispatch. Only upstream transcript and arithmetic primitives
//! are shared with execution.
// This writer uses the shared oracle framing helpers, not its proof readers.
#[allow(dead_code)]
#[path = "../support/native_transcript.rs"]
mod transcript;
use ark_ff::Field;
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use transcript::{Transcript, scalar_wire, tree};
use zkc_backends::{GroupPoint, Scalar};
use zkc_test_support::hex;

pub fn msm(a: &[Scalar], g: &[GroupPoint]) -> GroupPoint {
    assert_eq!(a.len(), g.len());
    a.iter()
        .zip(g)
        .fold(GroupPoint::identity(), |sum, (a, g)| sum.add(&g.scale(*a)))
}
fn group_wire(g: &GroupPoint) -> Vec<u8> {
    [b"ZKCV\x00\x09".as_slice(), &g.to_bytes().unwrap()].concat()
}
fn vector(a: &[Scalar]) -> Vec<u8> {
    let mut bytes = b"ZKCV\x00\x42".to_vec();
    bytes.extend_from_slice(&(a.len() as u32).to_le_bytes());
    for x in a {
        bytes.extend_from_slice(&scalar_wire(*x)[6..]);
    }
    bytes
}
fn groups(g: &[GroupPoint]) -> Vec<u8> {
    let mut bytes = b"ZKCV\x00\x43".to_vec();
    bytes.extend_from_slice(&(g.len() as u32).to_le_bytes());
    for x in g {
        bytes.extend_from_slice(&x.to_bytes().unwrap());
    }
    bytes
}
struct Writer<'a> {
    entry: &'a str,
    descriptor: &'a Json,
    transcript: Transcript,
    bytes: Vec<u8>,
}
impl Writer<'_> {
    fn origin(&self, round: Option<u64>, site: &str, query: bool, reverse: bool) -> Vec<u8> {
        let path = if round.is_some() {
            vec![json!(["repeat", self.entry, "rounds"])]
        } else {
            vec![]
        };
        let coordinates: Vec<_> = round.into_iter().map(|n| n.to_string()).collect();
        let event = if query {
            json!([
                "query",
                self.entry,
                site,
                "input_5",
                "random.bls12-381.fr/0",
                "draw",
                "V"
            ])
        } else {
            json!([
                "message",
                self.entry,
                site,
                site,
                if reverse { "V" } else { "P" },
                if reverse { "P" } else { "V" }
            ])
        };
        let template = tree(&json!([
            "zkc.native-origin-template/0",
            self.entry,
            path,
            [],
            event
        ]));
        assert!(self.descriptor[3].as_array().unwrap().contains(&json!([
            if query { "query" } else { "message" },
            hex(&template)
        ])));
        tree(&json!([
            "zkc.native-origin/0",
            self.entry,
            path,
            coordinates,
            event
        ]))
    }
    fn message(&mut self, round: Option<u64>, site: &str, bytes: &[u8]) {
        let origin = self.origin(round, site, false, false);
        self.transcript.absorb(b"origin", &origin);
        self.transcript.absorb(b"value", bytes);
        self.bytes
            .extend_from_slice(&(bytes.len() as u64).to_le_bytes());
        self.bytes.extend_from_slice(bytes);
    }
    fn challenge(&mut self, round: u64) -> Scalar {
        let origin = self.origin(Some(round), "draw", true, false);
        self.transcript.absorb(b"origin", &origin);
        let x = self.transcript.draw();
        let delivery = self.origin(Some(round), "challenge", false, true);
        self.transcript.absorb(b"origin", &delivery);
        self.transcript.absorb(b"value", &scalar_wire(x));
        x
    }
}
pub fn proof(
    envelope: &Json,
    input: &Json,
    n: u64,
    coefficients: &[Scalar],
    bases: &[GroupPoint],
    salt: Scalar,
) -> Vec<u8> {
    let root = transcript::root(envelope, input);
    let entry = envelope[2][1][1].as_str().unwrap();
    let mut w = Writer {
        entry,
        descriptor: &envelope[2],
        transcript: Transcript::new(envelope[2][1][5].as_str().unwrap(), &root),
        bytes: [b"ZKCPRF00".as_slice(), &Sha256::digest(&root)].concat(),
    };
    w.message(None, "salt", &scalar_wire(salt));
    let inv = salt.inverse().unwrap();
    let mut a: Vec<_> = coefficients.iter().map(|x| *x * inv).collect();
    let mut g = bases.to_vec();
    let mut claim;
    if entry == "fold" {
        claim = msm(&a, &g);
        for round in 0..n {
            assert_eq!(a.len(), g.len());
            assert_eq!(a.len() % 2, 0);
            let half = a.len() / 2;
            let l = msm(&a[..half], &g[half..]);
            let r = msm(&a[half..], &g[..half]);
            w.message(Some(round), "left", &group_wire(&l));
            w.message(Some(round), "right", &group_wire(&r));
            w.message(
                Some(round),
                "round_salt",
                &scalar_wire(Scalar::from(7 + round)),
            );
            let x = w.challenge(round);
            let y = x.inverse().unwrap();
            a = a[..half]
                .iter()
                .zip(&a[half..])
                .map(|(l, r)| *l * x + *r * y)
                .collect();
            g = g[..half]
                .iter()
                .zip(&g[half..])
                .map(|(l, r)| l.scale(y).add(&r.scale(x)))
                .collect();
            claim = claim.add(&l.scale(x * x)).add(&r.scale(y * y));
            assert_eq!(msm(&a, &g), claim);
            w.message(Some(round), "received", &groups(&g));
        }
    } else {
        assert_eq!(entry, "batch");
        let original = a;
        a = Vec::new();
        let original_g = g;
        g = Vec::new();
        let mut sum = GroupPoint::identity();
        claim = GroupPoint::identity();
        for round in 0..n {
            let i = round as usize;
            let term = original_g[i].scale(original[i]);
            w.message(Some(round), "contribution", &group_wire(&term));
            w.message(
                Some(round),
                "round_salt",
                &scalar_wire(Scalar::from(7 + round)),
            );
            let x = w.challenge(round);
            a.push(original[i] * x);
            g.push(original_g[i]);
            sum = sum.add(&term);
            claim = claim.add(&term.scale(x));
            assert_eq!(msm(&a, &g), claim);
            w.message(Some(round), "received", &groups(&g));
        }
        assert_eq!(sum, msm(&original[..n as usize], &original_g[..n as usize]));
    }
    w.message(None, "final", &vector(&a));
    assert_eq!(msm(&a, &g), claim);
    w.bytes
}

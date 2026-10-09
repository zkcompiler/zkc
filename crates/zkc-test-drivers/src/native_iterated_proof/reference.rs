//! Reconstruct source origins and protocol algebra independently of compiler and
//! backend origin, transcript, polynomial and proof-framing implementations.
#[path = "../support/native_transcript.rs"]
mod transcript;
use ark_serialize::CanonicalDeserialize;
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
pub use transcript::root;
use transcript::*;
use zkc_backends::{GroupPoint, Scalar};
use zkc_test_support::hex;

struct Oracle<'a> {
    descriptor: &'a Json,
    proof: &'a [u8],
    position: usize,
    transcript: Transcript,
}
impl Oracle<'_> {
    fn origin(
        &self,
        path: &[Json],
        coordinates: &[u64],
        protocol: &str,
        site: &str,
        query: bool,
        reverse: bool,
    ) -> Vec<u8> {
        let event = if query {
            json!([
                "query",
                protocol,
                site,
                "input_4",
                "random.bls12-381.fr/0",
                "draw",
                "V"
            ])
        } else {
            json!([
                "message",
                protocol,
                site,
                site,
                if reverse { "V" } else { "P" },
                if reverse { "P" } else { "V" }
            ])
        };
        let template = tree(&json!([
            "zkc.native-origin-template/0",
            "main",
            path,
            [],
            event
        ]));
        assert!(
            self.descriptor[3].as_array().unwrap().contains(&json!([
                if query { "query" } else { "message" },
                hex(&template)
            ])),
            "missing authored occurrence {protocol}/{site}"
        );
        tree(&json!([
            "zkc.native-origin/0",
            "main",
            path,
            coordinates.iter().map(u64::to_string).collect::<Vec<_>>(),
            event
        ]))
    }
    fn message(
        &mut self,
        path: &[Json],
        coordinates: &[u64],
        protocol: &str,
        site: &str,
    ) -> Vec<u8> {
        let origin = self.origin(path, coordinates, protocol, site, false, false);
        let length = u64::from_le_bytes(
            self.proof[self.position..self.position + 8]
                .try_into()
                .unwrap(),
        ) as usize;
        self.position += 8;
        let bytes = &self.proof[self.position..self.position + length];
        self.position += length;
        self.transcript.absorb(b"origin", &origin);
        self.transcript.absorb(b"value", bytes);
        bytes.to_vec()
    }
    fn challenge(
        &mut self,
        path: &[Json],
        coordinates: &[u64],
        protocol: &str,
        site: &str,
    ) -> Scalar {
        let origin = self.origin(path, coordinates, protocol, site, true, false);
        self.transcript.absorb(b"origin", &origin);
        let challenge = self.transcript.draw();
        let delivery = self.origin(path, coordinates, protocol, "challenge", false, true);
        self.transcript.absorb(b"origin", &delivery);
        self.transcript.absorb(b"value", &scalar_wire(challenge));
        challenge
    }
}
fn index(bytes: &[u8]) -> u64 {
    assert_eq!(&bytes[..6], b"ZKCV\x00\x1f");
    assert_eq!(bytes.len(), 14);
    u64::from_le_bytes(bytes[6..].try_into().unwrap())
}
fn fold(values: &[Scalar], challenge: Scalar) -> Vec<Scalar> {
    values[..values.len() / 2]
        .iter()
        .zip(&values[values.len() / 2..])
        .map(|(a, b)| *a + challenge * (*b - *a))
        .collect()
}
fn coefficients(a: &[Scalar], b: &[Scalar], cubic: bool) -> Vec<Scalar> {
    let mut sum = vec![Scalar::from(0); if cubic { 4 } else { 3 }];
    for i in 0..a.len() / 2 {
        let x = [a[i], a[i + a.len() / 2]];
        let y = [b[i], b[i + b.len() / 2]];
        let mut term = vec![Scalar::from(1)];
        for linear in if cubic {
            vec![
                [x[0], x[1] - x[0]],
                [x[0], x[1] - x[0]],
                [y[0], y[1] - y[0]],
            ]
        } else {
            vec![[x[0], x[1] - x[0]], [y[0], y[1] - y[0]]]
        } {
            let mut next = vec![Scalar::from(0); term.len() + 1];
            for (i, v) in term.iter().enumerate() {
                next[i] += *v * linear[0];
                next[i + 1] += *v * linear[1];
            }
            term = next;
        }
        for (s, t) in sum.iter_mut().zip(term) {
            *s += t;
        }
    }
    sum
}
pub fn verify(envelope: &Json, input: &Json, proof: &[u8], family: &str, n: u64) {
    let root = root(envelope, input);
    assert_eq!(&proof[..8], b"ZKCPRF00");
    assert_eq!(&proof[8..40], &Sha256::digest(&root)[..]);
    assert_eq!(envelope[3], hex(&Sha256::digest(tree(&envelope[2]))));
    let mut oracle = Oracle {
        descriptor: &envelope[2],
        proof,
        position: 40,
        transcript: Transcript::new(envelope[2][1][5].as_str().unwrap(), &root),
    };
    if family == "nested" {
        let outer = vec![json!(["repeat", "main", "outer"])];
        for i in 0..n {
            assert_eq!(
                index(&oracle.message(&outer, &[i], "main", "inner_count")),
                i
            );
            for j in 0..i {
                for call in ["first", "second"] {
                    let mut path = outer.clone();
                    path.extend([
                        json!(["apply", "main", "segment"]),
                        json!(["repeat", "segment", "inner"]),
                        json!(["apply", "segment", call]),
                    ]);
                    let commitment = group(&oracle.message(&path, &[i, j], "step", "commitment"));
                    let challenge = oracle.challenge(&path, &[i, j], "step", "draw_challenge");
                    let response = scalar(&oracle.message(&path, &[i, j], "step", "response"));
                    let base = GroupPoint::generator();
                    assert_eq!(commitment, base.scale(Scalar::from(7)));
                    assert_eq!(response, Scalar::from(7) + challenge * Scalar::from(3));
                    assert_eq!(
                        base.scale(response),
                        commitment.add(&base.scale(Scalar::from(3) * challenge))
                    );
                }
            }
        }
    } else {
        assert_eq!(index(&oracle.message(&[], &[], "main", "arity")), n);
        let (mut a, mut b) = super::tables(n as usize);
        let original = (a.clone(), b.clone());
        let cubic = family == "cubic";
        let mut claim: Scalar = a
            .iter()
            .zip(&b)
            .map(|(x, y)| if cubic { *x * *x * *y } else { *x * *y })
            .sum();
        let mut point = Vec::new();
        for i in 0..n {
            let path = [json!(["repeat", "main", "rounds"])];
            let bytes = oracle.message(&path, &[i], "main", "round_message");
            assert_eq!(&bytes[..6], b"ZKCV\x00\x40");
            let expected = coefficients(&a, &b, cubic);
            assert_eq!(bytes.len(), 6 + 32 * expected.len());
            let actual: Vec<_> = bytes[6..]
                .as_chunks::<32>()
                .0
                .iter()
                .map(|b| Scalar::deserialize_compressed(b.as_slice()).unwrap())
                .collect();
            assert_eq!(actual, expected);
            assert_eq!(actual[0] + actual.iter().copied().sum::<Scalar>(), claim);
            let r = oracle.challenge(&path, &[i], "main", "draw");
            claim = actual.iter().rev().fold(Scalar::from(0), |v, c| v * r + c);
            a = fold(&a, r);
            b = fold(&b, r);
            point.push(r);
        }
        let evaluate = |table: Vec<Scalar>| point.iter().fold(table, |v, r| fold(&v, *r))[0];
        let x = evaluate(original.0);
        let y = evaluate(original.1);
        assert_eq!(claim, if cubic { x * x * y } else { x * y });
    }
    assert_eq!(oracle.position, proof.len());
}

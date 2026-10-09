//! Reconstruct source origins and protocol algebra independently of compiler and
//! backend origin, transcript, polynomial and proof-framing implementations.
#[allow(dead_code)]
#[path = "../support/native_transcript.rs"]
mod transcript;
use ark_bls12_381::{Bls12_381, G1Affine, G2Affine};
use ark_poly_commit::multilinear_pc::{MultilinearPC, data_structures as pcs};
use ark_serialize::CanonicalDeserialize;
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
pub use transcript::root;
use transcript::*;
use zkc_backends::Scalar;
use zkc_tools::proof::hex;

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
// Decode only the fixed canonical point payloads into an independent upstream
// verifier; the native codec and wrapper check are not this oracle.
fn opening(bytes: &[u8], root: &[u8], proof: &[u8], point: &[Scalar], value: Scalar) {
    assert_eq!(&bytes[..9], b"ZKCAR000\x01");
    let n = usize::try_from(u64::from_le_bytes(bytes[9..17].try_into().unwrap())).unwrap();
    assert_eq!(point.len(), n);
    assert_eq!(bytes.len(), 81 + 48 + 96 + 48 * n);
    let mut data = &bytes[81..];
    let g = G1Affine::deserialize_compressed(&mut data).unwrap();
    let h = G2Affine::deserialize_compressed(&mut data).unwrap();
    let masks = (0..n)
        .map(|_| G1Affine::deserialize_compressed(&mut data).unwrap())
        .collect();
    assert!(data.is_empty());
    let vk = pcs::VerifierKey::<Bls12_381> {
        nv: n,
        g,
        h,
        g_mask_random: masks,
    };
    assert_eq!(root.len(), 135);
    assert_eq!(proof.len(), 87 + 96 * n);
    assert_eq!(&root[..6], b"ZKCV\x00\x06");
    assert_eq!(&proof[..6], b"ZKCV\x00\x07");
    let commitment = pcs::Commitment::<Bls12_381> {
        nv: n,
        g_product: G1Affine::deserialize_compressed(&root[87..]).unwrap(),
    };
    let mut data = &proof[87..];
    let quotients = (0..n)
        .map(|_| G2Affine::deserialize_compressed(&mut data).unwrap())
        .collect();
    assert!(data.is_empty());
    let proof = pcs::Proof::<Bls12_381> { proofs: quotients };
    assert!(MultilinearPC::check(&vk, &commitment, point, value, &proof));
    let mut wrong = point.to_vec();
    wrong[0] += Scalar::from(1);
    assert!(!MultilinearPC::check(
        &vk,
        &commitment,
        &wrong,
        value,
        &proof
    ));
}
fn unhex(v: &Json) -> Vec<u8> {
    let s = v.as_str().unwrap();
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}
pub fn verify(envelope: &Json, input: &Json, proof: &[u8], family: &str, n: usize) {
    let root = root(envelope, input);
    assert_eq!(&proof[..8], b"ZKCPRF00");
    assert_eq!(&proof[8..40], &Sha256::digest(&root)[..]);
    let public = |port: &str| {
        unhex(
            &input[1]
                .as_array()
                .unwrap()
                .iter()
                .find(|p| p[1] == port)
                .unwrap()[2],
        )
    };
    let mut oracle = Oracle {
        descriptor: &envelope[2],
        proof,
        position: 40,
        transcript: Transcript::new(envelope[2][1][5].as_str().unwrap(), &root),
    };
    // Authored has no observations/challenges; direct parse of both value/proof pairs.
    if matches!(family, "authored" | "structured") {
        for _ in 0..2 {
            let mut read = || {
                let len = u64::from_le_bytes(
                    proof[oracle.position..oracle.position + 8]
                        .try_into()
                        .unwrap(),
                ) as usize;
                oracle.position += 8;
                let bytes = &proof[oracle.position..oracle.position + len];
                oracle.position += len;
                bytes
            };
            let record = read();
            let (value, opening_proof) = if family == "structured" {
                assert_eq!(&record[..10], b"ZKCV\x00\x41\x01\x00\x00\x00");
                let value_len = u32::from_le_bytes(record[10..14].try_into().unwrap()) as usize;
                let end = 14 + value_len;
                let proof_len =
                    u32::from_le_bytes(record[end..end + 4].try_into().unwrap()) as usize;
                assert_eq!(end + 4 + proof_len, record.len());
                (scalar(&record[14..end]), &record[end + 4..])
            } else {
                (scalar(record), read())
            };
            opening(
                &public("2"),
                &public("3"),
                opening_proof,
                &[scalar(&public("4"))],
                value,
            );
            assert_eq!(value, scalar(&public("5")));
        }
    } else {
        let root_a = oracle.message(&[], &[], "main", "root_T");
        let root_b = oracle.message(&[], &[], "main", "root_U");
        assert_eq!(root_a, public("7"));
        assert_eq!(root_b, public("8"));
        assert_eq!(index(&oracle.message(&[], &[], "main", "arity")), n as u64);
        let (mut a, mut b) = super::tables(n);
        let original = (a.clone(), b.clone());
        let cubic = family == "cubic";
        let mut claim = scalar(&public("3"));
        let mut point = Vec::new();
        for i in 0..n {
            let path = [json!(["repeat", "main", "rounds"])];
            let bytes = oracle.message(&path, &[i as u64], "main", "round_message");
            assert_eq!(&bytes[..6], b"ZKCV\x00\x40");
            let actual: Vec<_> = bytes[6..]
                .as_chunks::<32>()
                .0
                .iter()
                .map(|b| Scalar::deserialize_compressed(b.as_slice()).unwrap())
                .collect();
            assert_eq!(actual, coefficients(&a, &b, cubic));
            assert_eq!(actual[0] + actual.iter().copied().sum::<Scalar>(), claim);
            let challenge = oracle.challenge(&path, &[i as u64], "main", "draw");
            claim = actual
                .iter()
                .rev()
                .fold(Scalar::from(0), |v, c| v * challenge + c);
            a = fold(&a, challenge);
            b = fold(&b, challenge);
            point.push(challenge);
        }
        let mut values = Vec::new();
        for (site, commitment, original) in [
            ("open_T", root_a, original.0),
            ("open_U", root_b, original.1),
        ] {
            let path = [json!(["apply", "main", site])];
            let value = scalar(&oracle.message(&path, &[], "opening", "value"));
            let proof = oracle.message(&path, &[], "opening", "proof");
            assert_eq!(value, point.iter().fold(original, |v, r| fold(&v, *r))[0]);
            opening(&public("6"), &commitment, &proof, &point, value);
            values.push(value);
        }
        assert_eq!(
            claim,
            if cubic {
                values[0] * values[0] * values[1]
            } else {
                values[0] * values[1]
            }
        );
    }
    assert_eq!(oracle.position, proof.len());
}

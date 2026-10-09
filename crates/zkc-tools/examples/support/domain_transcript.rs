//! Independent flat structured-proof replay for the non-BLS Merlin suites.
//! Root/origin trees, proof framing and scalar sampling do not call host/backend
//! constructors. The expected event names come from the authored fixtures.
#[allow(dead_code)]
#[path = "native_transcript.rs"]
mod encoding;
use curve25519_dalek::scalar::Scalar;
use num_bigint::BigUint;
use p3_field::{BasedVectorSpace, PrimeCharacteristicRing, PrimeField32};
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use zkc_backends::{KoalaBear, KoalaBearExt8};

pub struct Replay<'a> {
    envelope: &'a Json,
    proof: &'a [u8],
    position: usize,
    event: usize,
    rejections: usize,
    transcript: merlin::Transcript,
}
impl<'a> Replay<'a> {
    pub fn new(envelope: &'a Json, input: &Json, proof: &'a [u8], suite: &str) -> Self {
        assert_eq!(envelope[2][1][5], suite);
        let root = encoding::root(envelope, input);
        assert_eq!(&proof[..8], b"ZKCPRF01");
        assert_eq!(&proof[8..40], &Sha256::digest(&root)[..]);
        let mut transcript = merlin::Transcript::new(b"zkc.artifact");
        transcript.append_message(b"binding", &root);
        Self {
            envelope,
            proof,
            position: 40,
            event: 0,
            rejections: 0,
            transcript,
        }
    }
    fn origin(&mut self, data: Json) {
        let template = encoding::tree(&json!(["zkc.native-origin-template", "main", [], [], data]));
        let hex: String = template.iter().map(|b| format!("{b:02x}")).collect();
        assert_eq!(self.envelope[2][3][self.event], json!([data[0], hex]));
        self.event += 1;
        self.transcript.append_message(
            b"origin",
            &encoding::tree(&json!(["zkc.native-origin", "main", [], [], data])),
        );
    }
    pub fn observe(&mut self, site: &str, sender: &str, receiver: &str, wire: &[u8]) {
        self.origin(json!(["message", "main", site, site, sender, receiver]));
        self.transcript.append_message(b"value", wire);
    }
    pub fn message(&mut self, site: &str, sender: &str, receiver: &str) -> &'a [u8] {
        let at = self.position;
        let size = u64::from_le_bytes(self.proof[at..at + 8].try_into().unwrap()) as usize;
        self.position += 8 + size;
        let wire = &self.proof[at + 8..self.position];
        self.observe(site, sender, receiver, wire);
        wire
    }
    pub fn query(&mut self, site: &str, port: usize, contract: &str, owner: &str) {
        self.origin(json!([
            "query",
            "main",
            site,
            format!("input_{port}"),
            contract,
            "draw",
            owner
        ]));
    }
    pub fn ristretto(&mut self) -> Scalar {
        let mut bytes = [0; 64];
        self.transcript.challenge_bytes(b"challenge", &mut bytes);
        // Integer reduction independently checks the backend's wide LE mapping.
        let order = (BigUint::from(1u8) << 252usize)
            + BigUint::parse_bytes(b"27742317777372353535851937790883648493", 10).unwrap();
        let reduced = (BigUint::from_bytes_le(&bytes) % order).to_bytes_le();
        let mut canonical = [0; 32];
        canonical[..reduced.len()].copy_from_slice(&reduced);
        Option::<Scalar>::from(Scalar::from_canonical_bytes(canonical)).unwrap()
    }
    pub fn extension(&mut self) -> KoalaBearExt8 {
        let mut coordinates = Vec::new();
        for _ in 0..16 {
            let mut bytes = [0; 64];
            self.transcript.challenge_bytes(b"challenge", &mut bytes);
            for word in bytes.as_chunks::<4>().0 {
                let n = u32::from_le_bytes(*word) % (1 << 31);
                if n >= 2_130_706_433 {
                    self.rejections += 1;
                } else {
                    coordinates.push(KoalaBear::from_u32(n));
                    if coordinates.len() == 8 {
                        return KoalaBearExt8::from(
                            <[KoalaBear; 8]>::try_from(coordinates).unwrap(),
                        );
                    }
                }
            }
        }
        panic!("independent challenge sampler exhausted");
    }
    pub fn finish(self) -> usize {
        assert_eq!(self.position, self.proof.len());
        assert_eq!(self.event, self.envelope[2][3].as_array().unwrap().len());
        self.rejections
    }
}
pub fn extension_wire(value: KoalaBearExt8) -> Vec<u8> {
    let mut wire = b"ZKCV\x01\x1a".to_vec();
    for x in <KoalaBearExt8 as BasedVectorSpace<KoalaBear>>::as_basis_coefficients_slice(&value) {
        wire.extend_from_slice(&x.as_canonical_u32().to_le_bytes());
    }
    wire
}
pub fn extension_value(wire: &[u8]) -> KoalaBearExt8 {
    assert_eq!(wire.len(), 38);
    assert_eq!(&wire[..6], b"ZKCV\x01\x1a");
    let coordinates: Vec<_> = wire[6..]
        .as_chunks::<4>()
        .0
        .iter()
        .map(|word| {
            let n = u32::from_le_bytes(*word);
            assert!(n < 2_130_706_433);
            KoalaBear::from_u32(n)
        })
        .collect();
    KoalaBearExt8::from(<[KoalaBear; 8]>::try_from(coordinates).unwrap())
}

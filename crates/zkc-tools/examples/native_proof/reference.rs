//! Independent flat proof oracle using shared upstream transcript primitives.
#[path = "../support/native_transcript.rs"]
mod transcript;
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
pub use transcript::*;
use zkc_backends::{GroupPoint, Scalar};
use zkc_tools::artifact::hex;
pub fn verify(case: &Json, envelope: &Json, input: &Json, proof: &[u8], nonce: Option<Scalar>) {
    let root = root(envelope, input);
    assert_eq!(&proof[..8], b"ZKCPRF01");
    assert_eq!(&proof[8..40], &Sha256::digest(&root)[..]);
    assert_eq!(envelope[3], hex(&Sha256::digest(tree(&envelope[2]))));
    let policy = &envelope[2][1];
    let entry = policy[1].as_str().unwrap();
    let p = policy[2].as_str().unwrap();
    let v = policy[3].as_str().unwrap();
    let suite = policy[5].as_str().unwrap();
    let name = case["name"].as_str().unwrap();
    let protocol = case["origin_protocol"].as_str().unwrap_or(entry);
    let path = case
        .get("origin_path")
        .cloned()
        .unwrap_or_else(|| json!([]));
    let dleq = case["family"] == "dleq";
    let rounds = case["rounds"].as_u64().unwrap();
    let mut transcript = (!suite.is_empty()).then(|| Transcript::new(suite, &root));
    let mut pos = 40;
    let mut event_index = 0;
    let mut check_origin = |kind: &str, site: &str, sender: &str, receiver: &str| {
        let event = if kind == "query" {
            json!([
                "query",
                protocol,
                site,
                format!("input_{}", case["challenge_port"].as_u64().unwrap_or(4)),
                "random.bls12-381.fr/1",
                "draw",
                v
            ])
        } else {
            json!(["message", protocol, site, site, sender, receiver])
        };
        let origin = tree(&json!(["zkc.native-origin/1", entry, path, [], event]));
        assert_eq!(envelope[2][3][event_index], json!([kind, hex(&origin)]));
        event_index += 1;
        origin
    };
    for round in 0..rounds {
        let suffix = if round == 0 { "" } else { "_second" };
        let mut commitments = Vec::new();
        for site in if dleq {
            vec!["commitment", "second_commitment"]
        } else {
            vec!["commitment"]
        } {
            let site = if name.starts_with("renamed_") {
                "_transcript_0".into()
            } else {
                format!("{site}{suffix}")
            };
            let origin = check_origin("message", &site, p, v);
            let length = u64::from_le_bytes(proof[pos..pos + 8].try_into().unwrap()) as usize;
            pos += 8;
            let payload = &proof[pos..pos + length];
            pos += length;
            commitments.push(group(payload));
            if let Some(t) = &mut transcript {
                t.absorb(b"origin", &origin);
                t.absorb(b"value", payload);
            }
        }
        let c = if let Some(t) = &mut transcript {
            t.absorb(
                b"origin",
                &check_origin("query", &format!("draw_challenge{suffix}"), v, p),
            );
            let c = t.draw();
            t.absorb(
                b"origin",
                &check_origin("message", &format!("challenge{suffix}"), v, p),
            );
            t.absorb(b"value", &scalar_wire(c));
            c
        } else {
            Scalar::from(11)
        };
        let origin = check_origin("message", &format!("response{suffix}"), p, v);
        let length = u64::from_le_bytes(proof[pos..pos + 8].try_into().unwrap()) as usize;
        pos += 8;
        let payload = &proof[pos..pos + length];
        pos += length;
        let z = scalar(payload);
        if let Some(t) = &mut transcript {
            t.absorb(b"origin", &origin);
            t.absorb(b"value", payload);
        }
        if case["bool_message"] == true {
            let origin = check_origin("message", "flag", p, v);
            let length = u64::from_le_bytes(proof[pos..pos + 8].try_into().unwrap()) as usize;
            pos += 8;
            let payload = &proof[pos..pos + length];
            pos += length;
            assert_eq!(payload, b"ZKCV\x01\x05\x01");
            let t = transcript.as_mut().unwrap();
            t.absorb(b"origin", &origin);
            t.absorb(b"value", payload);
        }
        for (i, commitment) in commitments.into_iter().enumerate() {
            let base = GroupPoint::generator().scale(Scalar::from(if i == 0 { 1 } else { 7 }));
            let public = base.scale(Scalar::from(3));
            if let Some(k) = nonce {
                assert_eq!(commitment, base.scale(k));
                assert_eq!(z, k + c * Scalar::from(3));
            }
            assert_eq!(
                base.scale(z),
                commitment.add(&public.scale(c)),
                "independent group equation {name}"
            );
        }
    }
    assert_eq!(pos, proof.len());
    assert_eq!(event_index, envelope[2][3].as_array().unwrap().len());
}

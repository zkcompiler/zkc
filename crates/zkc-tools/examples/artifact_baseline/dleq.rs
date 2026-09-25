//! Exact two DLEQArgument calls with original formal roles and shared state.
use crate::{Result, codec::*, ensure, input::Input, transcript::*};
use serde_json::json;
use zkc_arkworks::{Scalar, scalar_from_wide_be};
pub fn execute(io: &Input, s: &mut Session<'_>) -> Result<()> {
    let validator = s.is_validator();
    let public = io.groups.ok_or("missing-group-inputs")?;
    let bases = [public[0], public[1]];
    let images = [public[2], public[3]];
    if !validator {
        ensure(
            io.x == Some(Scalar::from(19u64)),
            "development-public-witness-required",
        )?;
    }
    let mut results = Vec::new();
    for (site, nonce) in [("first", 0xa5u8), ("second", 0x5au8)] {
        let path = json!([["call", site, "argument"]]);
        // Deliberately PUBLIC test nonces. This executable has no production
        // prove mode; native host issuance uses OS entropy instead.
        // Full-width residues avoid an artificially cheap small-scalar MSM.
        let nonce = scalar_from_wide_be(&[nonce; 64]);
        // DLEQCommit computes BOTH group points before either source message.
        let authored = if validator {
            None
        } else {
            Some([bases[0].scale(nonce), bases[1].scale(nonce)])
        };
        let mut commitments = Vec::new();
        for i in 0..2 {
            let (b, a) = if validator {
                let b = s.receive()?;
                let a = point(&b)?;
                (b, a)
            } else {
                let a = authored.as_ref().ok_or("missing-commitment")?[i];
                let b = group(a)?;
                s.send(&b)?;
                (b, a)
            };
            s.observe(
                message(
                    "argument",
                    &path,
                    "DLEQArgument",
                    if i == 0 {
                        "commitment_0"
                    } else {
                        "commitment_1"
                    },
                    "g1",
                    "P",
                    "V",
                ),
                &b,
            )?;
            commitments.push(a);
        }
        let c = s.draw(challenge(
            "argument",
            &path,
            "DLEQArgument",
            "challenge",
            "DLEQDraw",
        ))?;
        s.observe(
            message(
                "argument",
                &path,
                "DLEQArgument",
                "challenge_message",
                "fr",
                "V",
                "P",
            ),
            &scalar(c)?,
        )?;
        let (b, z) = if validator {
            let b = s.receive()?;
            let z = field(&b)?;
            (b, z)
        } else {
            let z = nonce + c * io.x.ok_or("missing-x")?;
            let b = scalar(z)?;
            s.send(&b)?;
            (b, z)
        };
        s.observe(
            message(
                "argument",
                &path,
                "DLEQArgument",
                "response_message",
                "fr",
                "P",
                "V",
            ),
            &b,
        )?;
        if validator {
            let mut checks = [false; 2];
            for i in 0..2 {
                // Preserve ordered scale / scale / add / equal / require.
                let left = bases[i].scale(z);
                let cx = images[i].scale(c);
                let right = commitments[i].add(&cx);
                checks[i] = left == right;
                s.guard(
                    "argument",
                    &path,
                    [
                        "DLEQArgument",
                        "equations",
                        "DLEQCheck",
                        if i == 0 { "require_0" } else { "require_1" },
                    ],
                    checks[i],
                )?;
            }
            results.push(checks[0] && checks[1]);
        }
    }
    if validator {
        let accepted = results[0] && results[1];
        s.events
            .push(json!(["result", "DLEQBoth", "both", accepted]));
        ensure(accepted, "source-false-result")?;
    }
    s.finish()
}

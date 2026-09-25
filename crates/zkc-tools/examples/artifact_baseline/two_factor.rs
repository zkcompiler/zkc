//! Exact pinned CommittedTwoFactorArgument: commits, guarded roots, compact
//! sumcheck loop, sequential opening guards, terminal multiplication equality.
use crate::{Result, codec::*, ensure, input::Input, transcript::*};
use serde_json::json;
pub fn execute(io: &Input, n: usize, s: &mut Session<'_>) -> Result<()> {
    let validator = s.is_validator();
    let vk = io.vk.as_ref().ok_or("missing-vk")?;
    let states = if validator {
        None
    } else {
        let pk = io.pk.as_ref().ok_or("missing-pk")?;
        Some((
            pk.commit(io.f.as_ref().ok_or("missing-f")?)?,
            pk.commit(io.g.as_ref().ok_or("missing-g")?)?,
        ))
    };
    let mut roots = Vec::new();
    for (i, site) in ["root_f", "root_g"].iter().enumerate() {
        let b = if let Some((f, g)) = &states {
            let t = if i == 0 { f } else { g };
            let b = wire(6, &t.commitment().to_bytes(&BOUNDS)?);
            s.send(&b)?;
            b
        } else {
            s.receive()?
        };
        // Decode before observation, as native receives do.
        let root = if validator {
            Some(vk.decode_commitment(body(&b, 6)?, &BOUNDS)?)
        } else {
            None
        };
        s.observe(
            message(
                "interactive",
                &json!([]),
                "CommittedTwoFactorArgument",
                site,
                "commitment",
                "P",
                "V",
            ),
            &b,
        )?;
        roots.push((root, b));
    }
    if validator {
        for (i, site, label) in [
            (0, "require_f", "expected_f"),
            (1, "require_g", "expected_g"),
        ] {
            s.guard(
                "interactive",
                &json!([]),
                [
                    "CommittedTwoFactorArgument",
                    "check_expected_roots",
                    "CheckExpectedRoots",
                    site,
                ],
                roots[i].1 == io.public(label)?,
            )?;
        }
    }
    let mut f = io.f.clone();
    let mut g = io.g.clone();
    let mut claim = io.claim.ok_or("missing-claim")?;
    let mut point = Vec::new();
    for i in 0..n {
        let path = json!([
            ["call", "sumcheck_call", "sumcheck"],
            ["loop", "rounds", i.to_string()]
        ]);
        let (b, q) = if validator {
            let b = s.receive()?;
            let q = quadratic(&b)?;
            (b, q)
        } else {
            let q = f
                .as_ref()
                .ok_or("missing-f")?
                .round_product(g.as_ref().ok_or("missing-g")?)?;
            let b = round(q)?;
            s.send(&b)?;
            (b, q)
        };
        s.observe(
            message(
                "sumcheck",
                &path,
                "ProductSumcheck",
                "round_message",
                "quadratic",
                "P",
                "V",
            ),
            &b,
        )?;
        // P derives the challenge but does not execute erased verifier guards.
        if validator {
            s.guard(
                "sumcheck",
                &path,
                [
                    "ProductSumcheck",
                    "check_and_draw",
                    "CheckRoundAndDraw",
                    "require",
                ],
                q[0] + q[0] + q[1] + q[2] == claim,
            )?;
        }
        let r = s.draw(challenge(
            "sumcheck",
            &path,
            "ProductSumcheck",
            "check_and_draw",
            "CheckRoundAndDraw",
        ))?;
        if validator {
            claim = q[0] + r * (q[1] + r * q[2]);
        }
        s.observe(
            message(
                "sumcheck",
                &path,
                "ProductSumcheck",
                "challenge_message",
                "challenge",
                "V",
                "P",
            ),
            &scalar(r)?,
        )?;
        if !validator {
            f = Some(f.as_ref().ok_or("missing-f")?.restrict_first(r)?);
            g = Some(g.as_ref().ok_or("missing-g")?.restrict_first(r)?);
        }
        point.push(r);
    }
    let mut evaluations = Vec::new();
    for (i, site) in ["open_f", "open_g"].iter().enumerate() {
        let path = json!([["call", site, "opening"]]);
        let opening = if let Some((f, g)) = &states {
            Some((if i == 0 { f } else { g }).open(&point)?)
        } else {
            None
        };
        let value_bytes = if let Some((value, _)) = &opening {
            let b = scalar(*value)?;
            s.send(&b)?;
            b
        } else {
            s.receive()?
        };
        let value = if let Some((value, _)) = &opening {
            *value
        } else {
            field(&value_bytes)?
        };
        s.observe(
            message(
                "opening",
                &path,
                "FactorOpening",
                "evaluation_message",
                "evaluation",
                "P",
                "V",
            ),
            &value_bytes,
        )?;
        let proof_bytes = if let Some((_, proof)) = &opening {
            let b = wire(7, &proof.to_bytes(&BOUNDS)?);
            s.send(&b)?;
            b
        } else {
            s.receive()?
        };
        let proof = if validator {
            Some(vk.decode_proof(body(&proof_bytes, 7)?, &BOUNDS)?)
        } else {
            None
        };
        s.observe(
            message(
                "opening",
                &path,
                "FactorOpening",
                "proof_message",
                "opening",
                "P",
                "V",
            ),
            &proof_bytes,
        )?;
        if validator {
            s.guard(
                "opening",
                &path,
                ["FactorOpening", "check_opening", "CheckOpening", "require"],
                vk.check(
                    roots[i].0.as_ref().ok_or("missing-root")?,
                    &point,
                    value,
                    proof.as_ref().ok_or("missing-opening")?,
                )?,
            )?;
        }
        evaluations.push(value);
    }
    if validator {
        let accepted = evaluations[0] * evaluations[1] == claim;
        s.events.push(json!([
            "result",
            "CheckTerminal",
            "product",
            "equal",
            accepted
        ]));
        ensure(accepted, "source-false-result")?;
    }
    s.finish()
}

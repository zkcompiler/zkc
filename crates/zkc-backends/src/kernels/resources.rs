//! Resource transitions live at their logical operation sites. Vector storage
//! is preflighted; scalar draws retain consume-first output validation.
use crate::kernels::arithmetic::{natural, reserve};
use crate::{Policy, Result, Value, exhausted, refused, resource::Resources, value::size};
use zkc_runtime::interactive::Invocation;
pub(crate) fn apply(
    name: &str,
    args: &[Value],
    i: &Invocation<'_>,
    p: &Policy,
    r: &mut Resources,
) -> Option<Result<Vec<Value>>> {
    if !matches!(
        name,
        "random.index"
            | "transcript.draw_index"
            | "random.draw"
            | "random.vector"
            | "curve.commit"
            | "curve.response"
            | "transcript.challenge"
    ) && !name.starts_with("transcript.observe.")
    {
        return None;
    }
    Some((|| {
        use Value::*;
        match (name, args) {
            ("random.index", [Rng(t), Index(bound)]) => {
                p.output(1024, i.max_output_bytes)?;
                let (v, t) = r.draw_index(i.frame, t, *bound)?;
                Ok(vec![v, Rng(t)])
            }
            ("transcript.draw_index", [Transcript(t), Index(bound)]) => {
                p.output(1024, i.max_output_bytes)?;
                let origin = zkc_runtime::logical::challenge_origin(i.frame.origin(), i.attributes)
                    .map_err(|_| refused("transcript-origin"))?;
                let (v, t) = r.transcript_index(i.frame, t, &origin, *bound)?;
                Ok(vec![v, Transcript(t)])
            }
            ("random.draw", [Rng(t)]) => {
                let (v, t) = r.draw_value(i.frame, t)?;
                Ok(vec![v, Rng(t)])
            }
            ("random.vector", [Rng(t)]) => {
                let n = natural(i.attributes, 0)?;
                p.vector(n)?;
                p.output(
                    size(n, 32)?
                        .checked_add(512)
                        .ok_or_else(|| exhausted("size-overflow"))?,
                    i.max_output_bytes,
                )?;
                let (value, next) = r.draw_vector(i.frame, t, n)?;
                Ok(vec![value, Rng(next)])
            }
            ("transcript.challenge", [Transcript(t)]) => {
                p.output(1024, i.max_output_bytes)?;
                let origin = zkc_runtime::logical::challenge_origin(i.frame.origin(), i.attributes)
                    .map_err(|_| refused("transcript-origin"))?;
                let (v, t) = r.transcript_challenge_value(i.frame, t, &origin)?;
                Ok(vec![v, Transcript(t)])
            }
            (name, [Transcript(t), v]) if name.starts_with("transcript.observe.") => {
                p.output(512, i.max_output_bytes)?;
                let origin = zkc_runtime::logical::message_origin(i.frame.origin(), i.attributes)
                    .map_err(|_| refused("transcript-origin"))?;
                let bytes = crate::codec::encode(v, p)?;
                Ok(vec![Transcript(
                    r.transcript_observe(i.frame, t, &origin, &bytes)?,
                )])
            }
            ("curve.commit", [Groups(b), Nonce(t)]) => {
                p.groups(b.len())?;
                p.output(
                    size(b.len(), 128)?
                        .checked_add(512)
                        .ok_or_else(|| exhausted("size-overflow"))?,
                    i.max_output_bytes,
                )?;
                let mut out = reserve(b.len())?;
                let (k, t) = r.commit_nonce(i.frame, t)?;
                out.extend(b.iter().map(|b| b.scale(k)));
                Ok(vec![Groups(out.into()), Nonce(t)])
            }
            ("curve.commit", [RistrettoGroups(b), Nonce(t)]) => {
                p.ristretto_groups(b.len())?;
                p.output(
                    size(b.len(), std::mem::size_of::<crate::RistrettoPoint>())?
                        .checked_add(512)
                        .ok_or_else(|| exhausted("size-overflow"))?,
                    i.max_output_bytes,
                )?;
                let mut out = reserve(b.len())?;
                let (k, t) = r.commit_ristretto_nonce(i.frame, t)?;
                out.extend(b.iter().map(|b| b * k));
                Ok(vec![RistrettoGroups(out.into()), Nonce(t)])
            }
            ("curve.response", [Field(x), Field(c), Nonce(t)]) => {
                p.output(512, i.max_output_bytes)?;
                Ok(vec![Field(r.respond(i.frame, t, *x, *c)?)])
            }
            ("curve.response", [RistrettoField(x), RistrettoField(c), Nonce(t)]) => {
                p.output(512, i.max_output_bytes)?;
                Ok(vec![RistrettoField(
                    r.respond_ristretto(i.frame, t, *x, *c)?,
                )])
            }
            _ => Err(refused("kernel-operands")),
        }
    })())
}

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
    key: &crate::SetupRegistry,
) -> Result<Vec<Value>> {
    if !matches!(
        name,
        "random.index"
            | "random.draw"
            | "random.vector"
            | "curve.commit"
            | "curve.response"
            | "transcript.native.indexed.challenge"
            | "transcript.native.indexed.observe.data"
    ) {
        return Err(refused("kernel-operands"));
    }
    use Value::*;
    match (name, args) {
        ("random.index", [Rng(t), Index(bound)]) => {
            p.output(1024, i.max_output_bytes)?;
            let (v, t) = r.draw_index(i.frame, t, *bound)?;
            Ok(vec![v, Rng(t)])
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
        ("transcript.native.indexed.challenge", [Transcript(t), Indices(indices)]) => {
            p.output(1024, i.max_output_bytes)?;
            let origin =
                zkc_runtime::logical::indexed_native_origin(i.attributes, "query", indices)
                    .map_err(|_| refused("transcript-origin"))?;
            let (v, t) = r.transcript_challenge_value(i.frame, t, &origin)?;
            Ok(vec![v, Transcript(t)])
        }
        ("transcript.native.indexed.observe.data", [Transcript(t), v, Indices(indices)]) => {
            p.output(512, i.max_output_bytes)?;
            let origin =
                zkc_runtime::logical::indexed_native_origin(i.attributes, "message", indices)
                    .map_err(|_| refused("transcript-origin"))?;
            let bytes = crate::codec::native::encode(v, p, key).map_err(|e| match e {
                crate::NativeWireError::Limit => exhausted("native-wire-limit"),
                crate::NativeWireError::Backend(e) => e,
                crate::NativeWireError::Invalid(_) => refused("native-wire-value"),
            })?;
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
}

/// Independent native port facts, also used for exact implementation assembly.
pub(crate) const CONTRACTS: &[crate::bindings::Contract] = {
    use crate::bindings::{curve, random, transcript};
    use zkc_runtime::interactive::{AttributeRule, Type::*};
    &[
        transcript::observation(
            "transcript.native.indexed.observe.data",
            &[],
            &[],
            AttributeRule::NativeMessageTemplate,
        ),
        transcript::challenge(
            "transcript.native.indexed.challenge",
            &[Transcript, Indices],
            &[Field, Transcript],
            AttributeRule::NativeChallengeTemplate,
        ),
        curve::operation(
            "curve.commit",
            &[Groups, Nonce],
            &[Groups, Nonce],
            AttributeRule::None,
        ),
        curve::operation(
            "curve.response",
            &[Field, Field, Nonce],
            &[Field],
            AttributeRule::None,
        ),
        random::operation(
            "random.index",
            &[Rng, Index],
            &[Index, Rng],
            AttributeRule::None,
        ),
        random::operation("random.draw", &[Rng], &[Field, Rng], AttributeRule::None),
        random::operation(
            "random.vector",
            &[Rng],
            &[Vector, Rng],
            AttributeRule::NaturalIndex,
        ),
    ]
};

//! Independently installed primitive port shapes. Nominal bindings and provider
//! implementations are resolved in `bindings`; no closed source profiles exist.
use zkc_runtime::interactive::{AttributeRule, Type};

pub(crate) type Contract = (
    &'static str,
    &'static [Type],
    &'static [Type],
    AttributeRule,
);
pub(crate) const CONTRACTS: &[Contract] = {
    use AttributeRule::{FieldDecimal, None as NoAttrs};
    use Type::*;
    &[
        ("field.constant", &[], &[Field], FieldDecimal),
        ("field.add", &[Field, Field], &[Field], NoAttrs),
        ("field.mul", &[Field, Field], &[Field], NoAttrs),
        ("field.equal", &[Field, Field], &[Bool], NoAttrs),
        ("bool.and", &[Bool, Bool], &[Bool], NoAttrs),
        ("bool.not", &[Bool], &[Bool], NoAttrs),
        ("bool.or", &[Bool, Bool], &[Bool], NoAttrs),
        ("control.require", &[Bool], &[], NoAttrs),
        ("poly.product_sum", &[Table, Table], &[Field], NoAttrs),
        ("poly.product_round", &[Table, Table], &[Round], NoAttrs),
        ("poly.boundary", &[Round], &[Field], NoAttrs),
        ("poly.round_evaluate", &[Round, Field], &[Field], NoAttrs),
        ("poly.fold", &[Table, Field], &[Table], NoAttrs),
        ("poly.evaluate", &[Table, Point], &[Field], NoAttrs),
        ("poly.empty_point", &[], &[Point], NoAttrs),
        ("poly.append_point", &[Point, Field], &[Point], NoAttrs),
        (
            "pcs.commit",
            &[ProverKey, Table],
            &[Commitment, OpeningState],
            NoAttrs,
        ),
        ("pcs.open", &[OpeningState, Point], &[Field, Proof], NoAttrs),
        (
            "pcs.check",
            &[VerifierKey, Commitment, Point, Field, Proof],
            &[Bool],
            NoAttrs,
        ),
        ("pcs.equal", &[Commitment, Commitment], &[Bool], NoAttrs),
        ("curve.generator", &[], &[Group], NoAttrs),
        ("curve.add", &[Group, Group], &[Group], NoAttrs),
        ("curve.scale", &[Group, Field], &[Group], NoAttrs),
        ("curve.equal", &[Group, Group], &[Bool], NoAttrs),
        ("curve.empty", &[], &[Groups], NoAttrs),
        ("curve.append", &[Groups, Group], &[Groups], NoAttrs),
        ("curve.at", &[Groups], &[Group], AttributeRule::NaturalIndex),
        ("curve.get", &[Groups, Index], &[Group], NoAttrs),
        ("curve.length", &[Groups], &[Index], NoAttrs),
        ("curve.commit", &[Groups, Nonce], &[Groups, Nonce], NoAttrs),
        ("curve.response", &[Field, Field, Nonce], &[Field], NoAttrs),
        (
            "transcript.challenge",
            &[Transcript],
            &[Field, Transcript],
            AttributeRule::ChallengeOrigin,
        ),
        ("random.index", &[Rng, Index], &[Index, Rng], NoAttrs),
        (
            "transcript.draw_index",
            &[Transcript, Index],
            &[Index, Transcript],
            AttributeRule::ChallengeOrigin,
        ),
        ("random.draw", &[Rng], &[Field, Rng], NoAttrs),
    ]
};

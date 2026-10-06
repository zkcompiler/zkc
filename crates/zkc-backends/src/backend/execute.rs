//! Native dispatch after common invocation admission, before common output validation.
use super::NativeBackend;
use crate::{
    Result, Value, ark, exhausted, refused,
    value::{opening_state_bytes, size},
};
use std::sync::Arc;
use zkc_runtime::interactive::Invocation;

impl NativeBackend {
    pub(super) fn execute_basic(
        &mut self,
        name: &str,
        i: &Invocation<'_>,
        args: &[Value],
    ) -> Result<Vec<Value>> {
        use Value::*;
        let p = self.core.policy;
        let result = match (name, args) {
            ("pcs.equal", [Commitment(a), Commitment(b)]) => vec![Bool(
                a.to_bytes(&p.ark_bounds()).map_err(ark)?
                    == b.to_bytes(&p.ark_bounds()).map_err(ark)?,
            )],
            ("bool.and", [Bool(a), Bool(b)]) => vec![Bool(*a && *b)],
            ("bool.not", [Bool(a)]) => vec![Bool(!*a)],
            ("bool.or", [Bool(a), Bool(b)]) => vec![Bool(*a || *b)],
            ("control.require", [Bool(true)]) => vec![],
            ("control.require", [Bool(false)]) => {
                return Err(zkc_runtime::interactive::BackendError::new(
                    "rejected:require",
                ));
            }
            ("table.relayout", [Table(t)]) => {
                p.output(size(t.len(), 32)?, i.max_output_bytes)?;
                vec![TableMsb(Arc::new(
                    zkc_arkworks::MsbTable::from_lsb(t, &p.ark_bounds()).map_err(ark)?,
                ))]
            }
            ("table.relayout", [TableMsb(t)]) => {
                p.output(size(t.len(), 32)?, i.max_output_bytes)?;
                vec![Table(Arc::new(t.to_lsb(&p.ark_bounds()).map_err(ark)?))]
            }
            ("poly.product_sum", [TableMsb(a), TableMsb(b)]) => {
                vec![Field(a.product_boolean_sum(b).map_err(ark)?)]
            }
            ("poly.product_round", [TableMsb(a), TableMsb(b)]) => {
                vec![Round(a.round_product(b).map_err(ark)?)]
            }
            ("poly.fold", [TableMsb(t), Field(r)]) => {
                p.output(size(t.len() / 2, 32)?, i.max_output_bytes)?;
                vec![TableMsb(Arc::new(t.restrict_first(*r).map_err(ark)?))]
            }
            ("poly.evaluate", [TableMsb(t), Point(point)]) => {
                vec![Field(t.evaluate(point).map_err(ark)?)]
            }
            ("poly.table_arity", [Table(t)]) => vec![Index(t.arity() as u64)],
            ("poly.table_arity", [TableMsb(t)]) => vec![Index(t.arity() as u64)],
            ("poly.product_sum", [Table(a), Table(b)]) => {
                vec![Field(a.product_boolean_sum(b).map_err(ark)?)]
            }
            ("poly.product_round", [Table(a), Table(b)]) => {
                vec![Round(a.round_product(b).map_err(ark)?)]
            }
            ("poly.fold", [Table(t), Field(r)]) => {
                p.output(size(t.len() / 2, 32)?, i.max_output_bytes)?;
                vec![Table(Arc::new(t.restrict_first(*r).map_err(ark)?))]
            }
            ("poly.evaluate", [Table(t), Point(point)]) => {
                vec![Field(t.evaluate(point).map_err(ark)?)]
            }
            ("poly.empty_point", []) => vec![Point(Arc::from([]))],
            ("poly.append_point", [Point(point), Field(r)]) => {
                let n = point
                    .len()
                    .checked_add(1)
                    .ok_or_else(|| exhausted("point-size"))?;
                p.arity(n)?;
                p.output(size(n, 32)?, i.max_output_bytes)?;
                let mut next = Vec::new();
                next.try_reserve_exact(n)
                    .map_err(|_| exhausted("allocation"))?;
                next.extend_from_slice(point);
                next.push(*r);
                vec![Point(next.into())]
            }
            ("pcs.commit", [ProverKey(key), Table(t)]) => {
                if key.metadata().arity() != t.arity() {
                    return Err(refused("arity-mismatch"));
                }
                // Check both outputs before the helper allocates. Shared input
                // backing is charged again because the private result retains it.
                p.output(
                    opening_state_bytes(t, key.metadata().arity())?
                        .checked_add(512)
                        .ok_or_else(|| exhausted("output-bytes"))?,
                    i.max_output_bytes,
                )?;
                let state = Arc::new(key.commit(t).map_err(ark)?);
                vec![
                    Commitment(Arc::new(state.commitment().clone())),
                    OpeningState(state),
                ]
            }
            ("pcs.open", [OpeningState(state), Point(point)]) => {
                p.output(
                    size(state.commitment().metadata().arity(), 192)?
                        .checked_add(512)
                        .ok_or_else(|| exhausted("output-bytes"))?,
                    i.max_output_bytes,
                )?;
                let (value, proof) = state.open(point).map_err(ark)?;
                vec![Field(value), Proof(Arc::new(proof))]
            }
            (
                "pcs.check",
                [
                    VerifierKey(key),
                    Commitment(c),
                    Point(point),
                    Field(value),
                    Proof(proof),
                ],
            ) => vec![Bool(key.check(c, point, *value, proof).map_err(ark)?)],
            _ => return Err(refused("kernel-operands")),
        };
        Ok(result)
    }
}

/// Independent native port facts, also used for exact implementation assembly.
pub(crate) const CONTRACTS: &[crate::bindings::Contract] = {
    use crate::bindings::{control, pcs, poly};
    use zkc_runtime::interactive::{AttributeRule, Type::*};
    &[
        control::operation("bool.and", &[Bool, Bool], &[Bool], AttributeRule::None),
        control::operation("bool.not", &[Bool], &[Bool], AttributeRule::None),
        control::operation("bool.or", &[Bool, Bool], &[Bool], AttributeRule::None),
        control::operation("control.require", &[Bool], &[], AttributeRule::None),
        poly::operation("poly.table_arity", &[Table], &[Index], AttributeRule::None),
        poly::operation(
            "poly.product_sum",
            &[Table, Table],
            &[Field],
            AttributeRule::None,
        ),
        poly::operation(
            "poly.product_round",
            &[Table, Table],
            &[Round],
            AttributeRule::None,
        ),
        poly::operation("poly.fold", &[Table, Field], &[Table], AttributeRule::None),
        poly::operation(
            "poly.evaluate",
            &[Table, Point],
            &[Field],
            AttributeRule::None,
        ),
        poly::operation("poly.empty_point", &[], &[Point], AttributeRule::None),
        poly::operation(
            "poly.append_point",
            &[Point, Field],
            &[Point],
            AttributeRule::None,
        ),
        pcs::operation(
            "pcs.commit",
            &[ProverKey, Table],
            &[Commitment, OpeningState],
            AttributeRule::None,
        ),
        pcs::operation(
            "pcs.open",
            &[OpeningState, Point],
            &[Field, Proof],
            AttributeRule::None,
        ),
        pcs::operation(
            "pcs.check",
            &[VerifierKey, Commitment, Point, Field, Proof],
            &[Bool],
            AttributeRule::None,
        ),
        pcs::operation(
            "pcs.equal",
            &[Commitment, Commitment],
            &[Bool],
            AttributeRule::None,
        ),
    ]
};
pub(crate) const SPECIAL_OPERATIONS: &[&str] = &["table.relayout"];

pub(crate) const ALTERNATIVES: &[crate::backend::registry::Alternative] = &[
    crate::backend::registry::Alternative {
        identity: "arkworks-msb/poly.product_sum",
        original: "arkworks/poly.product_sum",
        primary: zkc_runtime::interactive::Identity::Bls12381Fr,
        ports: crate::bindings::PortTransform::Msb,
        handler: None,
        public_operands: false,
    },
    crate::backend::registry::Alternative {
        identity: "arkworks-msb/poly.product_round",
        original: "arkworks/poly.product_round",
        primary: zkc_runtime::interactive::Identity::Bls12381Fr,
        ports: crate::bindings::PortTransform::Msb,
        handler: None,
        public_operands: false,
    },
    crate::backend::registry::Alternative {
        identity: "arkworks-msb/poly.fold",
        original: "arkworks/poly.fold",
        primary: zkc_runtime::interactive::Identity::Bls12381Fr,
        ports: crate::bindings::PortTransform::Msb,
        handler: None,
        public_operands: false,
    },
    crate::backend::registry::Alternative {
        identity: "arkworks-msb/poly.evaluate",
        original: "arkworks/poly.evaluate",
        primary: zkc_runtime::interactive::Identity::Bls12381Fr,
        ports: crate::bindings::PortTransform::Msb,
        handler: None,
        public_operands: false,
    },
    crate::backend::registry::Alternative {
        identity: "arkworks-msb/poly.empty_point",
        original: "arkworks/poly.empty_point",
        primary: zkc_runtime::interactive::Identity::Bls12381Fr,
        ports: crate::bindings::PortTransform::Msb,
        handler: None,
        public_operands: false,
    },
    crate::backend::registry::Alternative {
        identity: "arkworks-msb/poly.append_point",
        original: "arkworks/poly.append_point",
        primary: zkc_runtime::interactive::Identity::Bls12381Fr,
        ports: crate::bindings::PortTransform::Msb,
        handler: None,
        public_operands: false,
    },
    crate::backend::registry::Alternative {
        identity: "arkworks-msb/poly.boundary",
        original: "arkworks/poly.boundary",
        primary: zkc_runtime::interactive::Identity::Bls12381Fr,
        ports: crate::bindings::PortTransform::Msb,
        handler: None,
        public_operands: false,
    },
    crate::backend::registry::Alternative {
        identity: "arkworks-msb/poly.round_evaluate",
        original: "arkworks/poly.round_evaluate",
        primary: zkc_runtime::interactive::Identity::Bls12381Fr,
        ports: crate::bindings::PortTransform::Msb,
        handler: None,
        public_operands: false,
    },
];

//! Native dispatch after common invocation admission, before common output validation.
use super::NativeBackend;
use crate::{
    Result, Value, ark, exhausted, refused,
    value::{opening_state_bytes, size},
};
use std::sync::Arc;
use zkc_runtime::interactive::Invocation;

impl NativeBackend {
    pub(super) fn execute(
        &mut self,
        name: &str,
        i: &Invocation<'_>,
        args: &[Value],
    ) -> Result<Vec<Value>> {
        use Value::*;
        if name.starts_with("resource_unit.") {
            let values = match (name, args) {
                ("resource_unit.create", []) => {
                    self.core.policy.output(512, i.max_output_bytes)?;
                    vec![
                        self.core.resources.create_unit(
                            i.frame,
                            i.binding.signature().outputs[0]
                                .logical()
                                .resource_domain()
                                .expect("an admitted unit creation names its domain"),
                        )?,
                    ]
                }
                ("resource_unit.pass", [ResourceUnit(token)]) => {
                    self.core.policy.output(512, i.max_output_bytes)?;
                    vec![self.core.resources.pass_unit(i.frame, token.capability())?]
                }
                ("resource_unit.consume", [ResourceUnit(token)]) => {
                    self.core
                        .resources
                        .consume_unit(i.frame, token.capability())?;
                    vec![]
                }
                _ => unreachable!("invoke checked the operands against the signature"),
            };
            return Ok(values);
        }
        if crate::requires_public_operands(i.binding.implementation())
            && !self.public_roles.permits(i.frame.role())
        {
            return Err(refused("public-operands-required"));
        }
        // Cheap output bound checks happen before allocating polynomial/PCS results.
        let p = self.core.policy;
        let field = i
            .binding
            .signature()
            .inputs
            .iter()
            .chain(&i.binding.signature().outputs)
            .find_map(|t| t.logical().identity().scalar_field());
        if let Some(result) = crate::external_kernels::apply(
            name,
            args,
            i.attributes,
            &p,
            i.max_output_bytes,
            &mut self.external_work,
        ) {
            return result;
        }
        if let Some(result) =
            crate::kernels::indices::apply(name, args, i.attributes, &p, i.max_output_bytes)
        {
            return result;
        }
        if let Some(result) = crate::oracle::apply(name, args, i, &p) {
            return result;
        }
        if let Some(result) = crate::diagonal::apply(i, args, &p) {
            return result;
        }
        if let Some(result) = crate::kernels::conversions::apply(name, args, i, &p) {
            return result;
        }
        if let Some(result) = crate::kernels::bn254::apply(name, field, args, i, &p) {
            return result;
        }
        if let Some(result) =
            crate::plonky3::numerical::apply(name, field, args, i, &p, &self.core.polynomial)
        {
            return result;
        }
        if let Some(result) = crate::kernels::arithmetic::apply(name, field, args, i, &p) {
            return result;
        }
        if let Some(result) = crate::kernels::curve::apply(name, field, args, i, &p) {
            return result;
        }
        if let Some(result) =
            crate::kernels::resources::apply(name, args, i, &p, &mut self.core.resources)
        {
            return result;
        }
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

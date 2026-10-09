//! Explicit BLS-only conversions between distinct mathematical objects.
use crate::kernels::arithmetic::reserve;
use crate::{Policy, Result, Value, ark, exhausted, refused, value::size};
use std::sync::Arc;
use zkc_runtime::interactive::{Invocation, Representation};
pub(crate) fn apply(
    name: &str,
    args: &[Value],
    i: &Invocation<'_>,
    p: &Policy,
) -> Result<Vec<Value>> {
    if !matches!(
        name,
        "vector.from_point"
            | "vector.to_point"
            | "vector.from_table"
            | "vector.to_table"
            | "poly.equality_weights"
    ) {
        return Err(refused("kernel-operands"));
    }
    use Value::*;
    let value = match (name, args) {
        ("vector.from_point", [Point(a)]) => {
            p.vector(a.len())?;
            p.output(size(a.len(), 32)?, i.max_output_bytes)?;
            Vector(a.clone())
        }
        ("vector.to_point", [Vector(a)]) => {
            p.arity(a.len())?;
            p.output(size(a.len(), 32)?, i.max_output_bytes)?;
            Point(a.clone())
        }
        ("vector.from_table", [Table(t)]) => {
            p.vector(t.len())?;
            p.output(size(t.len(), 32)?, i.max_output_bytes)?;
            Vector(t.logical_values().map_err(ark)?.into())
        }
        ("vector.from_table", [TableMsb(t)]) => {
            p.vector(t.len())?;
            p.output(size(t.len(), 32)?, i.max_output_bytes)?;
            let mut a = reserve(t.len())?;
            a.extend_from_slice(t.logical_values());
            Vector(a.into())
        }
        ("vector.to_table", [Vector(a)]) => {
            if !a.len().is_power_of_two() {
                return Err(refused("invalid-table-length"));
            }
            p.table_len(a.len().trailing_zeros() as usize)?;
            p.output(size(a.len(), 32)?, i.max_output_bytes)?;
            if i.binding.signature().outputs[0].representation() == Representation::TableMsb {
                TableMsb(Arc::new(
                    zkc_arkworks::MsbTable::from_logical(a, &p.ark_bounds()).map_err(ark)?,
                ))
            } else {
                Value::table(a, p)?
            }
        }
        ("poly.equality_weights", [Point(a)]) => {
            let n = p.table_len(a.len())?;
            p.vector(n)?;
            p.output(size(n, 32)?, i.max_output_bytes)?;
            let mut w = reserve(n)?;
            w.resize(n, crate::Scalar::from(0));
            w[0] = crate::Scalar::from(1);
            let mut len = 1usize;
            for r in a.iter() {
                for j in (0..len).rev() {
                    let old = w[j];
                    w[2 * j] = old * (crate::Scalar::from(1) - r);
                    w[2 * j + 1] = old * r;
                }
                len = len
                    .checked_mul(2)
                    .ok_or_else(|| exhausted("size-overflow"))?;
            }
            Vector(w.into())
        }
        _ => return Err(refused("kernel-operands")),
    };
    Ok(vec![value])
}

/// Independent native port facts, also used for exact implementation assembly.
pub(crate) const CONTRACTS: &[crate::bindings::Contract] = {
    use crate::bindings::{field, poly};
    use zkc_runtime::interactive::{AttributeRule, Type::*};
    &[
        field::operation(
            "vector.from_point",
            &[Point],
            &[Vector],
            AttributeRule::None,
        ),
        field::operation("vector.to_point", &[Vector], &[Point], AttributeRule::None),
        field::operation(
            "vector.from_table",
            &[Table],
            &[Vector],
            AttributeRule::None,
        ),
        field::operation("vector.to_table", &[Vector], &[Table], AttributeRule::None),
        poly::operation(
            "poly.equality_weights",
            &[Point],
            &[Vector],
            AttributeRule::None,
        ),
    ]
};

pub(crate) const ALTERNATIVES: &[crate::backend::registry::Alternative] = &[
    crate::backend::registry::Alternative {
        identity: "arkworks-msb/vector.from_table",
        original: "arkworks/vector.from_table",
        primary: zkc_runtime::interactive::Identity::Bls12381Fr,
        ports: crate::bindings::PortTransform::Msb,
        handler: None,
    },
    crate::backend::registry::Alternative {
        identity: "arkworks-msb/vector.to_table",
        original: "arkworks/vector.to_table",
        primary: zkc_runtime::interactive::Identity::Bls12381Fr,
        ports: crate::bindings::PortTransform::Msb,
        handler: None,
    },
];

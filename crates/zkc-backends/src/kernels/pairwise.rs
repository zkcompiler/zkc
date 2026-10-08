//! An explicitly selected two-accumulator dot product over the existing BLS
//! vector representation. Selection changes neither source ports nor defaults.
use crate::{Policy, Result, Scalar, Value, refused};
pub(crate) fn apply(args: &[Value], policy: &Policy, available: usize) -> Result<Vec<Value>> {
    let [Value::Vector(a), Value::Vector(b)] = args else {
        return Err(refused("kernel-operands"));
    };
    // Match the ordinary scalar-result preflight before shape-dependent work.
    policy.output(512, available)?;
    super::arithmetic::equal_len(a.len(), b.len())?;
    let mut even = Scalar::from(0);
    let mut odd = Scalar::from(0);
    let mut pairs = a.iter().zip(b.iter());
    while let Some((a, b)) = pairs.next() {
        even += *a * b;
        if let Some((a, b)) = pairs.next() {
            odd += *a * b;
        }
    }
    Ok(vec![Value::Field(even + odd)])
}

pub(crate) const ALTERNATIVES: &[crate::backend::registry::Alternative] =
    &[crate::backend::registry::Alternative {
        identity: "arkworks-pairwise/vector.dot",
        original: "arkworks/vector.dot",
        primary: zkc_runtime::interactive::Identity::Bls12381Fr,
        ports: crate::bindings::PortTransform::Default,
        handler: Some(crate::backend::registry::pairwise),
    }];

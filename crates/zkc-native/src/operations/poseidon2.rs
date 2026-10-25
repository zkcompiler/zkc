//! Native installation of the width-16 KoalaBear Poseidon2 permutation.
//! Admission, output allocation and persistent work charging precede evaluation.
use crate::{Policy, Result, Value, refused, value::size};
use zkc_kernels::plonky3::{
    KoalaBear,
    poseidon2::{self, Error},
};
use zkc_runtime::vm::{
    AttributeRule, BoundSignature, Identity, LogicalType, OperationBinding, OperationSignature,
    PhysicalType, Type,
};

fn failure(error: Error) -> zkc_runtime::vm::BackendError {
    match error {
        Error::Width => refused("poseidon2-width"),
    }
}

pub(crate) fn signature(binding: &OperationBinding) -> Option<BoundSignature> {
    if binding.contract != "hash.poseidon2_16"
        || binding.arguments != ["koala-bear"]
        || binding.implementation != "plonky3/hash.poseidon2_16"
    {
        return None;
    }
    let vector =
        PhysicalType::default_for(LogicalType::new(Type::Vector, Identity::KoalaBear).ok()?)
            .ok()?;
    Some(OperationSignature {
        inputs: vec![vector.clone()],
        outputs: vec![vector],
        attributes: AttributeRule::None,
    })
}

/// Shape, element, output and work checks all precede the first permutation.
pub(crate) fn apply(
    name: &str,
    args: &[Value],
    attributes: &[String],
    policy: &Policy,
    available: usize,
    budget: &mut crate::operations::external::Budget,
) -> Result<Vec<Value>> {
    if !attributes.is_empty() {
        return Err(refused("poseidon2-attributes"));
    }
    let ("hash.poseidon2_16", [Value::KoalaBearVector(states)]) = (name, args) else {
        return Err(refused("poseidon2-operands"));
    };
    let work = poseidon2::work(states.len()).map_err(failure)?;
    let element = std::mem::size_of::<KoalaBear>();
    policy.vector_width(states.len(), element)?;
    policy.output(size(states.len(), element)?, available)?;
    budget.charge(work)?;
    let mut out = crate::operations::arithmetic::reserve(states.len())?;
    poseidon2::permute_states(states, &mut out).map_err(failure)?;
    Ok(vec![Value::KoalaBearVector(out.into())])
}

pub(crate) const IMPLEMENTATIONS: &[(&str, &str)] =
    &[("plonky3/hash.poseidon2_16", "hash.poseidon2_16")];

#[cfg(test)]
mod tests {
    use super::*;
    use crate::operations::external::Budget;
    use p3_koala_bear::default_koalabear_poseidon2_16;
    use p3_symmetric::Permutation;
    use zkc_kernels::plonky3::poseidon2::WIDTH;

    fn states(n: usize) -> Value {
        Value::KoalaBearVector((0..n as u32).map(KoalaBear::new).collect::<Vec<_>>().into())
    }
    fn run(args: &[Value], budget: &mut Budget, available: usize) -> Result<Vec<Value>> {
        apply(
            "hash.poseidon2_16",
            args,
            &[],
            &Policy::default(),
            available,
            budget,
        )
    }

    #[test]
    fn batched_states_equal_independent_permutations() {
        let mut budget = Budget::default();
        let out = run(&[states(48)], &mut budget, usize::MAX).unwrap();
        let Value::KoalaBearVector(out) = &out[0] else {
            panic!("vector")
        };
        assert_eq!(budget.spent, 3);
        for (i, block) in out.chunks(WIDTH).enumerate() {
            let mut expected: [KoalaBear; WIDTH] =
                std::array::from_fn(|j| KoalaBear::new((i * WIDTH + j) as u32));
            default_koalabear_poseidon2_16().permute_mut(&mut expected);
            assert_eq!(block, expected);
        }
        let empty = run(&[states(0)], &mut budget, usize::MAX).unwrap();
        assert!(matches!(&empty[0], Value::KoalaBearVector(v) if v.is_empty()));
        assert_eq!(budget.spent, 3);
    }

    #[test]
    fn shape_output_and_work_failures_precede_permutation() {
        let mut budget = Budget::default();
        for n in [1, 15, 17, 31] {
            assert_eq!(
                run(&[states(n)], &mut budget, usize::MAX).unwrap_err().code,
                "refused:poseidon2-width"
            );
        }
        assert_eq!(
            run(&[states(16)], &mut budget, 0).unwrap_err().code,
            "exhausted:output-bytes"
        );
        let mut low = Budget { limit: 1, spent: 0 };
        assert_eq!(
            run(&[states(32)], &mut low, usize::MAX).unwrap_err().code,
            "exhausted:external-work-limit"
        );
        assert_eq!((budget.spent, low.spent), (0, 0));
        assert_eq!(
            apply(
                "hash.poseidon2_16",
                &[Value::Index(0)],
                &[],
                &Policy::default(),
                usize::MAX,
                &mut budget
            )
            .unwrap_err()
            .code,
            "refused:poseidon2-operands"
        );
        assert_eq!(
            apply(
                "hash.poseidon2_16",
                &[states(16)],
                &["1".into()],
                &Policy::default(),
                usize::MAX,
                &mut budget
            )
            .unwrap_err()
            .code,
            "refused:poseidon2-attributes"
        );
    }

    #[test]
    fn allocation_failure_preserves_the_charged_work_and_input() {
        let input = states(32);
        let Value::KoalaBearVector(values) = &input else {
            panic!("vector")
        };
        let saved = values.to_vec();
        let mut budget = Budget::default();
        let _failure = zkc_kernels::allocation::failure::after(0);
        let error = run(std::slice::from_ref(&input), &mut budget, usize::MAX).unwrap_err();
        assert_eq!(error.code, "exhausted:allocation");
        assert_eq!(budget.spent, 2);
        assert_eq!(values.as_ref(), saved);
    }

    #[test]
    fn only_the_koala_bear_binding_is_installed() {
        for (arguments, implementation, admitted) in [
            (vec!["koala-bear"], "plonky3/hash.poseidon2_16", true),
            (
                vec!["koala-bear.ext8-binomial3"],
                "plonky3/hash.poseidon2_16",
                false,
            ),
            (vec!["bls12-381.fr"], "arkworks/hash.poseidon2_16", false),
            (vec!["koala-bear"], "native/hash.poseidon2_16", false),
            (vec![], "plonky3/hash.poseidon2_16", false),
        ] {
            let binding = OperationBinding {
                contract: "hash.poseidon2_16".into(),
                arguments: arguments.into_iter().map(String::from).collect(),
                implementation: implementation.into(),
                physical_arguments: vec![],
            };
            assert_eq!(signature(&binding).is_some(), admitted, "{binding:?}");
        }
    }
}

//! The width-16 Poseidon2 permutation over KoalaBear with Plonky3 0.8.0's
//! default parameters: `p3_koala_bear::default_koalabear_poseidon2_16`, with
//! eight full rounds, twenty partial rounds, the cube S-box, the Grain-LFSR round
//! constants and the internal diagonal pinned by that release. The kernel
//! permutes each consecutive 16-element state of one vector. See
//! docs/spec/domains/permutations.md.
use super::KoalaBear;
use crate::external::Work;
use crate::{Policy, Result, Value, refused, value::size};
use p3_koala_bear::{Poseidon2KoalaBear, default_koalabear_poseidon2_16};
use p3_symmetric::Permutation;
use std::sync::OnceLock;
use zkc_runtime::interactive::{
    AttributeRule, BoundSignature, Identity, KernelSignature, LogicalType, OperationBinding,
    PhysicalType, Type,
};

/// Field elements in one permutation state.
pub const WIDTH: usize = 16;

/// The installed instance, constructed once from the pinned constants.
pub fn permutation() -> &'static Poseidon2KoalaBear<WIDTH> {
    static PERMUTATION: OnceLock<Poseidon2KoalaBear<WIDTH>> = OnceLock::new();
    PERMUTATION.get_or_init(default_koalabear_poseidon2_16)
}

/// Logical work of permuting `elements` values: one unit per state.
pub fn work(elements: usize) -> Result<Work> {
    if !elements.is_multiple_of(WIDTH) {
        return Err(refused("poseidon2-width"));
    }
    Ok(Work {
        permutations: (elements / WIDTH) as u64,
        ..Work::default()
    })
}

/// Permute every consecutive state of `states` into `out`, in order.
pub fn permute_states(states: &[KoalaBear], out: &mut Vec<KoalaBear>) -> Result<()> {
    if !states.len().is_multiple_of(WIDTH) {
        return Err(refused("poseidon2-width"));
    }
    for state in states.as_chunks::<WIDTH>().0 {
        let mut state = *state;
        permutation().permute_mut(&mut state);
        out.extend_from_slice(&state);
    }
    Ok(())
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
    Some(KernelSignature {
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
    budget: &mut crate::external_kernels::Budget,
) -> Result<Vec<Value>> {
    if !attributes.is_empty() {
        return Err(refused("poseidon2-attributes"));
    }
    let ("hash.poseidon2_16", [Value::KoalaBearVector(states)]) = (name, args) else {
        return Err(refused("poseidon2-operands"));
    };
    let work = work(states.len())?;
    let element = std::mem::size_of::<KoalaBear>();
    policy.vector_width(states.len(), element)?;
    policy.output(size(states.len(), element)?, available)?;
    budget.charge(work)?;
    let mut out = crate::kernels::arithmetic::reserve(states.len())?;
    permute_states(states, &mut out)?;
    Ok(vec![Value::KoalaBearVector(out.into())])
}

pub(crate) const IMPLEMENTATIONS: &[(&str, &str)] =
    &[("plonky3/hash.poseidon2_16", "hash.poseidon2_16")];

#[cfg(test)]
mod tests {
    use super::*;
    use crate::external_kernels::Budget;

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
            };
            assert_eq!(signature(&binding).is_some(), admitted, "{binding:?}");
        }
    }
}

//! Regression contracts for every registered residue collection.
use super::{binding, check};
use crate::backend::validation::Core;
use crate::{Buffer, Domain, EntryPolicy, Policy, Value};
use p3_field::PrimeCharacteristicRing;
use std::mem::size_of;
use zkc_runtime::vm::{Backing, Identity, Value as _};

fn core(policy: Policy) -> Core {
    Core::new(
        policy,
        EntryPolicy::new(Domain::new("P", "session", "main", None), None),
        Default::default(),
    )
}

fn backing(value: &Value, bytes: usize) -> Backing {
    assert_eq!(value.retained_bytes(), bytes);
    let mut parts = Vec::new();
    assert_eq!(
        value.retained_parts(&mut |b| {
            parts.push(b);
            true
        }),
        0
    );
    assert_eq!(parts.len(), 1);
    assert_eq!(parts[0].bytes(), bytes);
    assert_eq!(value.validation_backing(), Some(parts[0]));
    parts[0]
}

#[test]
fn storage_widths_preserve_existing_charges() {
    // Independent expectations keep a representation change from silently
    // changing this structural refactor's accounting contract.
    assert_eq!(
        (
            size_of::<crate::KoalaBear>(),
            size_of::<(u32, u32, crate::KoalaBear)>()
        ),
        (4, 12)
    );
    assert_eq!(
        (
            size_of::<crate::KoalaBearExt4>(),
            size_of::<(u32, u32, crate::KoalaBearExt4)>()
        ),
        (16, 24)
    );
    assert_eq!(
        (
            size_of::<crate::KoalaBearExt8>(),
            size_of::<(u32, u32, crate::KoalaBearExt8)>()
        ),
        (32, 40)
    );
    assert_eq!(
        (
            size_of::<crate::BabyBear>(),
            size_of::<(u32, u32, crate::BabyBear)>()
        ),
        (4, 12)
    );
    assert_eq!(
        (
            size_of::<crate::BabyBearExt4>(),
            size_of::<(u32, u32, crate::BabyBearExt4)>()
        ),
        (16, 24)
    );
    assert_eq!(
        (
            size_of::<crate::Goldilocks>(),
            size_of::<(u32, u32, crate::Goldilocks)>()
        ),
        (8, 16)
    );
    assert_eq!(
        (
            size_of::<crate::GoldilocksExt2>(),
            size_of::<(u32, u32, crate::GoldilocksExt2)>()
        ),
        (16, 24)
    );
}

macro_rules! collection_tests {
    ((); $(($s:ty, $id:ident, $base:ident, $f:ident, $v:ident, $m:ident, $p:ident, $r:ident, $sparse:ident, $ft:literal, $vt:literal, $mt:literal),)*) => { $(
        #[allow(non_snake_case)]
        mod $id {
            use super::*;
            const ONE: $s = <$s>::ONE;
            const ZERO: $s = <$s>::ZERO;

            #[test]
            fn capacity_and_backing_follow_the_owner_across_vector_and_polynomial() {
                let mut storage = Vec::with_capacity(17);
                storage.extend([ONE, ONE]);
                let capacity = storage.capacity();
                let buffer: Buffer<$s> = storage.into();
                let bytes = 256 + capacity * size_of::<$s>();
                let vector = Value::$v(buffer.clone());
                let polynomial = Value::$p(buffer.clone());
                let original = backing(&vector, bytes);
                assert_eq!(backing(&polynomial, bytes), original);
                assert_eq!(backing(&vector.clone(), bytes), original);
                let independent: Buffer<$s> = buffer.to_vec().into();
                assert_ne!(
                    backing(
                        &Value::$v(independent.clone()),
                        256 + independent.storage_capacity() * size_of::<$s>()
                    ),
                    original
                );
                for value in [&vector, &polynomial] {
                    core(Policy {
                        max_value_bytes: bytes,
                        ..Policy::default()
                    })
                    .validate(value)
                    .unwrap();
                    assert_eq!(
                        core(Policy {
                            max_value_bytes: bytes - 1,
                            max_table_elements: 0,
                            ..Policy::default()
                        })
                        .validate(value)
                        .unwrap_err()
                        .code,
                        "exhausted:output-bytes"
                    );
                    assert_eq!(
                        core(Policy {
                            max_table_elements: 1,
                            ..Policy::default()
                        })
                        .validate(value)
                        .unwrap_err()
                        .code,
                        "exhausted:element-limit"
                    );
                }
                let empty: Buffer<$s> = Buffer::default();
                let empty_vector = Value::$v(empty.clone());
                assert_eq!(
                    backing(&empty_vector, 256),
                    backing(&Value::$p(empty), 256)
                );
                assert_ne!(
                    backing(&empty_vector, 256),
                    backing(&Value::$v(Buffer::default()), 256)
                );
            }

            #[test]
            fn normalization_follows_retained_bytes_and_element_policy() {
                let native = core(Policy::default());
                for coefficients in [vec![], vec![ONE], vec![ZERO, ONE]] {
                    native
                        .validate(&Value::$p(coefficients.into()))
                        .unwrap();
                }
                for coefficients in [vec![ZERO], vec![ONE, ZERO]] {
                    let vector = Value::$v(coefficients.clone().into());
                    native.validate(&vector).unwrap();
                    let polynomial = Value::$p(coefficients.into());
                    assert_eq!(
                        native.validate(&polynomial).unwrap_err().code,
                        "refused:polynomial-normalization"
                    );
                    assert_eq!(
                        core(Policy {
                            max_table_elements: 0,
                            ..Policy::default()
                        })
                        .validate(&polynomial)
                        .unwrap_err()
                        .code,
                        "exhausted:element-limit"
                    );
                    assert_eq!(
                        core(Policy {
                            max_value_bytes: polynomial.retained_bytes() - 1,
                            max_table_elements: 0,
                            ..Policy::default()
                        })
                        .validate(&polynomial)
                        .unwrap_err()
                        .code,
                        "exhausted:output-bytes"
                    );
                }
                // Inline values keep the historical conservative charge and
                // remain independent of collection element ceilings.
                for value in [Value::$f(ONE), Value::$r([ONE; 3])] {
                    assert_eq!(value.retained_bytes(), 512);
                    assert_eq!(
                        value.retained_parts(&mut |_| panic!("inline value has no backing")),
                        512
                    );
                    assert_eq!(value.validation_backing(), None);
                    core(Policy {
                        max_value_bytes: 512,
                        max_table_elements: 0,
                        ..Policy::default()
                    })
                    .validate(&value)
                    .unwrap();
                    assert_eq!(
                        core(Policy {
                            max_value_bytes: 511,
                            ..Policy::default()
                        })
                        .validate(&value)
                        .unwrap_err()
                        .code,
                        "exhausted:output-bytes"
                    );
                }
            }

            #[test]
            fn matrix_entry_storage_and_policy_keep_their_existing_contract() {
                let matrix =
                    crate::matrix::from_entries(2, 3, &[(0, 1, ONE), (1, 2, ONE)], &Policy::default())
                        .unwrap();
                let value = Value::$m(matrix.clone());
                let bytes = 256 + 2 * size_of::<(u32, u32, $s)>();
                let original = backing(&value, bytes);
                assert_eq!(
                    backing(&Value::$m(matrix.clone()), bytes),
                    original
                );
                let independent =
                    crate::matrix::from_entries(2, 3, matrix.entries(), &Policy::default()).unwrap();
                assert_ne!(
                    backing(&Value::$m(independent), bytes),
                    original
                );
                core(Policy {
                    max_value_bytes: bytes,
                    max_table_elements: 0,
                    ..Policy::default()
                })
                .validate(&value)
                .unwrap();
                assert_eq!(
                    core(Policy {
                        max_value_bytes: bytes - 1,
                        ..Policy::default()
                    })
                    .validate(&value)
                    .unwrap_err()
                    .code,
                    "exhausted:output-bytes"
                );
            }

            #[test]
            fn output_aliases_are_free_and_fresh_allocations_charge_capacity() {
                let mut storage = Vec::with_capacity(17);
                storage.extend([ONE, ONE]);
                let bytes = 256 + storage.capacity() * size_of::<$s>();
                let operand = Value::$v(storage.into());
                let mut storage = Vec::with_capacity(23);
                storage.extend([ONE, ONE]);
                let fresh_bytes = 256 + storage.capacity() * size_of::<$s>();
                let fresh = Value::$v(storage.into());
                let signature = || {
                    binding(
                        "vector.split",
                        &[Identity::$id.name()],
                        "plonky3",
                    )
                };
                check(
                    signature(),
                    vec![operand.clone()],
                    vec![operand.clone(), operand.clone()],
                    0,
                    2 * bytes,
                );
                check(
                    signature(),
                    vec![operand.clone()],
                    vec![operand.clone(), fresh.clone()],
                    fresh_bytes,
                    bytes + fresh_bytes,
                );
                check(
                    signature(),
                    vec![operand.clone()],
                    vec![fresh.clone(), operand],
                    fresh_bytes,
                    bytes + fresh_bytes,
                );
                check(
                    signature(),
                    vec![Value::$v(vec![ONE, ONE].into())],
                    vec![fresh.clone(), fresh],
                    fresh_bytes,
                    2 * fresh_bytes,
                );
            }
        }
    )* };
}
crate::fields::inventory!([collection_tests], ());

//! Shared workloads for ordinary correctness and isolated thread-creation checks.
use ark_ff::{BigInteger, PrimeField};
use zkc_kernels::{arkworks::bls12_381, cpu::CpuExecution};

fn full_width_scalars<F: PrimeField>() -> [F; 4] {
    let high = F::from(2).pow([128]);
    let dense = F::from_le_bytes_mod_order(&[0xa5; 32]);
    let scalars = [high, -high, dense, -dense];
    // Both signs must reach ark-ec's BigInt partition, rather than a small
    // positive/negative shortcut. A nonempty partition triggers private pools
    // when the offending parallel feature is enabled, even for a singleton.
    for scalar in scalars {
        assert!(scalar.into_bigint().num_bits() > 64);
        assert!((-scalar).into_bigint().num_bits() > 64);
    }
    assert!(dense.into_bigint().num_bits() > 200);
    scalars
}

pub fn full_width_msms() {
    macro_rules! check {
        ($group:ty, $field:ty) => {{
            let generator = <$group>::generator();
            let wide = full_width_scalars::<$field>();
            for scalar in wide {
                assert_eq!(
                    <$group>::msm(&[scalar], &[generator]).unwrap(),
                    generator.scale(scalar),
                );
            }
            let scalars: Vec<_> = (0..33)
                .map(|i| match i % 8 {
                    0..=3 => wide[i % 8],
                    4 => <$field>::from(0),
                    5 => <$field>::from(1),
                    6 => -<$field>::from(1),
                    _ => <$field>::from(5),
                })
                .collect();
            let points: Vec<_> = (0..scalars.len())
                .map(|i| match i % 7 {
                    0 => <$group>::identity(),
                    1 => generator.neg(),
                    _ => generator.scale(<$field>::from((i + 1) as u64)),
                })
                .collect();
            // Individual scalar multiplication and addition are independent
            // of VariableBaseMSM's classification and WNAF dispatch.
            let expected = points
                .iter()
                .zip(&scalars)
                .fold(<$group>::identity(), |sum, (point, scalar)| {
                    sum.add(&point.scale(*scalar))
                });
            assert_eq!(<$group>::msm(&scalars, &points).unwrap(), expected);
            assert_eq!(<$group>::msm(&[], &[]).unwrap(), <$group>::identity());
            assert!(<$group>::msm(&scalars[..32], &points).is_err());
        }};
    }
    check!(bls12_381::G1, bls12_381::Scalar);
    check!(bls12_381::G2, bls12_381::Scalar);
    check!(
        zkc_kernels::arkworks::bn254::G1,
        zkc_kernels::arkworks::bn254::Scalar
    );
    check!(
        zkc_kernels::arkworks::bn254::G2,
        zkc_kernels::arkworks::bn254::Scalar
    );
}

pub struct PcsFixture {
    keys: bls12_381::Keys,
    table: bls12_381::Table,
    point: [bls12_381::Scalar; 3],
    value: bls12_381::Scalar,
    bounds: bls12_381::Bounds,
}

impl PcsFixture {
    pub fn new(cpu: &CpuExecution) -> Self {
        use ark_std::rand::{SeedableRng, rngs::StdRng};
        use bls12_381::{Bounds, Keys, Scalar, Table};
        let bounds = Bounds::new(3, 8, 1 << 20, 24);
        let keys = cpu
            .execute(|| Keys::setup_with_rng(3, &mut StdRng::seed_from_u64(17), &bounds).unwrap());
        let [high, _, dense, _] = full_width_scalars::<Scalar>();
        let values = [
            high,
            dense,
            -high,
            -dense,
            high + dense,
            high * Scalar::from(3),
            -dense * Scalar::from(5),
            dense - high,
        ];
        let point = [dense, high, -dense];
        // Independently evaluate the logical MSB-first table, including full
        // field coordinates and full-width differences in the opening MSMs.
        let value = values
            .iter()
            .enumerate()
            .map(|(i, value)| {
                point
                    .iter()
                    .enumerate()
                    .fold(*value, |term, (j, coordinate)| {
                        term * if (i >> (2 - j)) & 1 == 1 {
                            *coordinate
                        } else {
                            Scalar::from(1) - coordinate
                        }
                    })
            })
            .sum();
        Self {
            keys,
            table: Table::from_logical(&values, &bounds).unwrap(),
            point,
            value,
            bounds,
        }
    }

    pub fn check(&self) -> (Vec<u8>, Vec<u8>) {
        let committed = self.keys.prover_key().commit(&self.table).unwrap();
        let (value, proof) = committed.open(&self.point).unwrap();
        assert_eq!(value, self.value);
        assert!(
            self.keys
                .verifier_key()
                .check(committed.commitment(), &self.point, value, &proof)
                .unwrap()
        );
        assert!(
            !self
                .keys
                .verifier_key()
                .check(
                    committed.commitment(),
                    &self.point,
                    value + bls12_381::Scalar::from(1),
                    &proof
                )
                .unwrap()
        );
        (
            committed.commitment().to_bytes(&self.bounds).unwrap(),
            proof.to_bytes(&self.bounds).unwrap(),
        )
    }
}

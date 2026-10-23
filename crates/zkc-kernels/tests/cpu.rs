//! Scheduling changes numerical phases, never their results or refusal order.
use zkc_kernels::{
    cpu::CpuExecution,
    plonky3::{
        KoalaBear as F,
        polynomial::{Domain, Kernels},
    },
};

#[test]
fn worker_counts_preserve_vectors_transforms_hashes_and_curve_scratch() {
    let values: Vec<_> = (0..8193).map(|i| F::new(i as u32)).collect();
    let coefficients = &values[..1024];
    let domain = Domain::new(2048, F::new(7), 4096).unwrap();
    let states = &values[..8192];
    let compute = |cpu: &CpuExecution| {
        cpu.enter(|| {
            let mut product = vec![F::new(0); values.len()];
            zkc_kernels::vector::mul(&values, &values, &mut product).unwrap();
            let evaluations = Kernels::default().evaluate(coefficients, domain).unwrap();
            let mut hashes = vec![F::new(19)];
            zkc_kernels::plonky3::poseidon2::permute_states(states, &mut hashes).unwrap();
            (product, evaluations, hashes)
        })
    };
    let expected = compute(&CpuExecution::serial().unwrap());
    for workers in [2, 4, 8] {
        assert_eq!(compute(&CpuExecution::new(workers).unwrap()), expected);
    }
    use zkc_kernels::arkworks::{
        bls12_381::{G1, Scalar},
        scaling::{Algorithm, Selection},
    };
    let points: Vec<_> = (0..257)
        .map(|i| {
            if i % 3 == 0 {
                G1::identity()
            } else {
                G1::generator()
            }
        })
        .collect();
    let scalars: Vec<_> = (0..257).map(|i| Scalar::from((i % 5) as u64)).collect();
    let expected: Vec<_> = points
        .iter()
        .zip(&scalars)
        .map(|(p, s)| p.scale(*s))
        .collect();
    for workers in [1, 2, 4] {
        let cpu = CpuExecution::new(workers).unwrap();
        #[cfg(feature = "test-utils")]
        {
            let _failure = zkc_kernels::allocation::failure::after(0);
            let fallback = cpu
                .enter(|| {
                    G1::scaling_plan(
                        points.len(),
                        Selection::Automatic {
                            max_workspace: G1::scaling_workspace_bytes(256).unwrap(),
                        },
                    )
                })
                .unwrap();
            assert_eq!(fallback.algorithm(), Algorithm::Direct);
            assert_eq!(fallback.workspace_bytes(), 0);
        }
        for workspace in [0, G1::scaling_workspace_bytes(256).unwrap()] {
            let mut plan = G1::scaling_plan(
                points.len(),
                Selection::Automatic {
                    max_workspace: workspace,
                },
            )
            .unwrap();
            assert!(plan.workspace_bytes() <= workspace);
            if workspace == 0 {
                assert_eq!(plan.algorithm(), Algorithm::Direct);
            }
            let mut out = vec![G1::generator(); points.len()];
            cpu.enter(|| G1::scale_each_into(&scalars, &points, &mut out, &mut plan))
                .unwrap();
            assert_eq!(out, expected);
            let saved = out.clone();
            assert!(
                cpu.enter(|| G1::scale_each_into(&scalars[..256], &points, &mut out, &mut plan))
                    .is_err()
            );
            assert_eq!(out, saved);
        }
    }
}

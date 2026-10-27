//! Correctness and ambient-pool controls. Private pool creation is checked by
//! the separate `cpu_thread_creation` spawned harness, including exited threads.
use zkc_kernels::{arkworks, cpu::CpuExecution, plonky3};

#[path = "support/cpu_workloads.rs"]
mod cpu_workloads;

#[test]
fn shared_provider_leaves_do_not_initialize_the_ambient_pool() {
    let serial = check_shared_provider_leaves(&CpuExecution::new(1).unwrap());
    let parallel = check_shared_provider_leaves(
        &CpuExecution::new(if cfg!(feature = "parallel") { 4 } else { 1 }).unwrap(),
    );
    assert_eq!(serial, parallel, "worker count changed PCS artifact bytes");
    // This detects ambient registry use only; it cannot detect private pools.
    #[cfg(feature = "parallel")]
    rayon::ThreadPoolBuilder::new()
        .num_threads(1)
        .build_global()
        .expect("an actual numerical leaf escaped its supplied CPU context");
}

fn check_shared_provider_leaves(cpu: &CpuExecution) -> (Vec<u8>, Vec<u8>) {
    let pcs = cpu_workloads::PcsFixture::new(cpu);
    let expected = cpu.enter(|| pcs.check());
    std::thread::scope(|scope| {
        for _ in 0..2 {
            let cpu = cpu.clone();
            let pcs = &pcs;
            let expected = &expected;
            scope.spawn(move || {
                cpu.enter(|| {
                    for _ in 0..2 {
                        cpu_workloads::full_width_msms();
                        assert_eq!(&pcs.check(), expected);
                    }
                    use arkworks::bls12_381::{G1, G2, Scalar};
                    let points = [G1::generator(), G1::generator().neg()];
                    let scalars = [Scalar::from(3), Scalar::from(5)];
                    G1::msm(&scalars, &points).unwrap();
                    assert!(
                        arkworks::bls12_381::pairing_check(&points, &[G2::generator(); 2]).unwrap()
                    );
                    use arkworks::bn254::polynomial::{CoefficientBatch, Domain};
                    let domain = Domain::new(1024, arkworks::bn254::Scalar::from(7)).unwrap();
                    let coefficients = vec![arkworks::bn254::Scalar::from(1); 1024 * 3];
                    let mut scratch = Vec::with_capacity(1024);
                    let mut out = vec![arkworks::bn254::Scalar::from(0); 1024 * 3];
                    CoefficientBatch::new(&coefficients, 3, 1024, 1024)
                        .unwrap()
                        .write_into(domain, &mut scratch, &mut out)
                        .unwrap();
                    let domain =
                        plonky3::polynomial::Domain::new(1024, plonky3::KoalaBear::new(7), 4096)
                            .unwrap();
                    let values = vec![plonky3::KoalaBear::new(3); 1024];
                    plonky3::polynomial::Kernels::default()
                        .evaluate(&values, domain)
                        .unwrap();
                    let shape = plonky3::oracle::Shape::new(8, 128, 4096).unwrap();
                    let (root, tree) = plonky3::merkle::commit::<plonky3::merkle::poseidon2::Base>(
                        values.clone(),
                        shape,
                        1 << 20,
                    )
                    .unwrap();
                    let (rows, proof) = plonky3::merkle::open(&tree, &[1, 17, 99]).unwrap();
                    assert!(
                        plonky3::merkle::verify::<plonky3::merkle::poseidon2::Base>(
                            &root,
                            shape,
                            &[1, 17, 99],
                            &rows,
                            &proof,
                        )
                        .unwrap()
                    );
                    let (root, tree) = plonky3::oracle::commit(values, shape, 1 << 20).unwrap();
                    let (row, path) = tree.open(17).unwrap();
                    plonky3::oracle::verify(root, shape, 17, &row, &path).unwrap();
                })
            });
        }
    });
    expected
}

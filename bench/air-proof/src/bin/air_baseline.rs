//! Direct-kernel timing baseline. Compilation, witness generation and the
//! independent verification warmup are outside measured intervals.
use std::time::Instant;
use zkc_air_kernel_probe::air_argument::{self, Parameters, Proof};
fn bytes(proof: &Proof) -> usize {
    let row = |elements: usize, width: usize, path: usize| elements * width + path * 32;
    let roots = (5 + proof.layers.len()) * 32;
    let scalars = (2 + 12 + 1) * 32;
    roots
        + scalars
        + proof
            .queries
            .iter()
            .map(|q| {
                q.source
                    .iter()
                    .map(|s| {
                        s.main
                            .iter()
                            .map(|r| row(r.values.len(), 4, r.path.len()))
                            .sum::<usize>()
                            + s.aux
                                .iter()
                                .map(|r| row(r.values.len(), 32, r.path.len()))
                                .sum::<usize>()
                            + row(s.quotient.values.len(), 32, s.quotient.path.len())
                    })
                    .sum::<usize>()
                    + q.layers
                        .iter()
                        .flatten()
                        .map(|r| row(r.values.len(), 32, r.path.len()))
                        .sum::<usize>()
            })
            .sum::<usize>()
}
fn main() {
    let sizes: Vec<usize> = std::env::args()
        .skip(1)
        .map(|a| a.parse().expect("trace height"))
        .collect();
    let sizes = if sizes.is_empty() {
        vec![16, 128, 2048, 8192]
    } else {
        sizes
    };
    println!(
        "{{\"format\":\"zkc.air-native-baseline/1\",\"route\":\"direct Rust calls to the same numerical and oracle kernels\",\"blowup\":8,\"queries\":32,\"iterations\":3,\"cases\":["
    );
    for (case, n) in sizes.iter().copied().enumerate() {
        let p = Parameters {
            height: n,
            blowup: 8,
            queries: 32,
        };
        let (s, w) = air_argument::example(n);
        let warm = air_argument::prove(p, s, &w).unwrap();
        air_argument::verify(p, s, &warm).unwrap();
        let payload = bytes(&warm);
        let mut prover = Vec::new();
        let mut verifier = Vec::new();
        for _ in 0..3 {
            let start = Instant::now();
            let proof = air_argument::prove(p, s, &w).unwrap();
            prover.push(start.elapsed().as_secs_f64() * 1000.);
            let start = Instant::now();
            air_argument::verify(p, s, &proof).unwrap();
            verifier.push(start.elapsed().as_secs_f64() * 1000.);
        }
        prover.sort_by(f64::total_cmp);
        verifier.sort_by(f64::total_cmp);
        println!(
            "{}{{\"height\":{},\"prover_ms\":{},\"verifier_ms\":{},\"canonical_payload_bytes_without_framing\":{}}}",
            if case == 0 { "" } else { "," },
            n,
            prover[1],
            verifier[1],
            payload
        );
    }
    println!("]}}");
}

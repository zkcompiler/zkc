//! Synthetic kernel ablation; all test inputs are public, not proof randomness.
use curve25519_dalek::{
    constants::RISTRETTO_BASEPOINT_POINT,
    ristretto::RistrettoPoint,
    scalar::Scalar,
    traits::{Identity, MultiscalarMul, VartimeMultiscalarMul},
};
use std::{hint::black_box, time::Instant};

fn serial(s: &[Scalar], p: &[RistrettoPoint]) -> RistrettoPoint {
    s.iter()
        .zip(p)
        .fold(RistrettoPoint::identity(), |sum, (s, p)| sum + s * p)
}

fn main() {
    let repeats: usize = std::env::args()
        .nth(1)
        .map(|s| s.parse().unwrap())
        .unwrap_or(200);
    let mut rows = Vec::new();
    for n in [0, 1, 2, 4, 8, 16, 32, 64, 128, 256, 1024] {
        let points: Vec<_> = (0..n)
            .map(|i| Scalar::from(i as u64 + 17) * RISTRETTO_BASEPOINT_POINT)
            .collect();
        let scalars: Vec<_> = (0..n)
            .map(|i| {
                let mut bytes = [0u8; 64];
                for (j, b) in bytes.iter_mut().enumerate() {
                    *b = (i * 191 + j * 113 + 37) as u8;
                }
                Scalar::from_bytes_mod_order_wide(&bytes)
            })
            .collect();
        let expected = RistrettoPoint::multiscalar_mul(&scalars, &points);
        assert_eq!(expected, serial(&scalars, &points));
        assert_eq!(
            expected,
            RistrettoPoint::vartime_multiscalar_mul(&scalars, &points)
        );
        let samples = repeats.min(40_000 / (n + 1)).max(10);
        // Rotate order each round to reduce systematic ordering bias.
        for round in 0..5 {
            for mode in (0..3).map(|k| (k + round) % 3) {
                let start = Instant::now();
                for _ in 0..samples {
                    let s = black_box(&scalars);
                    let p = black_box(&points);
                    black_box(match mode {
                        0 => RistrettoPoint::multiscalar_mul(s, p),
                        1 => serial(s, p),
                        _ => RistrettoPoint::vartime_multiscalar_mul(s, p),
                    });
                }
                rows.push(serde_json::json!({"n": n, "round": round, "mode": (["constant-msm", "serial", "public-vartime"][mode]), "samples":samples, "seconds":start.elapsed().as_secs_f64()}));
            }
        }
    }
    println!(
        "{}",
        serde_json::json!({"scope":"synthetic public-input kernel ablation; not whole-protocol timing or a leakage proof", "samples":rows})
    );
}

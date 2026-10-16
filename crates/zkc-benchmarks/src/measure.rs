//! Explicit per-call timing. Input construction and observation are outside the timer.
use crate::Result;
use serde::{Deserialize, Serialize};
use std::{hint::black_box, time::Instant};

#[derive(Clone, Copy, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Plan {
    pub warmups: usize,
    pub samples: usize,
    pub iterations: usize,
}
#[derive(Serialize)]
pub struct Sample {
    pub phase: &'static str,
    pub index: usize,
    pub iterations: usize,
    pub elapsed_ns: u128,
    pub cpu_ns: u128,
    pub first_call_ns: u128,
}
fn cpu_time() -> u128 {
    let now = rustix::time::clock_gettime(rustix::time::ClockId::ProcessCPUTime);
    now.tv_sec as u128 * 1_000_000_000 + now.tv_nsec as u128
}
impl Plan {
    pub fn validate(self) -> Result<()> {
        if self.samples == 0
            || self.iterations == 0
            || self
                .warmups
                .checked_add(self.samples)
                .and_then(|v| v.checked_mul(self.iterations))
                .is_none_or(|v| v > 1_000_000)
        {
            return Err("sample plan must contain 1..1000000 total calls".into());
        }
        Ok(())
    }
}

pub fn measure<I, O>(
    plan: Plan,
    mut prepare: impl FnMut() -> Result<I>,
    mut execute: impl FnMut(I) -> Result<O>,
    mut observe: impl FnMut(O) -> Result<()>,
) -> Result<Vec<Sample>> {
    plan.validate()?;
    let mut samples = Vec::new();
    for index in 0..plan.warmups + plan.samples {
        let mut elapsed_ns = 0;
        let mut cpu_ns = 0;
        let mut first_call_ns = 0;
        for iteration in 0..plan.iterations {
            let input = prepare()?;
            let cpu = cpu_time();
            let start = Instant::now();
            let output = black_box(execute(black_box(input)));
            let elapsed = start.elapsed().as_nanos();
            cpu_ns += cpu_time() - cpu;
            if iteration == 0 {
                first_call_ns = elapsed;
            }
            elapsed_ns += elapsed;
            // A refusal, including a warmup refusal, invalidates the whole worker.
            observe(output?)?;
        }
        samples.push(Sample {
            phase: if index < plan.warmups {
                "warmup"
            } else {
                "sample"
            },
            index,
            iterations: plan.iterations,
            elapsed_ns,
            cpu_ns,
            first_call_ns,
        });
    }
    Ok(samples)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn warmup_failures_are_not_discarded() {
        let plan = Plan {
            warmups: 1,
            samples: 2,
            iterations: 1,
        };
        assert!(
            measure(
                plan,
                || Ok(()),
                |_| Ok(false),
                |ok| if ok { Ok(()) } else { Err("rejected".into()) }
            )
            .is_err()
        );
    }
    #[test]
    fn every_call_is_checked_and_warmups_are_retained() {
        let mut count = 0;
        let samples = measure(
            Plan {
                warmups: 1,
                samples: 2,
                iterations: 3,
            },
            || Ok(()),
            |_| Ok(()),
            |_| {
                count += 1;
                Ok(())
            },
        )
        .unwrap();
        assert_eq!(count, 9);
        assert_eq!(samples[0].phase, "warmup");
        assert_eq!(samples[2].phase, "sample");
        assert!(
            Plan {
                warmups: usize::MAX,
                samples: 1,
                iterations: 1
            }
            .validate()
            .is_err()
        );
    }
    #[test]
    fn known_delay_is_inside_the_wall_timer() {
        let samples = measure(
            Plan {
                warmups: 0,
                samples: 1,
                iterations: 2,
            },
            || Ok(()),
            |_| {
                std::thread::sleep(std::time::Duration::from_millis(2));
                Ok(())
            },
            |_| Ok(()),
        )
        .unwrap();
        assert!(samples[0].elapsed_ns >= 4_000_000);
        assert!(samples[0].first_call_ns >= 2_000_000);
    }
}

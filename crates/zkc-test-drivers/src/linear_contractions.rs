//! Execute compiler-exported shared contractions with the unmodified native Runner.
//! Usage: linear_contractions PROGRAM.json field|group [direct|if|for]
use curve25519_dalek::constants::RISTRETTO_BASEPOINT_POINT;
use zkc_cpu::{CpuBackend, Domain, EntryPolicy, Policy, RistrettoScalar, Scalar, Value};
use zkc_runtime::interpreter::Runner;
use zkc_runtime::vm::{Action, StopKind};

const LEFT: [u64; 4] = [3, 11, 13, 17];
const RIGHT: [u64; 4] = [19, 23, 0, 29];
const FACTORS: [u64; 4] = [2, 0, 5, 7];
const VALUES: [u64; 4] = [31, 37, 41, 43];
const SESSION: &str = "linear_contractions";

fn vector(values: &[u64], group: bool) -> Value {
    if group {
        Value::RistrettoVector(
            values
                .iter()
                .map(|&value| RistrettoScalar::from(value))
                .collect::<Vec<_>>()
                .into(),
        )
    } else {
        Value::Vector(
            values
                .iter()
                .map(|&value| Scalar::from(value))
                .collect::<Vec<_>>()
                .into(),
        )
    }
}

fn runner(bytes: &[u8], group: bool, allowed: bool, short_right: bool) -> Runner<CpuBackend> {
    let native = CpuBackend::new(
        Policy::default(),
        EntryPolicy::new(Domain::new("P", SESSION, "main", None), None),
        Default::default(),
    )
    .unwrap();
    let admitted = zkc_runtime::vm::Program::decode(bytes, zkc_cpu::cpu_contracts())
        .and_then(|program| {
            program.check_installation(&native)?;
            Ok(program)
        })
        .unwrap();
    let values = if group {
        Value::RistrettoGroups(
            VALUES
                .iter()
                .map(|&value| RISTRETTO_BASEPOINT_POINT * RistrettoScalar::from(value))
                .collect::<Vec<_>>()
                .into(),
        )
    } else {
        vector(&VALUES, false)
    };
    let right = if short_right { &RIGHT[..3] } else { &RIGHT[..] };
    Runner::new(
        &admitted,
        "main",
        "P",
        SESSION,
        native,
        vec![
            vector(&LEFT, group),
            vector(right, group),
            vector(&FACTORS, group),
            values,
            Value::Bool(allowed),
        ],
    )
    .map_err(|failure| failure.error)
    .unwrap()
}

fn finish(runner: &mut Runner<CpuBackend>) -> Action<Value> {
    let Action::Local(local) = runner.poll() else {
        panic!("expected the single Work call")
    };
    runner.execute_local(&local.cut).unwrap();
    runner.poll()
}

fn main() {
    let mut arguments = std::env::args().skip(1);
    let bytes = std::fs::read(arguments.next().expect("compiler-exported program")).unwrap();
    let group = match arguments.next().as_deref() {
        Some("field") => false,
        Some("group") => true,
        _ => panic!("expected field or group"),
    };
    let control = arguments.next().unwrap_or_else(|| "direct".into());
    assert!(arguments.next().is_none(), "unexpected argument");

    let mut successful = runner(&bytes, group, true, false);
    let Action::Returned(outputs) = finish(&mut successful) else {
        panic!("expected both contraction results")
    };
    assert_eq!(outputs.len(), 2);
    for (actual, weights) in outputs.iter().zip([LEFT, RIGHT]) {
        // Independent integer arithmetic; no vector kernel or MSM computes the
        // reference. These small coefficients cannot overflow u64 or either field.
        let coefficient: u64 = (0..VALUES.len())
            .map(|i| weights[i] * FACTORS[i] * VALUES[i])
            .sum();
        match actual {
            Value::Field(value) if !group => assert_eq!(*value, Scalar::from(coefficient)),
            Value::RistrettoGroup(value) if group => assert_eq!(
                **value,
                RISTRETTO_BASEPOINT_POINT * RistrettoScalar::from(coefficient)
            ),
            _ => panic!("unexpected contraction result: {actual:?}"),
        }
    }
    // One local call, four operations and the local/participant returns.
    if control == "direct" {
        assert_eq!(successful.usage().instructions, 7);
    } else {
        assert!(successful.usage().instructions > 7);
    }
    assert_eq!(successful.backend().active_frames(), 0);

    // Only the second reduction has mismatched lengths. The false guard must
    // hide that refusal; enabling the guard must expose it at the second site.
    for (allowed, code, instructions) in [
        (false, "rejected:require", 4),
        (true, "refused:length-mismatch", 5),
    ] {
        let mut stopped = runner(&bytes, group, allowed, true);
        let Action::Stopped(stop) = finish(&mut stopped) else {
            panic!("expected stop with {code}")
        };
        assert!(matches!(&stop.kind, StopKind::Backend(error) if error.code == code));
        assert_eq!(stop.role, "P");
        // Direct kernel failures identify the containing local call. Error codes
        // and instruction counts distinguish the guard from the second reduction.
        let site = if control == "direct" {
            "work"
        } else if allowed {
            "lc_6_second"
        } else {
            "lc_7_between"
        };
        assert_eq!(stop.site.as_deref(), Some(site));
        let local = stop.local.as_ref().expect("local failure context");
        assert_eq!(local.site, "work");
        assert!(!local.function.is_empty());
        assert!(stop.cleanup_errors.is_empty());
        assert_eq!(stopped.backend().active_frames(), 0);
        let usage = stopped.usage();
        if control == "direct" {
            assert_eq!(usage.instructions, instructions);
        } else {
            assert!(usage.instructions > instructions);
        }
        assert_eq!(usage.live_values, 0);
        assert_eq!(usage.live_value_bytes, 0);
        assert!(matches!(stopped.poll(), Action::Stopped(again) if again == stop));
        assert_eq!(stopped.usage(), usage);
    }
    println!("shared contractions: arithmetic, guard order and stop cleanup passed");
}

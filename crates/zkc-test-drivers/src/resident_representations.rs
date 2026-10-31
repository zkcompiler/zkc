//! Execute checked compiler fixtures without constructing or rewriting a Program.
//! Usage: resident_representations PROGRAM.json MODE
mod halo2curves_fixture;
use serde_json::{Value as Json, json};
use zkc_cpu::{
    CpuBackend, Domain, EntryPolicy, G1, Policy, Scalar, Sequence, Value, cpu_contracts,
};
use zkc_runtime::{
    interpreter::Runner,
    vm::{Action, PhysicalType, Program, StopKind, Usage, Value as _},
};

const SESSION: &str = "resident_representations";
const SCALAR: &str = "field:bls12-381.fr@blst/fr";
const SEQUENCE: &str = "sequence<field:bls12-381.fr>@logical.sequence/0[blst/fr]";
const NESTED: &str =
    "sequence<sequence<field:bls12-381.fr>>@logical.sequence/0[logical.sequence/0[blst/fr]]";

fn aggregate_runner(program: &Program, inputs: Vec<Value>, policy: Policy) -> Runner<CpuBackend> {
    let native = backend(policy);
    program.check_installation(&native).unwrap();
    Runner::new(program, "main", "P", SESSION, native, inputs)
        .map_err(|failure| failure.error)
        .unwrap()
}

fn canonical_sequence(element: &str, values: Vec<Value>) -> Value {
    let ty = cpu_contracts()
        .physical_type(&format!("sequence<{element}>@logical.sequence/0"))
        .unwrap();
    Value::Sequence(Sequence::new(ty, values, &Policy::default()).unwrap())
}

fn assert_canonical(native: &CpuBackend, value: &Value, expected: &Value, spelling: &str) {
    assert_eq!(value.physical_type().spelling(), spelling);
    let bytes = native.encode_native_value(value).unwrap();
    assert_eq!(bytes, native.encode_native_value(expected).unwrap());
    // The same canonical message decodes directly into either complete layout.
    let decoded = native
        .decode_native_value(&value.physical_type(), &bytes)
        .unwrap();
    assert_eq!(decoded.physical_type(), value.physical_type());
    assert_eq!(native.encode_native_value(&decoded).unwrap(), bytes);
    let default = PhysicalType::default_for(value.physical_type().logical().clone()).unwrap();
    let canonical = native.decode_native_value(&default, &bytes).unwrap();
    assert_eq!(native.encode_native_value(&canonical).unwrap(), bytes);
}

fn aggregate_returned(runner: &mut Runner<CpuBackend>) -> Vec<Value> {
    let Action::Returned(values) = finish(runner) else {
        panic!("expected aggregate result")
    };
    let usage = runner.usage();
    assert_eq!(usage.live_values, values.len());
    assert!(usage.live_value_bytes > 0);
    assert!(usage.total_value_bytes >= usage.live_value_bytes);
    assert!(matches!(runner.poll(), Action::Returned(_)));
    assert_eq!(runner.usage(), usage);
    values
}

fn scalar_inputs() -> [Scalar; 4] {
    [
        Scalar::from(0),
        Scalar::from(1),
        Scalar::from(17),
        -Scalar::from(1),
    ]
}

fn run_sequence(program: &Program) -> (usize, usize) {
    for scalar in scalar_inputs() {
        let mut runner = aggregate_runner(
            program,
            vec![selected(Value::Field(scalar), SCALAR)],
            Policy {
                max_numerical_work: 0,
                ..Policy::default()
            },
        );
        let values = aggregate_returned(&mut runner);
        assert_eq!(values.len(), 1);
        let inner = canonical_sequence("field:bls12-381.fr", vec![Value::Field(scalar)]);
        let expected = canonical_sequence("sequence<field:bls12-381.fr>", vec![inner]);
        assert_canonical(runner.backend(), &values[0], &expected, NESTED);
        let Value::Sequence(outer) = &values[0] else {
            panic!("nested sequence")
        };
        assert_eq!(outer.len(), 1);
        let Value::Sequence(inner) = outer.get(0).unwrap() else {
            panic!("inner sequence")
        };
        assert_eq!(inner.physical_type().spelling(), SEQUENCE);
        assert_eq!(inner.len(), 1);
        assert_canonical(
            runner.backend(),
            inner.get(0).unwrap(),
            &Value::Field(scalar),
            SCALAR,
        );
        assert_eq!(runner.usage().iterations, 0);
    }
    (4, 0)
}

fn run_variant(program: &Program) -> (usize, usize) {
    for scalar in scalar_inputs() {
        let mut runner = aggregate_runner(
            program,
            vec![selected(Value::Field(scalar), SCALAR)],
            Policy {
                max_numerical_work: 0,
                ..Policy::default()
            },
        );
        let values = aggregate_returned(&mut runner);
        assert_eq!(values.len(), 1);
        let expected = canonical_sequence("field:bls12-381.fr", vec![Value::Field(scalar)]);
        assert_canonical(runner.backend(), &values[0], &expected, SEQUENCE);
        assert_eq!(runner.usage().iterations, 0);
    }
    (4, 0)
}

fn run_control(program: &Program, ops: &[&Json]) -> (usize, usize) {
    let mut returned = 0;
    let mut stopped = 0;
    let conversion = conversion_site(ops, "branch_append", 1);
    let guard = operation(ops, "loop_guard")[1].as_str().unwrap();
    for branch in [false, true] {
        // Include a shifted empty interval and enough elements to cross a
        // sequence leaf boundary; length depends on trips, not absolute bounds.
        for (lo, hi) in [(0, 0), (4, 4), (2, 3), (2, 7)] {
            let trips = hi - lo;
            for tight in [false, true] {
                let policy = if tight {
                    Policy {
                        max_numerical_work: 0,
                        ..Policy::default()
                    }
                } else {
                    Policy::default()
                };
                let scalar = -Scalar::from(1);
                let mut runner = aggregate_runner(
                    program,
                    vec![
                        Value::Field(scalar),
                        Value::Bool(branch),
                        Value::Index(lo),
                        Value::Index(hi),
                    ],
                    policy,
                );
                if branch && tight {
                    let usage =
                        stopped_at(&mut runner, "exhausted:numerical-work", Some(conversion));
                    assert_eq!(usage.iterations, 0);
                    assert_eq!(usage.instructions, 5);
                    stopped += 1;
                } else if !branch && trips > 0 {
                    let usage = stopped_at(&mut runner, "rejected:require", Some(guard));
                    assert_eq!(usage.iterations, 1);
                    assert_eq!(usage.instructions, 6);
                    stopped += 1;
                } else {
                    let values = aggregate_returned(&mut runner);
                    assert_eq!(values.len(), 1);
                    let length = usize::try_from(trips + u64::from(branch)).unwrap();
                    let expected = canonical_sequence(
                        "field:bls12-381.fr",
                        vec![Value::Field(scalar); length],
                    );
                    assert_canonical(runner.backend(), &values[0], &expected, SEQUENCE);
                    let Value::Sequence(sequence) = &values[0] else {
                        panic!("control sequence")
                    };
                    assert_eq!(sequence.len(), length);
                    for value in sequence.iter() {
                        assert_canonical(runner.backend(), value, &Value::Field(scalar), SCALAR);
                    }
                    assert_eq!(runner.usage().iterations, trips);
                    assert_eq!(
                        runner.usage().instructions,
                        7 + 3 * u64::from(branch) + 4 * trips
                    );
                    returned += 1;
                }
            }
        }
    }
    (returned, stopped)
}

fn run_dense(program: &Program) -> (usize, usize) {
    let mut returned = 0;
    let mut stopped = 0;
    for elements in [
        vec![Scalar::from(0); 4],
        [2, 3, 5, 7].map(Scalar::from).to_vec(),
        vec![
            -Scalar::from(1),
            Scalar::from(0),
            Scalar::from(17),
            Scalar::from(1),
        ],
        vec![],
        vec![Scalar::from(3); 3],
        vec![Scalar::from(5); 5],
    ] {
        for index in [0, 1, 3, 4, u64::MAX] {
            let input = selected(
                Value::Vector(elements.clone().into()),
                "vector:bls12-381.fr@blst/fr",
            );
            let mut runner =
                aggregate_runner(program, vec![input, Value::Index(index)], Policy::default());
            if elements.len() != 4 {
                let usage = stopped_at(&mut runner, "refused:field-array-length", None);
                assert_eq!(usage.instructions, 2);
                stopped += 1;
            } else if index >= 4 {
                let usage = stopped_at(&mut runner, "refused:field-array-index", None);
                assert_eq!(usage.instructions, 3);
                stopped += 1;
            } else {
                let values = aggregate_returned(&mut runner);
                assert_eq!(values.len(), 1);
                // Canonical Arkworks field arithmetic is independent of the
                // selected dense handlers and their provider storage.
                let dot = elements.iter().fold(Scalar::from(0), |sum, x| sum + *x * x);
                assert_canonical(runner.backend(), &values[0], &Value::Field(dot), SCALAR);
                assert_eq!(runner.usage().iterations, 0);
                returned += 1;
            }
        }
    }
    (returned, stopped)
}

fn backend(policy: Policy) -> CpuBackend {
    CpuBackend::new(
        policy,
        EntryPolicy::new(Domain::new("P", SESSION, "main", None), None),
        Default::default(),
    )
    .unwrap()
}

fn selected(value: Value, spelling: &str) -> Value {
    let encoder = backend(Policy::default());
    let physical = cpu_contracts().physical_type(spelling).unwrap();
    let bytes = encoder.encode_native_value(&value).unwrap();
    encoder.decode_native_value(&physical, &bytes).unwrap()
}

fn runner(
    program: &Program,
    mode: &str,
    branch: bool,
    bounds: (u64, u64),
    allowed: bool,
    policy: Policy,
) -> Runner<CpuBackend> {
    let native = backend(policy);
    program.check_installation(&native).unwrap();
    let mut point = Value::Curve((G1::generator().scale(Scalar::from(7))).into());
    let mut scalar = Value::Field(Scalar::from(3));
    if mode != "ports" {
        point = selected(point, "group:bls12-381.g1@blst/g1");
        scalar = selected(scalar, "field:bls12-381.fr@blst/fr");
    }
    Runner::new(
        program,
        "main",
        "P",
        SESSION,
        native,
        vec![
            point,
            scalar,
            Value::Bool(branch),
            Value::Index(bounds.0),
            Value::Index(bounds.1),
            Value::Bool(allowed),
            Value::Field(Scalar::from(5)),
        ],
    )
    .map_err(|failure| failure.error)
    .unwrap()
}

fn finish(runner: &mut Runner<CpuBackend>) -> Action<Value> {
    let Action::Local(local) = runner.poll() else {
        panic!("expected the compiler-produced Work call")
    };
    runner.execute_local(&local.cut).unwrap();
    let outcome = runner.poll();
    assert_eq!(runner.backend().active_frames(), 0);
    outcome
}

fn returned(runner: &mut Runner<CpuBackend>, mode: &str, branch: bool, trips: u64) {
    let Action::Returned(values) = finish(runner) else {
        panic!("expected resident output: {mode}, branch={branch}, trips={trips}")
    };
    assert_eq!(values.len(), 1);
    assert_eq!(
        values[0].physical_type().spelling(),
        "group:bls12-381.g1@blst/g1"
    );
    // Integer coefficients and Arkworks scalar multiplication are independent of
    // the resident operations and the compiler's branch/backedge selection.
    let mut coefficient = 7 * 3_u64.pow(3);
    if branch {
        coefficient *= if mode == "branch" { 5 } else { 3 };
    }
    coefficient *= (if mode == "loop" { 5_u64 } else { 3_u64 }).pow(trips as u32);
    let expected = Value::Curve((G1::generator().scale(Scalar::from(coefficient))).into());
    assert_eq!(
        runner.backend().encode_native_value(&values[0]).unwrap(),
        runner.backend().encode_native_value(&expected).unwrap()
    );
    let branch_calls = u64::from(branch);
    let conversions = match mode {
        "ports" => 4 + branch_calls + trips,
        "branch" => branch_calls,
        "loop" => trips,
        _ => 0,
    };
    assert_eq!(runner.usage().iterations, trips);
    assert_eq!(
        runner.usage().instructions,
        10 + 2 * branch_calls + 3 * trips + conversions
    );
}

fn stopped(runner: &mut Runner<CpuBackend>, code: &str, site: Option<&str>) {
    let usage = stopped_at(runner, code, site);
    if site.is_none() {
        // Direct operation failures currently name the enclosing local call.
        // Exact instruction counts distinguish the first guard from the first
        // conversion; nested control additionally reports its inner site.
        assert_eq!(
            usage.instructions,
            if code == "rejected:require" { 2 } else { 3 }
        );
    }
}

fn stopped_at(runner: &mut Runner<CpuBackend>, code: &str, site: Option<&str>) -> Usage {
    let Action::Stopped(stop) = finish(runner) else {
        panic!("expected {code} at {site:?}")
    };
    assert!(
        matches!(&stop.kind, StopKind::Backend(error) if error.code == code),
        "{stop:?}"
    );
    assert_eq!(stop.role, "P");
    let local = stop.local.as_ref().expect("local failure context");
    assert_eq!(local.site, "work");
    assert_eq!(local.function, "Work");
    assert_eq!(local.instruction.as_deref(), site);
    assert_eq!(stop.site.as_deref(), Some(site.unwrap_or("work")));
    assert!(stop.cleanup_errors.is_empty());
    let usage = runner.usage();
    assert_eq!(usage.live_values, 0);
    assert_eq!(usage.live_value_bytes, 0);
    assert!(matches!(runner.poll(), Action::Stopped(again) if again == stop));
    assert_eq!(runner.usage(), usage);
    usage
}

fn operations<'a>(value: &'a Json, found: &mut Vec<&'a Json>) {
    if let Some(array) = value.as_array() {
        if array.first().and_then(Json::as_str) == Some("op") {
            found.push(value);
        } else {
            for child in array {
                operations(child, found);
            }
        }
    }
}

fn operation<'a>(ops: &[&'a Json], suffix: &str) -> &'a Json {
    let qualified = format!("_{suffix}");
    ops.iter()
        .copied()
        .find(|op| {
            let site = op[1].as_str().unwrap();
            site == suffix || site.ends_with(&qualified)
        })
        .expect("compiler-produced operation site")
}

fn conversion_site<'a>(ops: &[&'a Json], consumer: &str, operand: usize) -> &'a str {
    let input = &operation(ops, consumer)[4][operand];
    ops.iter()
        .find(|op| op[5][0] == *input)
        .expect("compiler-produced conversion feeding this exact port")[1]
        .as_str()
        .unwrap()
}

fn run_flat(bytes: &[u8], mode: &str) {
    // The Native context supplies installed resident identities. Neither the
    // artifact nor this driver grants variable-time execution permission.
    let program = Program::decode(bytes, cpu_contracts()).unwrap();
    let artifact: Json = serde_json::from_slice(bytes).unwrap();
    let callee = &artifact[3][0][6][0][2];
    let work = artifact[2]
        .as_array()
        .unwrap()
        .iter()
        .find(|function| function[1] == *callee)
        .expect("compiler-produced entry local function");
    let mut ops = Vec::new();
    operations(&work[4], &mut ops);
    let loop_guard = operation(&ops, "loop_guard")[1].as_str().unwrap();
    let tight = Policy {
        max_numerical_work: 0,
        ..Policy::default()
    };
    let mut successes = 0;
    let mut failures = 0;
    for branch in [false, true] {
        for bounds in [(0, 0), (4, 4), (2, 3), (2, 6)] {
            let trips = bounds.1 - bounds.0;
            let mut normal = runner(&program, mode, branch, bounds, true, Policy::default());
            if mode == "loop" && !branch && trips > 0 {
                stopped(&mut normal, "rejected:require", Some(loop_guard));
                failures += 1;
            } else {
                returned(&mut normal, mode, branch, trips);
                successes += 1;
            }
            let mut bounded = runner(&program, mode, branch, bounds, true, tight);
            let conversion = match mode {
                "ports" => Some(conversion_site(&ops, "initial", 0)),
                "branch" if branch => Some(conversion_site(&ops, "left_scale", 1)),
                "loop" if branch && trips > 0 => Some(conversion_site(&ops, "body_scale", 1)),
                _ => None,
            };
            if let Some(site) = conversion {
                stopped(
                    &mut bounded,
                    "exhausted:numerical-work",
                    if mode == "ports" { None } else { Some(site) },
                );
                failures += 1;
            } else if mode == "loop" && !branch && trips > 0 {
                stopped(&mut bounded, "rejected:require", Some(loop_guard));
                failures += 1;
            } else {
                returned(&mut bounded, mode, branch, trips);
                successes += 1;
            }
        }
        let mut guarded = runner(&program, mode, branch, (0, 4), false, tight);
        stopped(&mut guarded, "rejected:require", None);
        failures += 1;
    }
    println!(
        "{}",
        json!({"mode": mode, "returned": successes, "stopped": failures})
    );
}

fn main() {
    let mut arguments = std::env::args().skip(1);
    let bytes = std::fs::read(arguments.next().expect("compiler-produced Program JSON")).unwrap();
    let mode = arguments.next().expect("fixture mode");
    assert!(arguments.next().is_none());
    if let Some(mode) = mode.strip_prefix("halo2curves/") {
        halo2curves_fixture::run(&bytes, mode);
        return;
    }
    if matches!(mode.as_str(), "resident" | "ports" | "branch" | "loop") {
        run_flat(&bytes, &mode);
        return;
    }
    // Read the compiler's artifact without editing it or rebuilding its Program.
    let program = Program::decode(&bytes, cpu_contracts()).unwrap();
    let artifact: Json = serde_json::from_slice(&bytes).unwrap();
    let callee = &artifact[3][0][6][0][2];
    let work = artifact[2]
        .as_array()
        .unwrap()
        .iter()
        .find(|function| function[1] == *callee)
        .unwrap();
    let mut ops = Vec::new();
    operations(&work[4], &mut ops);
    let (returned, stopped) = match mode.as_str() {
        "sequence" => run_sequence(&program),
        "variant" => run_variant(&program),
        "control" => run_control(&program, &ops),
        "dense" => run_dense(&program),
        _ => panic!("unknown fixture mode: {mode}"),
    };
    println!(
        "{}",
        json!({"mode": mode, "returned": returned, "stopped": stopped})
    );
}

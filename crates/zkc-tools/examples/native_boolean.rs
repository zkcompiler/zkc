//! Execute compiler-generated Boolean recipes with the installed native backend.
use std::path::Path;
use zkc_backends::{
    Domain, EntryPolicy, GroupPoint, NativeBackend, Policy, PublicInputs, Scalar, Value,
};
use zkc_runtime::interactive::{Action, ArtifactFormat, Runner, admit_supplied};

fn main() {
    let directory = std::env::args()
        .nth(1)
        .expect("compiler Boolean evidence directory");
    for optimized in [0, 1] {
        let bytes = std::fs::read(Path::new(&directory).join(format!("booleans-{optimized}.json")))
            .unwrap();
        for a in [false, true] {
            for b in [false, true] {
                for c in [false, true] {
                    let backend = NativeBackend::new(
                        Policy::default(),
                        EntryPolicy::new(
                            Domain::new("P", "boolean_test", "main", None),
                            None,
                            PublicInputs::LocalOnly,
                        ),
                        None,
                    )
                    .unwrap();
                    let admitted = admit_supplied(&bytes, &backend).unwrap();
                    assert_eq!(admitted.format(), ArtifactFormat::Program);
                    let group =
                        |n: u64| Value::Curve(GroupPoint::generator().scale(Scalar::from(n)));
                    let mut runner = Runner::new(
                        &admitted,
                        "main",
                        "P",
                        "boolean_test",
                        backend,
                        vec![
                            Value::Bool(a),
                            Value::Bool(b),
                            Value::Bool(c),
                            Value::Field(Scalar::from(11u64)),
                            Value::Field(Scalar::from(23u64)),
                            group(31),
                            group(47),
                        ],
                    )
                    .unwrap_or_else(|_| panic!("entry"));
                    let result = loop {
                        match runner.poll() {
                            Action::Local(local) => runner.execute_local(&local.cut).unwrap(),
                            Action::Returned(values) => break values,
                            other => panic!("unexpected {other:?}"),
                        }
                    };
                    let booleans = [
                        true,
                        false,
                        a && b,
                        a || b,
                        a != b,
                        a == b,
                        a != b,
                        !a,
                        if c { a } else { b },
                    ];
                    assert_eq!(result.len(), 11);
                    for (value, expected) in result.iter().zip(booleans) {
                        assert!(matches!(value, Value::Bool(actual) if *actual == expected));
                    }
                    assert!(
                        matches!(&result[9], Value::Field(actual) if *actual == Scalar::from(if c {11u64} else {23u64}))
                    );
                    assert!(
                        matches!(&result[10], Value::Curve(actual) if *actual == GroupPoint::generator().scale(Scalar::from(if c {31u64} else {47u64})))
                    );
                    assert_eq!(runner.backend().active_frames(), 0);
                    // Terminal results remain retained for stable repeated polling.
                    assert_eq!(runner.usage().live_values, result.len());
                }
            }
        }
    }
    for (name, inputs, expected) in [
        ("literal-only", vec![], false),
        ("folded", vec![Value::Bool(false)], true),
    ] {
        let bytes = std::fs::read(Path::new(&directory).join(format!("{name}.json"))).unwrap();
        let backend = NativeBackend::new(
            Policy::default(),
            EntryPolicy::new(
                Domain::new("P", "boolean_test", "main", None),
                None,
                PublicInputs::LocalOnly,
            ),
            None,
        )
        .unwrap();
        let admitted = admit_supplied(&bytes, &backend).unwrap();
        let mut runner = Runner::new(&admitted, "main", "P", "boolean_test", backend, inputs)
            .unwrap_or_else(|_| panic!("Boolean-only entry"));
        loop {
            match runner.poll() {
                Action::Local(local) => runner.execute_local(&local.cut).unwrap(),
                Action::Returned(values) => {
                    assert!(
                        matches!(values.as_slice(), [Value::Bool(actual)] if *actual == expected)
                    );
                    assert_eq!(runner.backend().active_frames(), 0);
                    break;
                }
                other => panic!("Boolean-only execution: {other:?}"),
            }
        }
    }
    println!("16 native Boolean truth tables, including field/group select, passed");
}

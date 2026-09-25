use super::support::*;
use serde_json::{Value as Json, json};
use zkc_backends::{Policy, Value};
use zkc_runtime::interactive::{Backend, Value as RuntimeValue, admit_supplied};

fn fixture(d: bool, lazy: bool) -> (Json, Vec<Value>) {
    let names = if d {
        ["curve.scale_each", "curve.msm"]
    } else {
        ["vector.mul", "vector.dot"]
    };
    let bindings = names.map(|name| {
        let mut b = binding(d, name);
        if lazy {
            b.implementation = b.implementation.replace('/', "-diagonal/");
        }
        b
    });
    let args = vec![
        vector(d, &[11, 13]),
        vector(d, &[3, 5]),
        if d {
            groups(d, &[2, 4])
        } else {
            vector(d, &[2, 4])
        },
        vector(d, &[17, 19]),
    ];
    let types = args
        .iter()
        .map(RuntimeValue::physical_type)
        .collect::<Vec<_>>();
    let ty = bindings[1].signature().unwrap().outputs[0].clone();
    let bytes = program(
        &bindings,
        &types,
        vec![
            json!(["op", "producer", "b0", [], ["a1", "a2"], ["diag"]]),
            json!(["op", "first", "b1", [], ["a0", "diag"], ["out0"]]),
            json!(["op", "second", "b1", [], ["a3", "diag"], ["out1"]]),
        ],
        &[ty.clone(), ty],
        &["out0".into(), "out1".into()],
    );
    (serde_json::from_slice(&bytes).unwrap(), args)
}
fn run(
    d: bool,
    lazy: bool,
    limit: Option<usize>,
    bad_length: bool,
) -> (Result<Vec<Value>, String>, Controlled) {
    let (j, mut args) = fixture(d, lazy);
    if bad_length {
        args[3] = vector(d, &[1]);
    }
    let mut b = Controlled::new(backend(Policy::default()));
    b.output_limit = limit;
    run_program(b, &serde_json::to_vec(&j).unwrap(), args)
}

#[test]
fn shared_diagonal_has_two_compatible_consumers_and_full_retained_charge() {
    for d in [false, true] {
        let (dense, _) = run(d, false, None, false);
        let (lazy, b) = run(d, true, None, false);
        for (dense, lazy) in dense.unwrap().iter().zip(lazy.unwrap()) {
            assert_value(dense, &lazy);
        }
        assert_eq!(b.outputs.len(), 3); // One producer and both logical consumers execute.
        let view = &b.outputs[0][0];
        let required = if d {
            768 + 2 * (32 + std::mem::size_of::<zkc_backends::RistrettoPoint>())
        } else {
            896
        };
        assert_eq!(view.retained_bytes(), required);
        assert!(!view.physical_type().is_serializable());
        assert_eq!(
            b.inner.encode_value(view).unwrap_err().code,
            "refused:nonserializable"
        );
        // The immutable view remains fully charged after both consumers finish.
        b.inner.validate_value(view).unwrap();
        let (bad, b) = run(d, true, None, true);
        assert_eq!(bad.unwrap_err(), "refused:length-mismatch");
        assert_eq!(b.outputs.len(), 2); // First consumer succeeds, second checks its own shape.
        assert_eq!(b.inner.active_frames(), 0);
    }
}

#[test]
fn dead_internal_views_release_after_all_consumers_without_requiring_a_codec() {
    for d in [false, true] {
        let (base, args) = fixture(d, true);
        let mut released = base.clone();
        released[3][0][4]
            .as_array_mut()
            .unwrap()
            .insert(3, json!(["release", ["diag", "a0", "a1", "a2", "a3"]]));
        let execute = |program: &Json, args| {
            run_program(
                Controlled::new(backend(Policy::default())),
                &serde_json::to_vec(program).unwrap(),
                args,
            )
        };
        let (expected, _) = execute(&base, args.clone());
        let (actual, state) = execute(&released, args.clone());
        for (a, b) in expected.unwrap().iter().zip(actual.unwrap()) {
            assert_value(a, &b);
        }
        assert_eq!(state.outputs.len(), 3);
        assert_eq!(state.inner.active_frames(), 0);
        // Releasing between the two contractions cannot hide the second use.
        let body = released[3][0][4].as_array_mut().unwrap();
        let release = body.remove(3);
        body.insert(2, release);
        assert!(
            admit_supplied(
                &serde_json::to_vec(&released).unwrap(),
                &backend(Policy::default())
            )
            .is_err()
        );
    }
}

#[test]
fn diagonal_memory_limit_is_exact_and_stricter_than_materialization() {
    for d in [false, true] {
        let (_, b) = run(d, false, None, false);
        let dense_charge = b.outputs[0][0].retained_bytes();
        let (_, args) = fixture(d, true);
        let required = args[1].retained_bytes() + args[2].retained_bytes() + 256;
        assert!(required > dense_charge);
        for limit in [dense_charge, required - 1] {
            let (result, b) = run(d, true, Some(limit), false);
            assert_eq!(result.unwrap_err(), "exhausted:output-bytes");
            assert!(b.outputs.is_empty());
        }
        let (result, b) = run(d, true, Some(required), false);
        assert!(result.is_ok());
        assert_eq!(b.outputs[0][0].retained_bytes(), required);
    }
}

#[test]
fn every_diagonal_use_and_all_function_boundaries_are_checked() {
    for d in [false, true] {
        let (base, _) = fixture(d, true);
        let check = |j: Json| {
            assert!(
                admit_supplied(
                    &serde_json::to_vec(&j).unwrap(),
                    &backend(Policy::default())
                )
                .is_err(),
                "{j}"
            )
        };
        // A valid first use must never mask a later incompatible use.
        let mut j = base.clone();
        j[3][0][4][2][4] = json!(["diag", "diag"]); // weights and values in the same op
        check(j);
        let mut j = base.clone();
        j[3][0][4][2][4] = json!(["diag", "a3"]); // weights slot
        check(j);
        let mut j = base.clone();
        j[1][1][3] = json!(if d {
            "dalek/curve.msm"
        } else {
            "arkworks/vector.dot"
        });
        check(j); // dense consumer of a view
        let mut j = base.clone();
        j[3][0][4][2] = json!(["op", "nested", "b0", [], ["a1", "diag"], ["out1"]]);
        check(j); // depth two
        let mut j = base.clone();
        j[1][1][2] = json!([if d {
            "bls12-381.g1"
        } else {
            "ristretto255.scalar"
        }]);
        check(j); // nominal cast through a consumer declaration
        let mut j = base.clone();
        let view = if d {
            "groups:ristretto255.group@dalek.ristretto-diagonal/1"
        } else {
            "vector:bls12-381.fr@arkworks.fr-diagonal/1"
        };
        j[3][0][3] = json!([view]);
        j[3][0][4][3] = json!(["return", ["diag"]]);
        check(j); // user-authored returned view, even after good consumers
        let mut j = base.clone();
        j[3][0][2][2][1] = json!(view);
        check(j); // function ingress
        let mut j = base.clone();
        j[4][0][5][2][1] = json!(view);
        check(j); // participant ingress
        let mut j = base.clone();
        j[3][0][4][1][4][1] = json!("a2");
        j[3][0][4][2][4][1] = json!("a2");
        j[1][1][3] = json!(if d {
            "dalek/curve.msm"
        } else {
            "arkworks/vector.dot"
        });
        check(j); // unused diagonal producer
    }
}

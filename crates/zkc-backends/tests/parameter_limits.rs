//! Ordered index parameters have their own admission budget; vector shape is
//! still checked against the actual input by the backend.
#[path = "domains/support.rs"]
mod support;

use serde_json::{Value as Json, json};
use support::*;
use zkc_backends::Policy;
use zkc_runtime::interactive::{ErrorCode, Limits, admit_supplied};

fn gather(d: bool, indices: &[String]) -> Vec<u8> {
    let op = binding(d, "vector.gather");
    let sig = op.signature().unwrap();
    program(
        &[op],
        &sig.inputs,
        vec![json!(["op", "gather", "b0", indices, ["a0"], ["out"]])],
        &sig.outputs,
        &["out".into()],
    )
}

#[test]
fn large_gather_keeps_order_repetition_and_dynamic_bounds() {
    for d in [false, true] {
        for count in [0, 1024, 1025, 2048, 4096, Limits::OPERATION_ATTRIBUTES] {
            let indices = (0..count)
                .map(|i| ((i * 7 + 2) % 3).to_string())
                .collect::<Vec<_>>();
            let bytes = gather(d, &indices);
            let (result, _) = run_program(
                backend(Policy::default()),
                &bytes,
                vec![vector(d, &[11, 22, 33])],
            );
            let expected = indices
                .iter()
                .map(|i| [11, 22, 33][i.parse::<usize>().unwrap()])
                .collect::<Vec<_>>();
            assert_value(&result.unwrap()[0], &vector(d, &expected));
        }
        let mut indices = vec!["0".into(); 2048];
        indices[2047] = "3".into();
        let (result, _) = run_program(
            backend(Policy::default()),
            &gather(d, &indices),
            vec![vector(d, &[11, 22, 33])],
        );
        assert_eq!(result.unwrap_err(), "refused:vector-index");
    }
}

#[test]
fn parameter_budget_does_not_relax_naturals_ports_or_kernel_arity() {
    let b = backend(Policy::default());
    assert_eq!(
        admit_supplied(
            &gather(false, &vec!["0".into(); Limits::OPERATION_ATTRIBUTES + 1]),
            &b
        )
        .unwrap_err()
        .code,
        ErrorCode::Limit
    );
    for bad in ["01", "+1", "-1", "18446744073709551616", ""] {
        let mut indices = vec!["0".into(); 2048];
        indices[2047] = bad.into();
        assert_eq!(
            admit_supplied(&gather(false, &indices), &b)
                .unwrap_err()
                .code,
            ErrorCode::Attributes
        );
    }
    let original: Json = serde_json::from_slice(&gather(false, &["0".into()])).unwrap();
    for slot in [4, 5] {
        let mut bad = original.clone();
        bad[3][0][4][0][slot] = json!(vec!["a0"; Limits::PORTS + 1]);
        assert_eq!(
            admit_supplied(&serde_json::to_vec(&bad).unwrap(), &b)
                .unwrap_err()
                .code,
            ErrorCode::Limit
        );
    }
    for attrs in [
        json!(["1", "1"]),
        json!(["1", "1", "2"]),
        json!(["1", "1", "0", "0"]),
    ] {
        let mut bad = original.clone();
        bad[1][0][1] = json!("vector.matvec");
        bad[1][0][3] = json!("arkworks/vector.matvec");
        bad[3][0][4][0][3] = attrs;
        bad[3][0][4][0][4] = json!(["a0", "a0"]);
        assert_eq!(
            admit_supplied(&serde_json::to_vec(&bad).unwrap(), &b)
                .unwrap_err()
                .code,
            ErrorCode::Attributes
        );
    }
    let mut bad = original;
    bad[3][0][4][0][3] = json!([[]]);
    assert_eq!(
        admit_supplied(&serde_json::to_vec(&bad).unwrap(), &b)
            .unwrap_err()
            .code,
        ErrorCode::Record
    );
}

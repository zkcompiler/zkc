//! Data-driven relation programs through the general independent proof host.
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::path::Path;
use zkc_backends::{Domain, EntryPolicy, NativeBackend, Policy, Scalar, Sequence, Value, Variant};
use zkc_runtime::interactive::LogicalType;
use zkc_tools::proof::{NativeDeployment, hex};

fn backend() -> NativeBackend {
    NativeBackend::new(
        Policy::default(),
        EntryPolicy::new(Domain::new("P", "relations", "main", None), None),
        Default::default(),
    )
    .unwrap()
}
fn vector(values: &[u64]) -> Value {
    Value::Vector(
        values
            .iter()
            .copied()
            .map(Scalar::from)
            .collect::<Vec<_>>()
            .into(),
    )
}
fn sequence(element: &str, values: Vec<Value>) -> Value {
    Value::Sequence(
        Sequence::new(
            LogicalType::parse(element).unwrap(),
            values,
            &Policy::default(),
        )
        .unwrap(),
    )
}
fn r1cs(rows: usize, change: &str) -> Vec<Value> {
    let columns = if rows >= 17 { 17 } else { 3 };
    let matrices = (0..if change == "arity" { 2 } else { 3 })
        .map(|matrix| {
            let entries = (0..rows)
                .map(|row| {
                    let coefficient = if matrix == 1 { 1 } else { row as u64 + 1 };
                    let coefficient = if matrix == 0
                        && ((change == "configuration" && row == 0)
                            || (change == "last_constraint" && row + 1 == rows))
                    {
                        coefficient + 1
                    } else {
                        coefficient
                    };
                    (
                        row as u32,
                        if matrix == 2 { 1 } else { columns as u32 - 1 },
                        Scalar::from(coefficient),
                    )
                })
                .collect::<Vec<_>>();
            Value::matrix(
                rows + usize::from(change == "row_count" && matrix == 1),
                if change == "shape" && matrix == 1 {
                    columns + 1
                } else {
                    columns
                },
                &entries,
                &Policy::default(),
            )
            .unwrap()
        })
        .collect();
    vec![
        sequence("matrix:bls12-381.fr", matrices),
        vector(&[if change == "public" { 10 } else { 9 }]),
        {
            let mut assignment = vec![0; columns];
            assignment[0] = if change == "one" { 2 } else { 1 };
            assignment[1] = 9;
            assignment[columns - 1] = if change == "witness" { 4 } else { 3 };
            if change == "empty" {
                assignment.clear();
            }
            vector(&assignment)
        },
    ]
}
fn air(ty: &LogicalType, height: usize, change: &str) -> Vec<Value> {
    let descriptor = ty.variant_descriptor().unwrap().clone();
    let config = Value::Variant(
        Variant::new(
            descriptor,
            0,
            vec![
                Value::Field(Scalar::from(if change == "configuration" { 2 } else { 1 })),
                Value::Field(Scalar::from(1)),
            ],
        )
        .unwrap(),
    );
    let (mut x, mut y) = (Scalar::from(1), Scalar::from(2));
    let mut rows = Vec::new();
    for row in 0..height {
        let values = if change == "width" && row == 1 {
            vec![x, y, Scalar::from(0)]
        } else {
            vec![
                x,
                y + Scalar::from(u64::from(change == "witness" && row == 1)),
            ]
        };
        rows.push(Value::Vector(values.into()));
        if row + 1 < height {
            (x, y) = (y, x + y);
        }
    }
    vec![
        config,
        Value::Vector(
            vec![
                Scalar::from(1),
                Scalar::from(2),
                x,
                y + Scalar::from(u64::from(change == "public")),
            ]
            .into(),
        ),
        sequence("vector:bls12-381.fr", rows),
    ]
}
// Independent small reference checks operate on actual host values. They use
// direct sums and adjacent rows, without the interpreter's operation dispatch.
fn reference(family: &str, values: &[Value]) -> bool {
    let Value::Vector(public) = &values[1] else {
        panic!("public vector")
    };
    if family == "r1cs" {
        let Value::Sequence(matrices) = &values[0] else {
            panic!("matrices")
        };
        let Value::Vector(z) = &values[2] else {
            panic!("assignment")
        };
        if matrices.elements().len() != 3
            || z.len() <= public.len()
            || z[0] != Scalar::from(1)
            || z[1..=public.len()] != **public
        {
            return false;
        }
        let mut products = Vec::new();
        for matrix in matrices.elements() {
            let Value::Matrix(matrix) = matrix else {
                panic!("matrix")
            };
            if matrix.columns() != z.len() {
                return false;
            }
            let mut product = vec![Scalar::from(0); matrix.rows()];
            for (row, column, coefficient) in matrix.entries() {
                product[*row as usize] += *coefficient * z[*column as usize];
            }
            products.push(product);
        }
        products[0].len() == products[1].len()
            && products[0].len() == products[2].len()
            && (0..products[0].len()).all(|i| products[0][i] * products[1][i] == products[2][i])
    } else {
        let Value::Variant(config) = &values[0] else {
            panic!("configuration")
        };
        let [Value::Field(a), Value::Field(b)] = config.payload() else {
            panic!("coefficients")
        };
        let Value::Sequence(trace) = &values[2] else {
            panic!("trace")
        };
        let rows: Vec<_> = trace
            .elements()
            .iter()
            .map(|row| {
                let Value::Vector(row) = row else {
                    panic!("row")
                };
                row
            })
            .collect();
        if public.len() != 4 || rows.is_empty() || rows.iter().any(|row| row.len() != 2) {
            return false;
        }
        rows[0][..] == public[..2]
            && rows.last().unwrap()[..] == public[2..]
            && rows.windows(2).all(|pair| {
                pair[1][0] == pair[0][1] && pair[1][1] == *a * pair[0][0] + *b * pair[0][1]
            })
    }
}

fn inputs(envelope: &Json, values: &[Value], producing: bool) -> Json {
    let codec = backend();
    let wire = |i: &Json| {
        hex(&codec
            .encode_native_value(&values[i.as_str().unwrap().parse::<usize>().unwrap()])
            .unwrap())
    };
    let public = envelope[2][4]
        .as_array()
        .unwrap()
        .iter()
        .map(|p| json!([p[0], p[1], wire(&p[1])]))
        .collect::<Vec<_>>();
    let role_name = &envelope[2][1][if producing { 2 } else { 3 }];
    let role = envelope[6]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row[0] == *role_name)
        .unwrap();
    let ports = role[2]
        .as_array()
        .unwrap()
        .iter()
        .map(|p| json!([p[0], ["wire", wire(&p[0])]]))
        .collect::<Vec<_>>();
    let draws = if envelope[2][1][5] == "" { "0" } else { "32" };
    json!(["zkc.native-proof-inputs", public, ports, "", [], draws])
}
fn execute(
    deployment: &NativeDeployment,
    input: &Json,
    proof: Option<&[u8]>,
) -> Result<Vec<u8>, String> {
    let report = deployment.execute(input, proof)?;
    assert!(!report.outcome.as_ref().err().is_some_and(
        |e| e.starts_with("native-proof-cleanup") || e == "native-proof-active-frames"
    ));
    report.outcome
}
fn ordered(values: Vec<Value>, case: &Json) -> Vec<Value> {
    case.get("order").map_or_else(
        || values.clone(),
        |order| {
            order
                .as_array()
                .unwrap()
                .iter()
                .map(|i| values[i.as_u64().unwrap() as usize].clone())
                .collect()
        },
    )
}
fn main() {
    let directory = std::env::args().nth(1).expect("generated directory");
    let directory = Path::new(&directory);
    let manifest: Json =
        serde_json::from_slice(&std::fs::read(directory.join("manifest.json")).unwrap()).unwrap();
    for case in manifest.as_array().unwrap() {
        let name = case["name"].as_str().unwrap();
        let family = case["family"].as_str().unwrap();
        let bytes = std::fs::read(directory.join(format!("{name}.deployment"))).unwrap();
        let envelope: Json = serde_json::from_slice(&bytes).unwrap();
        let deployment =
            NativeDeployment::admit(&bytes, &Sha256::digest(&bytes).into(), Default::default())
                .unwrap();
        let config_type = LogicalType::parse(envelope[2][4][0][2].as_str().unwrap()).unwrap();
        let data = |n, change| {
            let values = if family == "r1cs" {
                r1cs(n, change)
            } else {
                air(&config_type, n, change)
            };
            assert_eq!(
                reference(family, &values),
                change == "valid" && (family == "r1cs" || n > 0)
            );
            ordered(values, case)
        };
        for size in if family == "r1cs" {
            [0, 1, 3, 17, 128]
        } else {
            [1, 2, 3, 17, 128]
        } {
            let values = data(size, "valid");
            let p = inputs(&envelope, &values, true);
            let v = inputs(&envelope, &values, false);
            let proof = execute(&deployment, &p, None)
                .unwrap_or_else(|e| panic!("{name}/{size} produce: {e}"));
            execute(&deployment, &v, Some(&proof))
                .unwrap_or_else(|e| panic!("{name}/{size} validate: {e}"));
            if size == 3 {
                for (suffix, input) in [("producer", &p), ("validator", &v)] {
                    std::fs::write(
                        directory.join(format!("{name}.{suffix}.json")),
                        serde_json::to_vec(input).unwrap(),
                    )
                    .unwrap();
                }
                std::fs::write(directory.join(format!("{name}.proof")), &proof).unwrap();
                let mut changes = vec!["configuration", "public", "witness"];
                if family == "r1cs" {
                    changes.push("last_constraint");
                }
                for change in changes {
                    let bad = data(size, change);
                    let bp = inputs(&envelope, &bad, true);
                    let bv = inputs(&envelope, &bad, false);
                    let bad_proof = execute(&deployment, &bp, None).unwrap();
                    let error = execute(&deployment, &bv, Some(&bad_proof)).unwrap_err();
                    assert_eq!(error, "artifact-rejected", "{name}/{change}: {error}");
                    if change != "witness" {
                        assert!(
                            execute(&deployment, &bv, Some(&proof)).is_err(),
                            "old proof accepted under changed public root"
                        );
                        let mut mismatched = v.clone();
                        mismatched[2] = bv[2].clone();
                        assert_eq!(
                            execute(&deployment, &mismatched, Some(&proof)).unwrap_err(),
                            "native-proof-shared-public-input"
                        );
                    }
                }
                let mut truncated = proof.clone();
                truncated.pop();
                assert!(execute(&deployment, &v, Some(&truncated)).is_err());
                let mut trailing = proof.clone();
                trailing.push(0);
                assert!(execute(&deployment, &v, Some(&trailing)).is_err());
            }
        }
        for change in if family == "r1cs" {
            vec!["one", "arity", "shape", "row_count", "empty"]
        } else {
            vec!["width"]
        } {
            let values = data(3, change);
            let p = inputs(&envelope, &values, true);
            let v = inputs(&envelope, &values, false);
            let proof = execute(&deployment, &p, None).unwrap();
            let expected = if change == "one" {
                "artifact-rejected"
            } else {
                "artifact-stopped:Explicit(\"reject\")"
            };
            assert_eq!(
                execute(&deployment, &v, Some(&proof)).unwrap_err(),
                expected,
                "{name}/{change}"
            );
        }
        if family == "air" {
            let values = data(0, "valid");
            let proof = execute(&deployment, &inputs(&envelope, &values, true), None).unwrap();
            assert_eq!(
                execute(
                    &deployment,
                    &inputs(&envelope, &values, false),
                    Some(&proof)
                )
                .unwrap_err(),
                "artifact-stopped:Explicit(\"reject\")"
            );
        }
    }
}

//! The importer rechecks a candidate export instead of trusting its producer,
//! binds it only to an instance that selects its identity, and refuses changed
//! heights, missing data and noncanonical encodings. Self-consistent but wrong
//! exports are caught by comparison with the same pinned AIR.

mod common;

use common::*;
use p3_field::{PrimeCharacteristicRing, PrimeField32};
use p3_matrix::Matrix;
use p3_matrix::dense::RowMajorMatrix;
use serde_json::{Value, json};
use zkc_plonky3_air::arena::Node;
use zkc_plonky3_air::artifact::canonical;
use zkc_plonky3_air::field::{F, MODULUS};
use zkc_plonky3_air::reference::{upstream_accepts, upstream_failures};
use zkc_plonky3_air::view::{SelectorLaw, violations};
use zkc_plonky3_air::{ClosedView, Export, Instance, Slot, Witness};
use zkc_plonky3_air_client::RecurrenceAir;

const HEIGHT: usize = 8;

fn setup() -> (RecurrenceAir, Export, RowMajorMatrix<F>, Vec<F>) {
    let air = RecurrenceAir { log_height: 3 };
    let export = zkc_plonky3_air::export(&air, "recurrence").unwrap();
    let (trace, publics) = air.generate(F::from_u32(2), F::from_u32(5));
    (air, export, trace, publics)
}

fn refused(text: String) -> &'static str {
    Export::parse(&text).expect_err("import must refuse").id
}

/// Violations of an imported export on a trace, with an instance selecting it.
fn imported_violations(
    text: &str,
    trace: &RowMajorMatrix<F>,
    publics: &[F],
) -> Vec<(usize, usize)> {
    let export = Export::parse(text).unwrap();
    let view = bind(&export, HEIGHT, publics);
    violations(
        &view.residuals(&view.row_inputs(trace, SelectorLaw::RowIndicator).unwrap()),
        export.assertions.len(),
    )
}

#[test]
fn stale_identities_and_inconsistent_derived_facts_refuse() {
    let (_, export, _, _) = setup();
    let original = export_value(&export);

    let mut v = original.clone();
    v["arena"][2][25][2] = json!("123456790");
    assert_eq!(refused(canonical(&v)), "plonky3-arena-identity");

    let mut v = original.clone();
    v["layout"]["preprocessed"]["values"][3] = json!("34");
    assert_eq!(refused(canonical(&v)), "plonky3-preprocessed-identity");

    // Arena formation precedes identity: other field sorts are outside this view.
    let mut v = original.clone();
    v["arena"][1][0] = json!("koala-bear.ext8-binomial3");
    assert_eq!(refused(canonical(&v)), "plonky3-arena-field");

    let mut v = original.clone();
    v["features"].as_array_mut().unwrap().retain(|f| f != "sub");
    assert_eq!(refused(canonical(&v)), "plonky3-feature-inventory");

    let mut v = original.clone();
    let sub = v["node_origins"]
        .as_array()
        .unwrap()
        .iter()
        .position(|o| o == "sub")
        .unwrap();
    v["node_origins"][sub] = json!("add");
    assert_eq!(refused(canonical(&v)), "plonky3-node-map");

    let mut v = original.clone();
    v["assertions"][1]["constraint"] = json!(2);
    assert_eq!(refused(canonical(&v)), "plonky3-assertion");
    let mut v = original.clone();
    v["assertions"][4]["degree_multiple"] = json!(2);
    assert_eq!(refused(canonical(&v)), "plonky3-assertion");
    let mut v = original.clone();
    v["assertions"][4]["selectors"] = json!(["first-row"]);
    assert_eq!(refused(canonical(&v)), "plonky3-assertion");
}

#[test]
fn layout_slot_and_feature_mutations_refuse() {
    let (_, export, _, _) = setup();
    let original = export_value(&export);
    type Mutation = Box<dyn Fn(&mut Value)>;
    let cases: Vec<(Mutation, &str)> = vec![
        (
            Box::new(|v| v["read_model"] = json!("finite")),
            "plonky3-artifact-schema",
        ),
        (
            Box::new(|v| v["selector_semantics"] = json!("scoped")),
            "plonky3-artifact-schema",
        ),
        (
            Box::new(|v| v["upstream"]["commit"] = json!("0".repeat(40))),
            "plonky3-artifact-schema",
        ),
        (
            Box::new(|v| v["upstream"]["crates"]["p3-air"] = json!("0.8.0")),
            "plonky3-artifact-schema",
        ),
        (
            Box::new(|v| {
                v["probed_absent"]
                    .as_array_mut()
                    .unwrap()
                    .pop()
                    .map(|_| ())
                    .unwrap()
            }),
            "plonky3-artifact-schema",
        ),
        (
            Box::new(|v| {
                v["extra"] = json!(1);
            }),
            "plonky3-artifact-schema",
        ),
        (
            Box::new(|v| {
                v.as_object_mut().unwrap().remove("features");
            }),
            "plonky3-artifact-schema",
        ),
        (
            Box::new(|v| v["slots"][1] = json!(["main", 9, 0])),
            "plonky3-slot",
        ),
        (
            Box::new(|v| v["slots"][8] = json!(["public", 7])),
            "plonky3-slot",
        ),
        (
            Box::new(|v| v["slots"][0] = json!(["main", 1, 0])),
            "plonky3-slot",
        ),
        (
            Box::new(|v| v["layout"]["main"]["next_row_columns"] = json!([1, 2, 3])),
            "plonky3-next-row-metadata",
        ),
        (
            Box::new(|v| v["layout"]["main"]["next_row_columns"] = json!([0, 1, 2, 3, 4])),
            "plonky3-next-row-metadata",
        ),
        (
            Box::new(|v| v["layout"]["main"]["width"] = json!(3)),
            "plonky3-next-row-metadata",
        ),
        (
            Box::new(|v| v["layout"]["preprocessed"] = Value::Null),
            "plonky3-slot",
        ),
        (
            Box::new(|v| v["layout"]["preprocessed"]["height"] = json!(6)),
            "plonky3-preprocessed-shape",
        ),
        (
            Box::new(|v| v["layout"]["public_values"] = json!(2)),
            "plonky3-slot",
        ),
        (
            Box::new(|v| {
                v["arena"][1]
                    .as_array_mut()
                    .unwrap()
                    .push(json!("koala-bear"))
            }),
            "plonky3-slot",
        ),
    ];
    for (i, (mutate, id)) in cases.into_iter().enumerate() {
        let mut v = original.clone();
        mutate(&mut v);
        assert_eq!(refused(redigest(v)), id, "case {i}");
    }
}

#[test]
fn breaking_a_guard_in_the_artifact_refuses_on_import() {
    let (_, export, _, _) = setup();
    let mut v = export_value(&export);
    // Assertion 1 is `first_row * (x - x0)`; turn its product into a sum.
    let root = export.arena.outputs()[1];
    let Node::Mul(a, b) = export.arena.nodes()[root] else {
        panic!("guarded assertion")
    };
    v["arena"][2][root] = json!(["add", a, b]);
    v["node_origins"][root] = json!("add");
    assert_eq!(refused(redigest(v)), "plonky3-selector-not-guard");
}

#[test]
fn noncanonical_text_refuses() {
    let (_, export, _, _) = setup();
    let text = export.to_text();
    assert_eq!(Export::parse(&text).unwrap(), export);
    for mutated in [
        text.replacen("  \"air\": ", "  \"air\":", 1),
        text.replace("\n}\n", "\n}"),
        text.replacen('\n', "\n\n", 1),
        format!("{text} "),
    ] {
        assert_eq!(
            Export::parse(&mutated).unwrap_err().id,
            "plonky3-artifact-noncanonical"
        );
    }
    assert_eq!(
        Export::parse("{").unwrap_err().id,
        "plonky3-artifact-schema"
    );
}

#[test]
fn self_consistent_wrong_exports_are_caught_against_the_same_air() {
    let (air, export, trace, publics) = setup();
    assert!(upstream_accepts(&air, &trace, &publics));
    assert!(imported_violations(&export.to_text(), &trace, &publics).is_empty());

    // An exporter that wrote the internal Montgomery residue of the constant.
    let montgomery = ((zkc_plonky3_air_client::STEP_CONSTANT as u64) << 32) % MODULUS as u64;
    let constant = export
        .arena
        .nodes()
        .iter()
        .position(|n| matches!(n, Node::Constant(_)))
        .unwrap();
    let mut v = export_value(&export);
    v["arena"][2][constant][2] = json!(montgomery.to_string());
    let found = imported_violations(&redigest(v), &trace, &publics);
    assert_eq!(
        found,
        (0..HEIGHT - 1).map(|row| (row, 5)).collect::<Vec<_>>()
    );

    // An exporter that bound `x' - x` instead of `x' - y`.
    let x = input_node(
        &export,
        Slot::Main {
            offset: 0,
            column: 0,
        },
    );
    let root = export.arena.outputs()[4];
    let Node::Mul(_, sub) = export.arena.nodes()[root] else {
        panic!("guarded assertion")
    };
    let Node::Add(_, negation) = export.arena.nodes()[sub] else {
        panic!("subtraction")
    };
    let mut v = export_value(&export);
    v["arena"][2][negation] = json!(["neg", x]);
    let found = imported_violations(&redigest(v), &trace, &publics);
    assert!(
        !found.is_empty() && found.iter().all(|(_, c)| *c == 4),
        "{found:?}"
    );

    // A changed fixed column is a different relation with a different identity.
    let mut v = export_value(&export);
    v["layout"]["preprocessed"]["values"][3] = json!("34");
    let text = redigest(v);
    let changed = Export::parse(&text).unwrap();
    assert_ne!(changed.sha256(), export.sha256());
    let stale = Instance {
        export_sha256: export.sha256(),
        height: HEIGHT,
        public_values: publics.clone(),
    };
    assert_eq!(
        ClosedView::bind(&changed, &stale).unwrap_err().id,
        "plonky3-export-identity"
    );
    assert_eq!(
        imported_violations(&text, &trace, &publics),
        [(3, 5), (3, 6)]
    );
    assert!(upstream_failures(&air, &trace, &publics).is_empty());
}

#[test]
fn instances_bind_one_export_height_and_statement() {
    let (_, export, trace, publics) = setup();
    let good = instance(&export, HEIGHT, &publics);
    assert_eq!(Instance::parse(&good.to_text()).unwrap(), good);
    let view = ClosedView::bind(&export, &good).unwrap();
    assert!(view.row_inputs(&trace, SelectorLaw::RowIndicator).is_ok());
    let cases = [
        (
            Instance {
                height: 0,
                ..good.clone()
            },
            "plonky3-height",
        ),
        (
            Instance {
                height: 6,
                ..good.clone()
            },
            "plonky3-height",
        ),
        (
            Instance {
                height: 16,
                ..good.clone()
            },
            "plonky3-height",
        ),
        (
            Instance {
                public_values: publics[..2].to_vec(),
                ..good.clone()
            },
            "plonky3-public-values",
        ),
        (
            Instance {
                public_values: [publics.clone(), vec![F::ONE]].concat(),
                ..good.clone()
            },
            "plonky3-public-values",
        ),
        (
            Instance {
                export_sha256: "0".repeat(64),
                ..good.clone()
            },
            "plonky3-export-identity",
        ),
    ];
    for (instance, id) in cases {
        assert_eq!(
            ClosedView::bind(&export, &instance).unwrap_err().id,
            id,
            "{instance:?}"
        );
    }
    // A wrong public value binds, then fails exactly where the statement is used.
    let mut wrong = publics.clone();
    wrong[2] += F::ONE;
    let view = bind(&export, HEIGHT, &wrong);
    assert_eq!(
        violations(
            &view.residuals(&view.row_inputs(&trace, SelectorLaw::RowIndicator).unwrap()),
            9
        ),
        [(7, 7)]
    );
    let text = good.to_text();
    for mutated in [
        text.replace("\"height\": 8", "\"height\": 8.0"),
        text.replace("\"5\"", "\"05\""),
        text.replace("\"5\"", "\"2130706438\""),
        text.replace("\"format\"", "\"extra\": 1,\n  \"format\""),
    ] {
        assert!(Instance::parse(&mutated).is_err(), "{mutated}");
    }
}

#[test]
fn witnesses_must_match_the_declared_table() {
    let (_, export, trace, publics) = setup();
    let view = bind(&export, HEIGHT, &publics);
    let witness = Witness {
        trace: trace.clone(),
    };
    assert_eq!(Witness::parse(&witness.to_text()).unwrap(), witness);
    let narrow = RowMajorMatrix::new(
        trace
            .values
            .iter()
            .enumerate()
            .filter(|(i, _)| i % 4 != 3)
            .map(|(_, v)| *v)
            .collect(),
        3,
    );
    assert_eq!(
        view.row_inputs(&narrow, SelectorLaw::RowIndicator)
            .unwrap_err()
            .id,
        "plonky3-trace-width"
    );
    let short = RowMajorMatrix::new(trace.values[..4 * 4].to_vec(), 4);
    assert_eq!(
        view.row_inputs(&short, SelectorLaw::RowIndicator)
            .unwrap_err()
            .id,
        "plonky3-height"
    );
    assert_eq!(
        view.coefficient_inputs(&short).unwrap_err().id,
        "plonky3-height"
    );
    let text = witness.to_text();
    let first = trace.values[0].as_canonical_u32().to_string();
    for (mutated, id) in [
        (
            text.replacen(&format!("\"{first}\""), "\"02\"", 1),
            "plonky3-noncanonical-scalar",
        ),
        (
            text.replacen(&format!("\"{first}\""), &format!("\"{}\"", MODULUS), 1),
            "plonky3-noncanonical-scalar",
        ),
        (
            text.replace("\"height\": 8", "\"height\": 7"),
            "plonky3-artifact-schema",
        ),
        (
            text.replace("\"width\": 4", "\"width\": 5"),
            "plonky3-artifact-schema",
        ),
        (
            text.replace("\"format\"", "\"extra\": 1,\n  \"format\""),
            "plonky3-artifact-schema",
        ),
    ] {
        assert_eq!(Witness::parse(&mutated).unwrap_err().id, id);
    }
    assert_eq!(trace.height(), HEIGHT);
}

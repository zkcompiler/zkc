use super::*;
use crate::{KoalaBearExt8, ring::Budget};
use serde_json::Value as Json;
use zkc_runtime::relation::{
    Assertion, Authority, Columns, Group, Height, HeightAuthority, Input, ReadModel, Scope, Table,
};
use zkc_runtime::ring::{Expression, Node};

const FINITE: &str = r#"["zkc.relation-bundle/0",[["p","koala-bear"]],[],
 [["t","required",["instance",1,8,false],"finite",[["w","witness","koala-bear",2]],
 ["zkc.ring/0",["koala-bear","koala-bear","koala-bear","koala-bear"],
 [["input",0],["input",1],["neg",0],["add",1,2],["input",3],["neg",4],["add",0,5],
 ["input",2],["mul",7,7],["neg",7],["add",8,9],["constant","koala-bear","0"],["mul",11,1]],
 [3,6,10,12,6]],
 [["read",0,"0",0],["read",0,"1",0],["read",0,"0",1],["public",0]],
 [[0,["interior",0,1]],[1,["first"]],[2,["all"]],[3,["interval",0,2]],[4,["last"]]],[]]]]"#;
fn kb(values: &[u32]) -> Vec<KoalaBear> {
    values.iter().map(|n| KoalaBear::from_u32(*n)).collect()
}

#[test]
fn finite_scopes_have_hand_calculated_residuals_and_check_windows_before_zero() {
    let bundle = Bundle::parse(FINITE).unwrap();
    let view = bundle.table_view(0, Identity::KoalaBear).unwrap();
    let result = rows(
        view.clone(),
        4,
        &kb(&[1, 0, 3, 1, 7, 2, 9, 0]),
        &[],
        &kb(&[1]),
        &Policy::default(),
        &mut Budget::default(),
        usize::MAX,
    )
    .unwrap();
    assert_eq!(
        result,
        kb(&[2, 0, 0, 0, 0, 4, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 8])
    );
    assert_eq!(view.lengths(2).unwrap_err().0, "bundle-window");
    assert_eq!(view.lengths(1).unwrap_err().0, "bundle-scope-height");
    for height in [0, 9] {
        assert_eq!(view.lengths(height).unwrap_err().0, "bundle-height");
    }
    for (w, c, p, code) in [
        (vec![0; 7], vec![], vec![1], "relation-table-witness-shape"),
        (
            vec![0; 8],
            vec![0],
            vec![1],
            "relation-table-configuration-shape",
        ),
        (vec![0; 8], vec![], vec![], "relation-table-public-shape"),
    ] {
        assert_eq!(
            rows(
                view.clone(),
                4,
                &kb(&w),
                &kb(&c),
                &kb(&p),
                &Policy::default(),
                &mut Budget::default(),
                usize::MAX
            )
            .unwrap_err()
            .code,
            format!("refused:{code}")
        );
    }
    assert_eq!(
        rows(
            view.clone(),
            4,
            &kb(&[0; 8]),
            &[],
            &kb(&[1]),
            &Policy::default(),
            &mut Budget { limit: 0, spent: 0 },
            usize::MAX
        )
        .unwrap_err()
        .code,
        "exhausted:ring-work"
    );
    assert!(
        rows(
            view,
            4,
            &kb(&[0; 8]),
            &[],
            &kb(&[1]),
            &Policy::default(),
            &mut Budget::default(),
            0
        )
        .is_err()
    );
}

fn recurrence() -> (Bundle, Json, Json, Json) {
    let bundle = Bundle::parse(include_str!(
        "../../../../compiler/adapters/plonky3/fixtures/recurrence/bundle.json"
    ))
    .unwrap();
    (
        bundle,
        serde_json::from_str(include_str!(
            "../../../../compiler/adapters/plonky3/fixtures/recurrence/bundle-configuration.json"
        ))
        .unwrap(),
        serde_json::from_str(include_str!(
            "../../../../compiler/adapters/plonky3/fixtures/recurrence/bundle-instance.json"
        ))
        .unwrap(),
        serde_json::from_str(include_str!(
            "../../../../compiler/adapters/plonky3/fixtures/recurrence/bundle-witness.json"
        ))
        .unwrap(),
    )
}
#[test]
fn actual_table_view_agrees_with_whole_bundle_evaluation_after_each_authority_changes() {
    let (bundle, c, i, w) = recurrence();
    let c = bundle.decode_configuration(&c).unwrap();
    let i = bundle.decode_instance(&i).unwrap();
    let w = bundle.decode_witness(&w).unwrap();
    let arithmetic = Arithmetic::<KoalaBear>(PhantomData);
    let view = bundle.table_view(0, Identity::KoalaBear).unwrap();
    assert_eq!((view.degree(), view.assertion_count()), (3, 9));
    for mutation in 0..4 {
        let (mut c, mut i, mut w) = (c.clone(), i.clone(), w.clone());
        match mutation {
            1 => w.tables[0].as_mut().unwrap()[0][0] = "3".into(),
            2 => i.publics[0][0] = "3".into(),
            3 => c.tables[0].1[0][0] = "4".into(),
            _ => (),
        }
        let data = view.slice(&c, &i, &w).unwrap();
        let parse = |s: &Columns| {
            s.iter()
                .map(|v| crate::parse_koala_bear_decimal(v).unwrap())
                .collect::<Vec<_>>()
        };
        let dense = view
            .evaluate(
                data.height,
                &parse(&data.witness),
                &parse(&data.configuration),
                &parse(&data.public_data),
                &arithmetic,
            )
            .unwrap();
        let reference = bundle.evaluate(&c, &i, &w, &arithmetic).unwrap();
        let mut expected = vec![KoalaBear::ZERO; 72];
        for residual in reference.residuals {
            expected[residual.row as usize * 9 + residual.assertion] =
                crate::parse_koala_bear_decimal(&residual.value[0]).unwrap();
        }
        assert_eq!(dense, expected);
        assert_eq!(dense.iter().all(|v| *v == KoalaBear::ZERO), mutation == 0);
    }
}

#[test]
fn cyclic_reads_bind_each_authority_and_preserve_extension_coordinates() {
    let field = Identity::KoalaBearExt8;
    let bundle = Bundle::new(
        vec![],
        vec![],
        vec![Table {
            name: "t".into(),
            optional: false,
            height: Height {
                authority: HeightAuthority::Fixed,
                min: 2,
                max: 2,
                power_of_two: false,
            },
            read_model: ReadModel::Cyclic,
            groups: vec![
                Group {
                    name: "c".into(),
                    authority: Authority::Config,
                    field,
                    width: 1,
                },
                Group {
                    name: "w".into(),
                    authority: Authority::Witness,
                    field,
                    width: 1,
                },
                Group {
                    name: "p".into(),
                    authority: Authority::Public,
                    field,
                    width: 1,
                },
            ],
            arena: Expression::new(
                vec![field; 3],
                vec![
                    Node::Input(0),
                    Node::Input(1),
                    Node::Mul(0, 1),
                    Node::Input(2),
                    Node::Neg(3),
                    Node::Add(2, 4),
                ],
                vec![5],
            )
            .unwrap(),
            inputs: vec![
                Input::Read {
                    group: 1,
                    offset: 1,
                    column: 0,
                },
                Input::Read {
                    group: 0,
                    offset: 0,
                    column: 0,
                },
                Input::Read {
                    group: 2,
                    offset: -1,
                    column: 0,
                },
            ],
            assertions: vec![Assertion {
                output: 0,
                scope: Scope::All,
            }],
            interactions: vec![],
        }],
    )
    .unwrap();
    let x = KoalaBearExt8::from_basis_coefficients_fn(|j| KoalaBear::from_usize(j + 1));
    let y = KoalaBearExt8::from_basis_coefficients_fn(|j| KoalaBear::from_usize(j * 3 + 2));
    let two = KoalaBearExt8::from_u32(2);
    let three = KoalaBearExt8::from_u32(3);
    let expected = vec![y * two - x, x * three - y];
    let got = rows(
        bundle.table_view(0, field).unwrap(),
        2,
        &[x, y],
        &[two, three],
        &[y, x],
        &Policy::default(),
        &mut Budget::default(),
        usize::MAX,
    )
    .unwrap();
    assert_eq!(got, expected);
    assert_eq!(
        bundle.table_view(0, Identity::KoalaBear).unwrap_err().0,
        "relation-table-carrier"
    );
}

#[test]
fn registry_checks_identity_missing_duplicate_carrier_and_retained_fact_limits() {
    let (bundle, _, _, _) = recurrence();
    let body = bundle.encode().to_string();
    let mut registry = Registry::default();
    assert_eq!(
        registry.insert(&"0".repeat(64), &body).unwrap_err().code,
        "refused:relation-asset-identity"
    );
    registry.insert(bundle.identity(), &body).unwrap();
    assert!(registry.bundle(bundle.identity()).is_some());
    assert_eq!(
        registry.insert(bundle.identity(), &body).unwrap_err().code,
        "refused:relation-asset-duplicate"
    );
    assert_eq!(
        registry
            .table_reference("missing", 0, Identity::KoalaBear)
            .unwrap_err()
            .code,
        "refused:relation-asset-missing"
    );
    assert_eq!(
        registry
            .table_reference(bundle.identity(), 1, Identity::KoalaBear)
            .unwrap_err()
            .code,
        "refused:relation-table-index"
    );
    for field in [Identity::KoalaBearExt8, Identity::Bls12381Fr] {
        assert_eq!(
            registry
                .table_reference(bundle.identity(), 0, field)
                .unwrap_err()
                .code,
            "refused:relation-table-carrier"
        );
    }
    assert!(registry.admitted_bytes() > body.len());
    let mut full = Registry {
        bytes: crate::ring::REGISTRY_BYTE_LIMIT - body.len(),
        ..Registry::default()
    };
    assert_eq!(
        full.insert(bundle.identity(), &body).unwrap_err().code,
        "exhausted:relation-assets-bytes"
    );
    assert!(full.assets.is_empty());
    // A harmless extra space exceeds the remaining text allowance before parse.
    assert_eq!(
        full.insert(bundle.identity(), &(body + " "))
            .unwrap_err()
            .code,
        "exhausted:relation-assets-bytes"
    );
}

#[test]
fn static_signature_is_independent_and_exact() {
    for (field, table, accepted) in [
        ("koala-bear", "0", true),
        ("koala-bear.ext8-binomial3", "1048576", true),
        ("koala-bear", "01", false),
        ("koala-bear", "1048577", false),
        ("bls12-381.fr", "0", false),
    ] {
        let binding = OperationBinding {
            contract: "relation.table_rows".into(),
            arguments: vec![field.into(), table.into()],
            implementation: "plonky3/relation.table_rows".into(),
        };
        assert_eq!(signature(&binding).is_some(), accepted);
        if accepted {
            assert_eq!(signature(&binding).unwrap(), binding.signature().unwrap());
        }
    }
}

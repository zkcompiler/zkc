use super::support::*;
use serde_json::json;
use zkc_backends::{Policy, Value};
use zkc_runtime::interactive::{
    Backend, Identity, LogicalType, PhysicalType, Representation, Type, admit_supplied,
};
#[test]
fn nominal_associations_and_native_advertisements_are_checked_independently() {
    let backend = backend(Policy::default());
    for d in [false, true] {
        let f = if d {
            Identity::Ristretto255Scalar
        } else {
            Identity::Bls12381Fr
        };
        let g = if d {
            Identity::Ristretto255Group
        } else {
            Identity::Bls12381G1
        };
        assert_eq!(g.scalar_field(), Some(f));
        let b = binding(d, "curve.msm");
        let sig = b.signature().unwrap();
        assert_eq!(
            sig.inputs[0].logical(),
            LogicalType::new(Type::Vector, f).unwrap()
        );
        assert_eq!(
            sig.inputs[1].logical(),
            LogicalType::new(Type::Groups, g).unwrap()
        );
        assert_eq!(
            sig.outputs[0].logical(),
            LogicalType::new(Type::Group, g).unwrap()
        );
        assert_eq!(backend.binding_signature(&b), Some(sig));
        for name in [
            "field.sub",
            "field.neg",
            "field.inverse",
            "vector.empty",
            "vector.append",
            "vector.splat",
            "vector.powers",
            "vector.add",
            "vector.sub",
            "vector.mul",
            "vector.scale",
            "vector.sum",
            "vector.dot",
            "vector.split",
            "vector.concat",
            "vector.at",
            "vector.length_check",
            "vector.gather",
            "vector.kronecker",
            "vector.matvec",
            "poly.from_coefficients",
            "poly.coefficients",
            "poly.degree_check",
            "poly.univariate_evaluate",
            "poly.univariate_boundary",
            "random.vector",
            "random.draw",
            "curve.neg",
            "curve.nonidentity",
            "curve.msm",
            "curve.scale_each",
            "curve.vector_add",
            "curve.vector_scale",
            "curve.split",
            "curve.concat",
            "curve.generator",
            "curve.add",
            "curve.scale",
            "curve.equal",
            "curve.empty",
            "curve.append",
            "curve.at",
            "curve.get",
            "curve.length",
            "curve.commit",
            "curve.response",
            "transcript.challenge",
            "field.constant",
            "field.add",
            "field.mul",
            "field.equal",
            "poly.boundary",
            "poly.round_evaluate",
        ] {
            let b = binding(d, name);
            assert_eq!(
                backend.binding_signature(&b),
                Some(b.signature().unwrap()),
                "{b:?}"
            );
            let mut bad = b.clone();
            bad.implementation = format!("invented/{name}");
            assert!(backend.binding_signature(&bad).is_none());
            assert!(bad.signature().is_err());
            bad = b.clone();
            bad.arguments[0] = "uninstalled.field".into();
            assert!(backend.binding_signature(&bad).is_none());
            assert!(bad.signature().is_err());
            bad = b.clone();
            bad.implementation = b.implementation.replace(
                if d { "dalek/" } else { "arkworks/" },
                if d { "arkworks/" } else { "dalek/" },
            );
            assert!(backend.binding_signature(&bad).is_none());
            assert!(bad.signature().is_err());
        }
        for name in ["bool.and", "bool.not", "bool.or", "control.require"] {
            let b = binding(d, name);
            assert_eq!(backend.binding_signature(&b), Some(b.signature().unwrap()));
        }
        for kind in [
            "field",
            "vector",
            "polynomial",
            "round",
            "group",
            "groups",
            "bool",
        ] {
            let mut b = binding(d, &format!("transcript.observe.{kind}"));
            let nominal = if kind == "group" || kind == "groups" {
                g
            } else {
                f
            };
            b.arguments = vec![
                (if f == Identity::Bls12381Fr {
                    Identity::Merlin3Fr64Be
                } else {
                    Identity::Merlin3Ristretto64Le
                })
                .name()
                .into(),
            ];
            if kind != "bool" {
                b.arguments.push(nominal.name().into());
            }
            b.arguments.push(if kind == "bool" {
                "zkcv.bool/1".into()
            } else {
                format!("zkcv.{kind}.{}/1", nominal.name())
            });
            assert_eq!(backend.binding_signature(&b), Some(b.signature().unwrap()));
            let mut bad = b.clone();
            *bad.arguments.last_mut().unwrap() = "zkcv.vector.uninstalled/1".into();
            assert!(bad.signature().is_err());
            assert!(backend.binding_signature(&bad).is_none());
            if kind != "bool" {
                let mut bad = b;
                bad.arguments[1] = if d {
                    "bls12-381.fr"
                } else {
                    "ristretto255.scalar"
                }
                .into();
                assert!(bad.signature().is_err());
                assert!(backend.binding_signature(&bad).is_none());
            }
        }
    }
    for name in [
        "vector.from_point",
        "vector.to_point",
        "vector.from_table",
        "vector.to_table",
        "poly.equality_weights",
        "poly.product_sum",
        "poly.product_round",
        "poly.fold",
        "poly.evaluate",
        "poly.empty_point",
        "poly.append_point",
    ] {
        let b = binding(false, name);
        assert_eq!(backend.binding_signature(&b), Some(b.signature().unwrap()));
        let b = binding(true, name);
        assert!(backend.binding_signature(&b).is_none());
        assert!(b.signature().is_err());
    }
    for spelling in [
        "table:ristretto255.scalar",
        "point:ristretto255.scalar",
        "field:ristretto255.group",
        "group:ristretto255.scalar",
        "vector:bls12-381.g1",
        "polynomial:unknown",
        "commitment:ristretto255.group",
    ] {
        assert!(LogicalType::parse(spelling).is_err());
    }
    assert!(
        PhysicalType::new(
            LogicalType::new(Type::Vector, Identity::Ristretto255Scalar).unwrap(),
            Representation::FrVector
        )
        .is_err()
    );
    assert!(
        PhysicalType::new(
            LogicalType::new(Type::Groups, Identity::Bls12381G1).unwrap(),
            Representation::RistrettoDiagonal
        )
        .is_err()
    );
}
#[test]
fn exact_attribute_counts_canonical_naturals_and_scalar_moduli_are_admitted() {
    let backend = backend(Policy::default());
    for d in [false, true] {
        for (name, attrs) in [
            ("vector.splat", vec!["01"]),
            ("vector.at", vec!["-1"]),
            ("vector.gather", vec!["0", "+2"]),
            ("vector.matvec", vec!["2", "3", "2"]),
            ("vector.matvec", vec!["2", "3"]),
            ("field.constant", vec!["00"]),
            ("vector.empty", vec!["0"]),
            ("poly.degree_check", vec![]),
        ] {
            let b = binding(d, name);
            let sig = b.signature().unwrap();
            let ret = (0..sig.outputs.len())
                .map(|i| format!("o{i}"))
                .collect::<Vec<_>>();
            let ins = (0..sig.inputs.len())
                .map(|i| format!("a{i}"))
                .collect::<Vec<_>>();
            let bytes = program(
                &[b],
                &sig.inputs,
                vec![json!(["op", "site", "b0", attrs, ins, ret])],
                &sig.outputs,
                &ret,
            );
            assert_eq!(
                admit_supplied(&bytes, &backend).unwrap_err().code,
                zkc_runtime::interactive::ErrorCode::Attributes
            );
        }
    }
    let d = "7237005577332262213973186563042994240857116359379907606001950938285454250989";
    let b = binding(true, "field.constant");
    let sig = b.signature().unwrap();
    let bytes = program(
        &[b],
        &[],
        vec![json!(["op", "site", "b0", [d], [], ["x"]])],
        &sig.outputs,
        &["x".into()],
    );
    assert!(admit_supplied(&bytes, &backend).is_err());
    assert!(matches!(
        call(
            false,
            "bool.and",
            &[],
            vec![Value::Bool(true), Value::Bool(false)]
        )[0],
        Value::Bool(false)
    ));
}
#[test]
fn runtime_refuses_wrong_implementation_and_full_operand_identity() {
    for d in [false, true] {
        let mut b = Controlled::new(super::support::backend(Policy::default()));
        b.implementation = Some("dalek/field.neg".into());
        assert_eq!(
            one(
                b,
                binding(d, "field.add"),
                &[],
                vec![field(d, 1), field(d, 2)]
            )
            .0
            .unwrap_err(),
            "refused:kernel-operands"
        );
        let mut b = Controlled::new(super::support::backend(Policy::default()));
        b.substitute = Some(field(!d, 1));
        assert_eq!(
            one(
                b,
                binding(d, "field.add"),
                &[],
                vec![field(d, 1), field(d, 2)]
            )
            .0
            .unwrap_err(),
            "refused:kernel-operands"
        );
    }
}

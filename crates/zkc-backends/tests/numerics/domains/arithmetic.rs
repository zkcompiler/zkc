use super::support::*;
use zkc_backends::{Policy, RistrettoScalar, Scalar, Value};
#[test]
fn scalar_vector_and_polynomial_contracts_have_both_field_meanings() {
    for d in [false, true] {
        assert_value(
            &call(d, "field.sub", &[], vec![field(d, 7), field(d, 3)])[0],
            &field(d, 4),
        );
        let neg = call(d, "field.neg", &[], vec![field(d, 7)]).remove(0);
        assert_value(
            &call(d, "field.add", &[], vec![neg, field(d, 7)])[0],
            &field(d, 0),
        );
        let inv = call(d, "field.inverse", &[], vec![field(d, 7)]).remove(0);
        assert_value(
            &call(d, "field.mul", &[], vec![inv, field(d, 7)])[0],
            &field(d, 1),
        );
        assert_error(
            d,
            "field.inverse",
            &[],
            vec![field(d, 0)],
            "refused:zero-inverse",
        );
        assert_value(&call(d, "vector.empty", &[], vec![])[0], &vector(d, &[]));
        assert_value(
            &call(
                d,
                "vector.append",
                &[],
                vec![vector(d, &[1, 2]), field(d, 3)],
            )[0],
            &vector(d, &[1, 2, 3]),
        );
        assert_value(
            &call(d, "vector.splat", &["3"], vec![field(d, 4)])[0],
            &vector(d, &[4, 4, 4]),
        );
        assert_value(
            &call(d, "vector.powers", &["4"], vec![field(d, 3)])[0],
            &vector(d, &[1, 3, 9, 27]),
        );
        for (op, expected) in [
            ("vector.add", [7, 10]),
            ("vector.sub", [3, 4]),
            ("vector.mul", [10, 21]),
        ] {
            assert_value(
                &call(d, op, &[], vec![vector(d, &[5, 7]), vector(d, &[2, 3])])[0],
                &vector(d, &expected),
            );
            assert_error(
                d,
                op,
                &[],
                vec![vector(d, &[1]), vector(d, &[])],
                "refused:length-mismatch",
            );
        }
        assert_value(
            &call(
                d,
                "vector.scale",
                &[],
                vec![vector(d, &[2, 3]), field(d, 5)],
            )[0],
            &vector(d, &[10, 15]),
        );
        assert_value(
            &call(d, "vector.sum", &[], vec![vector(d, &[2, 3, 5])])[0],
            &field(d, 10),
        );
        assert_value(
            &call(
                d,
                "vector.dot",
                &[],
                vec![vector(d, &[2, 3]), vector(d, &[5, 7])],
            )[0],
            &field(d, 31),
        );
        assert_value(
            &call(d, "vector.dot", &[], vec![vector(d, &[]), vector(d, &[])])[0],
            &field(d, 0),
        );
        assert_value(
            &call(d, "vector.sum", &[], vec![vector(d, &[])])[0],
            &field(d, 0),
        );
        assert_error(
            d,
            "vector.dot",
            &[],
            vec![vector(d, &[1]), vector(d, &[])],
            "refused:length-mismatch",
        );
        let split = call(d, "vector.split", &[], vec![vector(d, &[1, 2, 3, 4])]);
        assert_value(&split[0], &vector(d, &[1, 2]));
        assert_value(&split[1], &vector(d, &[3, 4]));
        assert_value(
            &call(d, "vector.concat", &[], split)[0],
            &vector(d, &[1, 2, 3, 4]),
        );
        for n in [&[][..], &[1][..], &[1, 2, 3][..]] {
            assert_error(
                d,
                "vector.split",
                &[],
                vec![vector(d, n)],
                "refused:split-length",
            );
        }
        assert_value(
            &call(d, "vector.at", &["1"], vec![vector(d, &[8, 9])])[0],
            &field(d, 9),
        );
        assert_error(
            d,
            "vector.at",
            &["2"],
            vec![vector(d, &[8, 9])],
            "refused:vector-index",
        );
        assert!(matches!(
            call(d, "vector.length_check", &["3"], vec![vector(d, &[1, 2])])[0],
            Value::Bool(false)
        ));
        assert_value(
            &call(
                d,
                "vector.gather",
                &["2", "0", "2"],
                vec![vector(d, &[4, 5, 6])],
            )[0],
            &vector(d, &[6, 4, 6]),
        );
        assert_value(
            &call(d, "vector.gather", &[], vec![vector(d, &[])])[0],
            &vector(d, &[]),
        );
        assert_error(
            d,
            "vector.gather",
            &["0", "3"],
            vec![vector(d, &[4, 5, 6])],
            "refused:vector-index",
        );
        assert_value(
            &call(
                d,
                "vector.kronecker",
                &[],
                vec![vector(d, &[2, 3]), vector(d, &[5, 7, 11])],
            )[0],
            &vector(d, &[10, 14, 22, 15, 21, 33]),
        );
        assert_value(
            &call(
                d,
                "vector.matvec",
                &["2", "3", "0"],
                vec![vector(d, &[1, 2, 3, 4, 5, 6]), vector(d, &[2, 3, 4])],
            )[0],
            &vector(d, &[20, 47]),
        );
        assert_value(
            &call(
                d,
                "vector.matvec",
                &["2", "3", "1"],
                vec![vector(d, &[1, 2, 3, 4, 5, 6]), vector(d, &[2, 3])],
            )[0],
            &vector(d, &[14, 19, 24]),
        );
        assert_value(
            &call(
                d,
                "vector.matvec",
                &["3", "0", "0"],
                vec![vector(d, &[]), vector(d, &[])],
            )[0],
            &vector(d, &[0, 0, 0]),
        );
        assert_error(
            d,
            "vector.matvec",
            &["2", "3", "0"],
            vec![vector(d, &[1, 2]), vector(d, &[2, 3, 4])],
            "refused:length-mismatch",
        );
        assert_error(
            d,
            "vector.matvec",
            &["2", "3", "1"],
            vec![vector(d, &[1, 2, 3, 4, 5, 6]), vector(d, &[2, 3, 4])],
            "refused:length-mismatch",
        );
        let poly = call(
            d,
            "poly.from_coefficients",
            &[],
            vec![vector(d, &[2, 3, 4, 0, 0])],
        )
        .remove(0);
        assert_value(
            &call(d, "poly.coefficients", &[], vec![poly.clone()])[0],
            &vector(d, &[2, 3, 4]),
        );
        assert!(matches!(
            call(d, "poly.degree_check", &["1"], vec![poly.clone()])[0],
            Value::Bool(false)
        ));
        assert!(matches!(
            call(d, "poly.degree_check", &["2"], vec![poly.clone()])[0],
            Value::Bool(true)
        ));
        assert_value(
            &call(
                d,
                "poly.univariate_evaluate",
                &[],
                vec![poly.clone(), field(d, 5)],
            )[0],
            &field(d, 117),
        );
        assert_value(
            &call(d, "poly.univariate_boundary", &[], vec![poly])[0],
            &field(d, 11),
        );
        let zero = call(d, "poly.from_coefficients", &[], vec![vector(d, &[0, 0])]).remove(0);
        assert_value(
            &call(d, "poly.coefficients", &[], vec![zero.clone()])[0],
            &vector(d, &[]),
        );
        assert!(matches!(
            call(d, "poly.degree_check", &["0"], vec![zero.clone()])[0],
            Value::Bool(true)
        ));
        assert_value(
            &call(d, "poly.univariate_evaluate", &[], vec![zero, field(d, 5)])[0],
            &field(d, 0),
        );
        let round = if d {
            Value::RistrettoRound([2u64, 3, 4].map(RistrettoScalar::from))
        } else {
            Value::Round([2, 3, 4].map(Scalar::from))
        };
        assert_value(
            &call(d, "poly.boundary", &[], vec![round.clone()])[0],
            &field(d, 11),
        );
        assert_value(
            &call(d, "poly.round_evaluate", &[], vec![round, field(d, 5)])[0],
            &field(d, 117),
        );
    }
}
#[test]
fn explicit_point_table_conversions_and_equality_weights_are_msb_first() {
    let p = Policy::default();
    let point = Value::point(vec![Scalar::from(2), Scalar::from(3)], &p).unwrap();
    assert_value(
        &call(false, "vector.from_point", &[], vec![point.clone()])[0],
        &vector(false, &[2, 3]),
    );
    assert_value(
        &call(false, "vector.to_point", &[], vec![vector(false, &[2, 3])])[0],
        &point,
    );
    let weights = call(false, "poly.equality_weights", &[], vec![point]).remove(0);
    assert_value(
        &call(false, "vector.sum", &[], vec![weights.clone()])[0],
        &field(false, 1),
    );
    let t = Value::table(&[1, 2, 4, 8].map(Scalar::from), &p).unwrap();
    let cells = call(false, "vector.from_table", &[], vec![t.clone()]).remove(0);
    assert_value(&cells, &vector(false, &[1, 2, 4, 8]));
    assert_value(
        &call(false, "vector.dot", &[], vec![weights, cells.clone()])[0],
        &field(false, 28),
    );
    assert_value(&call(false, "vector.to_table", &[], vec![cells])[0], &t);
    assert_value(
        &call(
            false,
            "poly.equality_weights",
            &[],
            vec![Value::point(vec![], &p).unwrap()],
        )[0],
        &vector(false, &[1]),
    );
    for bad in [&[][..], &[1, 2, 3][..]] {
        assert_error(
            false,
            "vector.to_table",
            &[],
            vec![vector(false, bad)],
            "refused:invalid-table-length",
        );
    }
}
#[test]
fn both_native_groups_obey_checked_contractions_and_sequence_operations() {
    for d in [false, true] {
        let bases = groups(d, &[2, 3]);
        let point = call(d, "curve.at", &["0"], vec![groups(d, &[31])]).remove(0);
        assert_value(
            &call(d, "curve.msm", &[], vec![vector(d, &[5, 7]), bases.clone()])[0],
            &point,
        );
        assert_value(
            &call(
                d,
                "curve.scale_each",
                &[],
                vec![vector(d, &[5, 7]), bases.clone()],
            )[0],
            &groups(d, &[10, 21]),
        );
        assert_value(
            &call(
                d,
                "curve.vector_scale",
                &[],
                vec![bases.clone(), field(d, 5)],
            )[0],
            &groups(d, &[10, 15]),
        );
        assert_value(
            &call(
                d,
                "curve.vector_add",
                &[],
                vec![bases.clone(), groups(d, &[5, 7])],
            )[0],
            &groups(d, &[7, 10]),
        );
        let halves = call(d, "curve.split", &[], vec![bases.clone()]);
        assert_value(&halves[0], &groups(d, &[2]));
        assert_value(&halves[1], &groups(d, &[3]));
        assert_value(&call(d, "curve.concat", &[], halves)[0], &bases);
        let generator = call(d, "curve.generator", &[], vec![]).remove(0);
        let negative = call(d, "curve.neg", &[], vec![generator.clone()]).remove(0);
        let identity = call(d, "curve.add", &[], vec![generator.clone(), negative]).remove(0);
        assert!(matches!(
            call(d, "curve.nonidentity", &[], vec![identity.clone()])[0],
            Value::Bool(false)
        ));
        assert!(matches!(
            call(d, "curve.nonidentity", &[], vec![generator.clone()])[0],
            Value::Bool(true)
        ));
        assert_value(
            &call(d, "curve.msm", &[], vec![vector(d, &[]), groups(d, &[])])[0],
            &identity,
        );
        assert_value(
            &call(d, "curve.scale", &[], vec![generator.clone(), field(d, 0)])[0],
            &identity,
        );
        assert!(matches!(
            call(
                d,
                "curve.equal",
                &[],
                vec![generator.clone(), generator.clone()]
            )[0],
            Value::Bool(true)
        ));
        assert_value(
            &call(d, "curve.append", &[], vec![groups(d, &[]), generator])[0],
            &groups(d, &[1]),
        );
        assert_value(&call(d, "curve.empty", &[], vec![])[0], &groups(d, &[]));
        for op in ["curve.msm", "curve.scale_each"] {
            assert_error(
                d,
                op,
                &[],
                vec![vector(d, &[1]), bases.clone()],
                "refused:length-mismatch",
            );
        }
        assert_error(
            d,
            "curve.vector_add",
            &[],
            vec![bases, groups(d, &[1])],
            "refused:length-mismatch",
        );
        for bad in [&[][..], &[1][..]] {
            assert_error(
                d,
                "curve.split",
                &[],
                vec![groups(d, bad)],
                "refused:split-length",
            );
        }
        assert_error(
            d,
            "curve.at",
            &["0"],
            vec![groups(d, &[])],
            "refused:group-index",
        );
    }
}
#[test]
fn vector_output_limits_reject_growth_before_work() {
    for d in [false, true] {
        let p = Policy {
            max_table_elements: 2,
            ..Policy::default()
        };
        assert_eq!(
            one(
                backend(p),
                binding(d, "vector.kronecker"),
                &[],
                vec![vector(d, &[1, 2]), vector(d, &[3, 4])]
            )
            .0
            .unwrap_err(),
            "exhausted:element-limit"
        );
        assert_eq!(
            one(
                backend(p),
                binding(d, "vector.concat"),
                &[],
                vec![vector(d, &[1, 2]), vector(d, &[3])]
            )
            .0
            .unwrap_err(),
            "exhausted:element-limit"
        );
        // The largest size admission accepts still exceeds this policy, and
        // is refused before any element is produced.
        assert_eq!(
            one(
                backend(p),
                binding(d, "vector.splat"),
                &["1048576"],
                vec![field(d, 1)]
            )
            .0
            .unwrap_err(),
            "exhausted:element-limit"
        );
        let mut b = Controlled::new(backend(Policy::default()));
        b.output_limit = Some(511);
        assert_eq!(
            one(b, binding(d, "field.inverse"), &[], vec![field(d, 0)])
                .0
                .unwrap_err(),
            "exhausted:output-bytes"
        );
    }
}

#[test]
fn msb_and_lsb_table_conversions_preserve_the_same_logical_vector() {
    use zkc_runtime::interactive::{Representation, Value as RuntimeValue};
    let original = vector(false, &[1, 2, 4, 8]);
    let mut to = binding(false, "vector.to_table");
    to.implementation = "arkworks-msb/vector.to_table".into();
    let msb = one(backend(Policy::default()), to, &[], vec![original.clone()])
        .0
        .unwrap()
        .remove(0);
    assert_eq!(
        msb.physical_type().representation(),
        Representation::TableMsb
    );
    let mut from = binding(false, "vector.from_table");
    from.implementation = "arkworks-msb/vector.from_table".into();
    assert_value(
        &one(backend(Policy::default()), from, &[], vec![msb])
            .0
            .unwrap()[0],
        &original,
    );
}

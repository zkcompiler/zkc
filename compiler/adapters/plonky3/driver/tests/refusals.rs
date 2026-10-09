//! Upstream features the capture cannot preserve, and metadata that contradicts
//! evaluation, refuse by name before any artifact exists.

use zkc_plonky3_air::export;
use zkc_plonky3_air_client::refused::*;

fn refusal<A>(air: &A) -> &'static str
where
    A: p3_air::Air<p3_air::SymbolicAirBuilder<zkc_plonky3_air::field::F>>,
{
    export(air, "refused").expect_err("capture must refuse").id
}

#[test]
fn unsupported_upstream_surfaces_refuse_by_name() {
    assert_eq!(refusal(&PeriodicAir), "plonky3-periodic-column");
    assert_eq!(
        refusal(&ExtensionConstraintAir),
        "plonky3-extension-constraint"
    );
    assert_eq!(
        refusal(&PermutationAir(PermutationSurface::Column)),
        "plonky3-permutation-column"
    );
    assert_eq!(
        refusal(&PermutationAir(PermutationSurface::Challenge)),
        "plonky3-permutation-challenge"
    );
    assert_eq!(
        refusal(&PermutationAir(PermutationSurface::ExpectedValue)),
        "plonky3-permutation-value"
    );
}

#[test]
fn selectors_outside_guard_position_refuse() {
    for misuse in [
        SelectorMisuse::AddedFirstRow,
        SelectorMisuse::SubtractedLastRow,
        SelectorMisuse::SharedProduct,
    ] {
        assert_eq!(
            refusal(&SelectorMisuseAir(misuse)),
            "plonky3-selector-not-guard",
            "{misuse:?}"
        );
    }
}

#[test]
fn metadata_that_contradicts_evaluation_refuses() {
    let consistent = MetadataAir::consistent();
    assert!(export(&consistent, "metadata").is_ok());
    let cases = [
        (
            MetadataAir {
                next_row_columns: vec![],
                ..MetadataAir::consistent()
            },
            "plonky3-next-row-metadata",
        ),
        (
            MetadataAir {
                next_row_columns: vec![3],
                ..MetadataAir::consistent()
            },
            "plonky3-next-row-metadata",
        ),
        (
            MetadataAir {
                next_row_columns: vec![0, 0],
                ..MetadataAir::consistent()
            },
            "plonky3-next-row-metadata",
        ),
        (
            MetadataAir {
                constraint_count: Some(2),
                ..MetadataAir::consistent()
            },
            "plonky3-constraint-count-hint",
        ),
        (
            MetadataAir {
                degree: Some(1),
                ..MetadataAir::consistent()
            },
            "plonky3-degree-hint",
        ),
        (
            MetadataAir {
                preprocessed: Some((6, 1)),
                ..MetadataAir::consistent()
            },
            "plonky3-preprocessed-shape",
        ),
        (
            MetadataAir {
                preprocessed: Some((8, 0)),
                ..MetadataAir::consistent()
            },
            "plonky3-preprocessed-shape",
        ),
    ];
    for (air, id) in cases {
        assert_eq!(refusal(&air), id, "{air:?}");
    }
    // Absent hints and an unread fixed table are not refusals.
    let unhinted = MetadataAir {
        constraint_count: None,
        degree: None,
        preprocessed: Some((8, 2)),
        ..MetadataAir::consistent()
    };
    assert!(export(&unhinted, "metadata").is_ok());
}

#[test]
fn evaluation_failures_and_unstable_evaluation_refuse() {
    assert_eq!(refusal(&UndeclaredPublicAir), "plonky3-eval-panicked");
    assert_eq!(refusal(&PanickingAir), "plonky3-eval-panicked");
    assert_eq!(refusal(&WideWindowAir), "plonky3-eval-panicked");
    assert_eq!(
        refusal(&NondeterministicAir),
        "plonky3-nondeterministic-eval"
    );
    assert_eq!(refusal(&ProbeDependentAir), "plonky3-probe-dependent-eval");
}

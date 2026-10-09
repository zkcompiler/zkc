use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_field::PrimeCharacteristicRing;
use p3_matrix::dense::RowMajorMatrix;
use zkc_plonky3_air::bundle::BundleView;
use zkc_plonky3_air::{ClosedView, Instance, SelectorLaw, Slot, export, field::F};
use zkc_plonky3_air_client::CounterAir;

struct PublicSum;
impl<T> BaseAir<T> for PublicSum {
    fn width(&self) -> usize {
        1
    }
    fn num_public_values(&self) -> usize {
        4096
    }
}
impl<AB: AirBuilder> Air<AB> for PublicSum {
    fn eval(&self, builder: &mut AB) {
        let mut terms: Vec<AB::Expr> = builder
            .public_values()
            .iter()
            .copied()
            .map(Into::into)
            .collect();
        while terms.len() > 1 {
            terms = terms
                .as_chunks::<2>()
                .0
                .iter()
                .map(|pair| pair[0].clone() + pair[1].clone())
                .collect();
        }
        let value = builder.main().current_slice()[0];
        builder.assert_eq(value, terms.pop().unwrap());
    }
}

#[test]
fn public_broadcast_expansion_refuses_before_materialization() {
    let captured = export(&PublicSum, "public-sum").unwrap();
    let statement = Instance {
        export_sha256: captured.sha256(),
        height: 1024,
        public_values: vec![F::ZERO; 4096],
    };
    let view = ClosedView::bind(&captured, &statement).unwrap();
    // The supplied trace and publics occupy only 20 KiB. Broadcasting every
    // public into every row exceeds the view's separate materialization cap.
    let trace = RowMajorMatrix::new(vec![F::ZERO; 1024], 1);
    assert_eq!(
        view.row_inputs(&trace, SelectorLaw::RowIndicator)
            .unwrap_err()
            .id,
        "plonky3-view-limit"
    );
}

#[test]
fn reference_interpolation_and_residual_shape_are_checked() {
    let captured = export(&CounterAir { guarded: true }, "counter").unwrap();
    let statement = Instance {
        export_sha256: captured.sha256(),
        height: 512,
        public_values: vec![],
    };
    let view = ClosedView::bind(&captured, &statement).unwrap();
    let trace = CounterAir::generate(512);
    assert_eq!(
        view.coefficient_inputs(&trace).unwrap_err().id,
        "plonky3-coefficient-limit"
    );
    assert_eq!(view.residuals(&[]).unwrap_err().id, "plonky3-view-shape");
    let input = view.row_inputs(&trace, SelectorLaw::RowIndicator).unwrap();
    assert!(
        view.residuals(&input)
            .unwrap()
            .iter()
            .all(|x| *x == F::ZERO)
    );
}

#[test]
fn binding_rechecks_a_modified_candidate_before_interpretation() {
    let mut captured = export(&CounterAir { guarded: true }, "counter").unwrap();
    captured.slots[0] = Slot::Main {
        offset: 0,
        column: 1,
    };
    let statement = Instance {
        export_sha256: captured.sha256(),
        height: 8,
        public_values: vec![],
    };
    assert_eq!(
        ClosedView::bind(&captured, &statement).unwrap_err().id,
        "plonky3-slot"
    );
    assert_eq!(
        BundleView::derive(&captured).unwrap_err().id,
        "plonky3-slot"
    );
}

#[test]
fn derived_bundle_checks_shape_and_work_before_evaluation() {
    let captured = export(&PublicSum, "public-sum").unwrap();
    let bundle = BundleView::derive(&captured).unwrap();
    let publics = vec![F::ZERO; 4096];
    let trace = RowMajorMatrix::new(vec![F::ZERO; 32768], 1);
    assert_eq!(
        bundle.residuals(&trace, &publics).unwrap_err().id,
        "plonky3-view-limit"
    );
    let small = RowMajorMatrix::new(vec![F::ZERO; 8], 1);
    assert_eq!(
        bundle.residuals(&small, &[]).unwrap_err().id,
        "plonky3-public-values"
    );
    let wrong_width = RowMajorMatrix::new(vec![F::ZERO; 16], 2);
    assert_eq!(
        bundle.residuals(&wrong_width, &publics).unwrap_err().id,
        "plonky3-trace-width"
    );
    assert!(
        bundle
            .residuals(&small, &publics)
            .unwrap()
            .iter()
            .all(|(_, _, v)| *v == F::ZERO)
    );
}

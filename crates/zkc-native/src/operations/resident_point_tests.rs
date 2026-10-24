//! Validation provenance and storage controls for the resident family adapter.
use crate::Value;
use crate::operations::curve::{Family, PointStorage, PointView};
use zkc_kernels::allocation::{self, failure};

macro_rules! adapter_tests {
    ($module:ident, $kernel:path, $point:ident, $bulk:ident, $element:ident) => {
        mod $module {
            use super::*;
            use $kernel as kernel;
            type Point = kernel::$point;
            type Bulk = kernel::$bulk;

            fn samples() -> [Point; 4] {
                let g = Point::generator();
                [
                    Point::identity(),
                    g,
                    g.neg(),
                    g.scale(kernel::Scalar::from(7)),
                ]
            }

            #[test]
            fn borrowed_points_and_publication_preserve_the_reserved_buffer() {
                let expected = samples();
                let mut buffer = <Bulk as PointStorage<Point>>::reserve(expected.len()).unwrap();
                let address = buffer.as_elements().as_ptr();
                let bytes = buffer.storage_bytes();
                for point in expected {
                    <Bulk as PointStorage<Point>>::push(&mut buffer, point);
                }
                assert_eq!(buffer.as_elements().as_ptr(), address);
                assert_eq!(buffer.storage_bytes(), bytes);
                assert_eq!(
                    <Point as Family<Bulk>>::width(),
                    size_of::<kernel::$element>()
                );

                // Borrowing, wrapper arithmetic and publication consume no
                // managed staging reservation. The raw buffer stays in place.
                let _guard = failure::after(0);
                let value = <Point as Family<Bulk>>::values(buffer);
                let view = <Point as Family<Bulk>>::points(&value).unwrap();
                assert_eq!(view.as_elements().as_ptr(), address);
                assert_eq!(view.storage_bytes(), bytes);
                assert_eq!(PointView::len(view), expected.len());
                assert_eq!(PointView::get(view, 4), None);
                assert_eq!(PointView::get(view, usize::MAX), None);
                assert_eq!(PointView::iter(view).collect::<Vec<_>>(), expected);
                assert_eq!(
                    PointView::iter(view).rev().collect::<Vec<_>>(),
                    expected.into_iter().rev().collect::<Vec<_>>()
                );
                let point = PointView::get(view, 1).unwrap();
                let sum = crate::operations::curve::Group::add(
                    point,
                    crate::operations::curve::Group::neg(point),
                );
                let single = <Point as Family<Bulk>>::value(sum);
                assert_eq!(
                    <Point as Family<Bulk>>::point(&single).unwrap(),
                    Point::identity()
                );
                assert_eq!(PointView::iter(view).collect::<Vec<_>>(), expected);
                assert!(allocation::reserve::<u8>(1).is_err());
            }

            #[test]
            fn addition_uses_one_reserved_provider_buffer_and_preserves_inputs() {
                let expected = samples();
                let left = Bulk::from_slice(&expected).unwrap();
                let right = Bulk::from_slice(&expected.map(|point| point.neg())).unwrap();
                let _guard = failure::after(1);
                let mut output = <Bulk as PointStorage<Point>>::reserve(left.len()).unwrap();
                let address = output.as_elements().as_ptr();
                let bytes = output.storage_bytes();
                <Bulk as PointStorage<Point>>::add_many(&left, &right, &mut output).unwrap();
                assert_eq!(output.len(), expected.len());
                assert!(output.iter().all(|point| point == Point::identity()));
                let value = <Point as Family<Bulk>>::values(output);
                let view = <Point as Family<Bulk>>::points(&value).unwrap();
                assert_eq!(view.as_elements().as_ptr(), address);
                assert_eq!(view.storage_bytes(), bytes);
                assert_eq!(left.iter().collect::<Vec<_>>(), expected);
                assert_eq!(
                    right.iter().collect::<Vec<_>>(),
                    expected.map(|point| point.neg())
                );
                assert!(allocation::reserve::<u8>(1).is_err());
            }

            #[test]
            fn addition_shape_refusal_preserves_the_private_destination() {
                let left = Bulk::from_slice(&samples()).unwrap();
                let right = Bulk::from_slice(&samples()[..3]).unwrap();
                for (left, right) in [(&left, &right), (&right, &left)] {
                    let mut output = <Bulk as PointStorage<Point>>::reserve(left.len()).unwrap();
                    let address = output.as_elements().as_ptr();
                    let _guard = failure::after(0);
                    assert_eq!(
                        <Bulk as PointStorage<Point>>::add_many(left, right, &mut output),
                        Err(kernel::Error::LengthMismatch)
                    );
                    assert!(output.is_empty());
                    assert_eq!(output.as_elements().as_ptr(), address);
                    assert!(allocation::reserve::<u8>(1).is_err());
                }
                let expected = samples();
                let mut output = Bulk::from_slice(&expected).unwrap();
                let address = output.as_elements().as_ptr();
                let _guard = failure::after(0);
                assert_eq!(
                    <Bulk as PointStorage<Point>>::add_many(&left, &left, &mut output),
                    Err(kernel::Error::LengthMismatch)
                );
                assert_eq!(output.iter().collect::<Vec<_>>(), expected);
                assert_eq!(output.as_elements().as_ptr(), address);
                assert!(allocation::reserve::<u8>(1).is_err());
            }

            #[test]
            fn scaling_writes_directly_into_one_reserved_provider_buffer() {
                let expected = samples();
                let input = Bulk::from_slice(&expected).unwrap();
                let scalar = kernel::Scalar::from(3);
                for each in [false, true] {
                    // One managed reservation constructs the destination.
                    // Neither scaling nor publication may stage another Vec.
                    let _guard = failure::after(1);
                    let mut output = <Bulk as PointStorage<Point>>::reserve(input.len()).unwrap();
                    let address = output.as_elements().as_ptr();
                    if each {
                        let scalars = [kernel::Scalar::ZERO, kernel::Scalar::ONE, scalar, scalar];
                        let elements = scalars.map(kernel::Scalar::into_element);
                        <Bulk as PointStorage<Point>>::scale_each(
                            &elements,
                            &input,
                            &mut output,
                            0,
                        )
                        .unwrap();
                        for (actual, (point, scalar)) in
                            output.iter().zip(expected.iter().zip(scalars))
                        {
                            assert_eq!(actual, point.scale(scalar));
                        }
                    } else {
                        <Bulk as PointStorage<Point>>::scale_many(
                            &input,
                            scalar.into_element(),
                            &mut output,
                            0,
                        )
                        .unwrap();
                        for (actual, point) in output.iter().zip(expected) {
                            assert_eq!(actual, point.scale(scalar));
                        }
                    }
                    let value = <Point as Family<Bulk>>::values(output);
                    let view = <Point as Family<Bulk>>::points(&value).unwrap();
                    assert_eq!(view.len(), input.len());
                    assert_eq!(view.as_elements().as_ptr(), address);
                    assert_eq!(input.iter().collect::<Vec<_>>(), expected);
                    assert!(allocation::reserve::<u8>(1).is_err());
                }
            }

            #[test]
            fn projections_and_destination_reservations_keep_their_refusals() {
                assert_eq!(
                    <Point as Family<Bulk>>::point(&Value::Bool(false))
                        .unwrap_err()
                        .code,
                    "refused:kernel-operands"
                );
                assert_eq!(
                    <Point as Family<Bulk>>::points(&Value::Bool(false))
                        .unwrap_err()
                        .code,
                    "refused:kernel-operands"
                );
                for len in [0, 4] {
                    let _guard = failure::after(0);
                    assert_eq!(
                        <Bulk as PointStorage<Point>>::reserve(len)
                            .unwrap_err()
                            .code,
                        "exhausted:allocation"
                    );
                }
                let empty = <Bulk as PointStorage<Point>>::reserve(0).unwrap();
                let value = <Point as Family<Bulk>>::values(empty);
                let view = <Point as Family<Bulk>>::points(&value).unwrap();
                assert_eq!(PointView::len(view), 0);
                assert_eq!(PointView::get(view, 0), None);
                assert_eq!(PointView::iter(view).count(), 0);
            }
        }
    };
}

adapter_tests!(
    halo_g1,
    zkc_kernels::halo2curves::bn254,
    G1,
    G1Vector,
    G1Element
);
adapter_tests!(
    halo_g2,
    zkc_kernels::halo2curves::bn254,
    G2,
    G2Vector,
    G2Element
);
adapter_tests!(
    blst_g1,
    zkc_kernels::blst::bls12_381,
    G1,
    G1Vector,
    G1Element
);
adapter_tests!(
    blst_g2,
    zkc_kernels::blst::bls12_381,
    G2,
    G2Vector,
    G2Element
);

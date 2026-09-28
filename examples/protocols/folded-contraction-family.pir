// One interaction algorithm, instantiated over an explicitly selected field.
// This numerical client makes no cryptographic security claim.
use zkc::algebra::{
  Field,
  Vector
};
use zkc::algebra;
use zkc::core;
fn Fold<F: domain Field>(values: Vector<F::Element>, point: F::Element) -> Vector<F::Element> requires (
  Field(F)
) {
  [__site_0] let (lower, upper) = zkc::algebra::vector_split::<F>(values);
  [__site_1] let difference = zkc::algebra::vector_sub::<F>(upper, lower);
  [__site_2] let scaled = zkc::algebra::vector_scale::<F>(difference, point);
  [__site_3] let folded = zkc::algebra::vector_add::<F>(lower, scaled);
  return folded;
}
fn Contraction<F: domain Field>(
  left: Vector<F::Element>,
  right: Vector<F::Element>,
  weights: Vector<F::Element>
) -> F::Element requires (Field(F)) {
  [__site_0] let products = zkc::algebra::vector_mul::<F>(left, right);
  [__site_1] let result = zkc::algebra::vector_dot::<F>(weights, products);
  return result;
}
fn Check<F: domain Field>(actual: F::Element, expected: F::Element) -> bool requires (Field(F)) {
  [__site_0] let equal = zkc::algebra::equal::<F>(actual, expected);
  [__site_1] zkc::core::require(equal);
  return equal;
}
protocol FoldedContraction<F: Field> {
  roles (Worker, Checker);
  inputs (
    Worker left: Vector<F::Element>,
    Worker right: Vector<F::Element>,
    Worker weights: Vector<F::Element>,
    Checker point: F::Element,
    Checker expected: F::Element
  );
  outputs (Worker result: F::Element, Checker accepted: bool);
  message [__site_0] point: Checker(point) -> Worker(received_point);
  let result = local Worker {
    let folded = (Fold(left, received_point), Fold(right, received_point));
    Contraction(weights: weights, left: folded.0, right: folded.1)
  };
  message [__site_4] result: Worker(result) -> Checker(received_result);
  let accepted = local Checker {
    Check(received_result, expected)
  };
  finish {
    result,
    accepted
  };
}
entry main = FoldedContraction::<F = "koala-bear">;

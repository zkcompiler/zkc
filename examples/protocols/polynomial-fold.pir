// Local algorithm example, not a proof system: coefficients are high to low.
// Keep bulk polynomial operations when they match an algorithm; use local
// control for stateful recurrences or algorithms without an existing primitive.
use zkc::algebra::{
  Field,
  Vector
};
use zkc::algebra;
fn MultiplyAdd<F: Field>(a: F::Element, b: F::Element, c: F::Element) -> F::Element {
  let product = zkc::algebra::mul(a, b);
  let result = zkc::algebra::add(product, c);
  return result;
}
fn Evaluate<F: Field>(coefficients: Vector<F::Element>, point: F::Element, negate: bool) -> F::Element {
  let mut result = zkc::algebra::constant::<F>() attributes ("0");
  for i in 0..coefficients.len() {
    result = MultiplyAdd::<F>(result, point, coefficients[i]);
  }
  if negate {
    result = zkc::algebra::neg(result);
  } else {
    // No change: the frontend supplies the unchanged branch result.
  }
  return result;
}
configure EvaluatePolynomial = Evaluate(F = "koala-bear");
protocol Main {
  roles (P);
  inputs (
    P coefficients: Vector<"koala-bear"::Element>,
    P point: "koala-bear"::Element,
    P negate: bool
  );
  outputs (P "koala-bear"::Element);
  local P: let value = EvaluatePolynomial(coefficients, point, negate);
  return value;
}
instance concrete: Main {
  roles (P = P);
}
entry main = concrete;

// A numerical integration client, not a cryptographic proof of correct work.
// The verifier supplies an evaluation point and independently expected result.
// Only the concrete configurations select a field; no algorithm names a backend.
module {
  fn Fold<F: domain Field>(values: Vector<F::Element>, point: F::Element) -> Vector<F::Element> requires (
    Field(F)
  ) {
    [__site_0] let (lower, upper) = vector::split::<F>(values);
    [__site_1] let difference = vector::sub::<F>(upper, lower);
    [__site_2] let scaled = vector::scale::<F>(difference, point);
    [__site_3] let folded = vector::add::<F>(lower, scaled);
    return folded;
  }

  fn Contraction<F: domain Field>(
    left: Vector<F::Element>,
    right: Vector<F::Element>,
    weights: Vector<F::Element>
  ) -> F::Element requires (Field(F)) {
    [__site_0] let products = vector::mul::<F>(left, right);
    [__site_1] let result = vector::dot::<F>(weights, products);
    return result;
  }

  fn Check<F: domain Field>(actual: F::Element, expected: F::Element) -> bool requires (Field(F)) {
    [__site_0] let equal = field::equal::<F>(actual, expected);
    [__site_1] control::require(equal);
    return equal;
  }

  configure FoldValues = Fold(F = koala-bear);
  configure Contract = Contraction(F = koala-bear);
  configure CheckResult = Check(F = koala-bear);
  protocol FoldedContraction {
    roles (Worker, Checker);
    inputs (
      Worker left: Vector<koala-bear::Element>,
      Worker right: Vector<koala-bear::Element>,
      Worker weights: Vector<koala-bear::Element>,
      Checker point: koala-bear::Element,
      Checker expected: koala-bear::Element
    );
    outputs (Worker koala-bear::Element, Checker bool);
    message [__site_0] point: Checker(point) -> Worker(received_point);
    local [__site_1] Worker: let folded_left = FoldValues(left, received_point);
    local [__site_2] Worker: let folded_right = FoldValues(right, received_point);
    local [__site_3] Worker: let result = Contract(folded_left, folded_right, weights);
    message [__site_4] result: Worker(result) -> Checker(received_result);
    local [__site_5] Checker: let accepted = CheckResult(received_result, expected);
    return (result, accepted);
  }

  instance contraction: FoldedContraction {
    roles (Worker = Worker, Checker = Checker);
  }

  entry main = contraction;
}

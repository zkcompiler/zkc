module {
  fn Equation<F: domain Field>(
    subject: F::Element,
    expected: F::Element,
    context: F::Element,
    admitted: F::Element
  ) -> bool requires (Field(F)) {
    [__site_0] let ok = field::equal::<F>(subject, expected);
    [equation_guard] control::require(ok);
    [__site_1] let bound = field::equal::<F>(context, admitted);
    [context_guard] control::require(bound);
    return ok;
  }

  fn Ignore<F: domain Field>(
    subject: F::Element,
    expected: F::Element,
    context: F::Element,
    admitted: F::Element
  ) -> bool requires (Field(F)) {
    [__site_0] let ok = field::equal::<F>(subject, expected);
    return ok;
  }

  configure Verify = Equation(F = bls12-381.fr);
  configure IgnoreCheck = Ignore(F = bls12-381.fr);
  protocol Pair {
    roles (V);
    inputs (
      V x: "bls12-381.fr"::Element,
      V y: "bls12-381.fr"::Element,
      V ctx: "bls12-381.fr"::Element,
      V admitted: "bls12-381.fr"::Element
    );
    outputs (V bool, V bool);
    local [first] V: let first_ok = Verify(x, y, ctx, admitted);
    local [second] V: let second_ok = Verify(y, x, admitted, ctx);
    return (first_ok, second_ok);
  }

  instance pair: Pair {
    roles (V = V);
  }

  entry main = pair;
}

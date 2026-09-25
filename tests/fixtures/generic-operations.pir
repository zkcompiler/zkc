module {
  // A reusable mathematical algorithm, independent of field and table storage.
  fn Fold<F: domain Field>(a: Table<F>, r: F::Element) -> Table<F> requires (CommRing(F)) {
    [fold] let result = poly::fold::<F>(a, r);
    return result;
  }

  // The scalar domain belongs to the selected group, not to a global profile.
  fn Scale<G: domain Group>(g: G::Element, r: G::Scalar::Element) -> G::Element requires (
    ScalarAction(G)
  ) {
    [scale] let result = curve::scale::<G>(g, r);
    return result;
  }

  fn Both<>(a: bool, b: bool) -> bool {
    [and] let result = bool::and(a, b);
    return result;
  }

  configure Partial = Fold();
  configure Left = Partial(F = bls12-381.fr) using (fold = "arkworks-msb/poly.fold");
  configure Right = Partial(F = bls12-381.fr);
  configure Shared = Right();
  configure Curve = Scale(G = bls12-381.g1);
  configure Boolean = Both();
  configure Unused = Fold();
  protocol Round {
    roles (P, V);
    inputs (
      P a: Table<"bls12-381.fr">,
      P b: Table<"bls12-381.fr">,
      P g: "bls12-381.g1"::Element,
      P x: bool,
      P y: bool,
      V r: "bls12-381.fr"::Element
    );
    outputs (
      P Table<"bls12-381.fr">,
      P Table<"bls12-381.fr">,
      P Table<"bls12-381.fr">,
      P "bls12-381.g1"::Element,
      P bool
    );
    message [challenge] field-challenge: V(r) -> P(rp);
    local [left] P: let left = Left(a, rp);
    local [right] P: let right = Right(b, rp);
    local [shared] P: let shared = Shared(a, rp);
    local [scale] P: let scaled = Curve(g, rp);
    local [both] P: let both = Boolean(x, y);
    return (left, right, shared, scaled, both);
  }

  instance concrete: Round {
    roles (P = P, V = V);
  }

  entry main = concrete;
}

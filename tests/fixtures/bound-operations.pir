module {
  bind fold_left = poly::fold(bls12-381.fr);
  bind fold_right = poly::fold(bls12-381.fr);
  bind scale = curve::scale(bls12-381.g1);
  bind empty = poly::empty_point(bls12-381.fr);
  fn FoldLeft(a: Table<"bls12-381.fr">, r: "bls12-381.fr"::Element) -> Table<"bls12-381.fr"> {
    [fold] let result = fold_left(a, r);
    return result;
  }

  fn FoldRight(a: Table<"bls12-381.fr">, r: "bls12-381.fr"::Element) -> Table<"bls12-381.fr"> {
    [fold] let result = fold_right(a, r);
    return result;
  }

  fn Scale(g: "bls12-381.g1"::Element, r: "bls12-381.fr"::Element) -> "bls12-381.g1"::Element {
    [scale] let result = scale(g, r);
    return result;
  }

  fn Empty() -> Point<"bls12-381.fr"> {
    [empty] let result = empty();
    return result;
  }

  protocol Round {
    roles (P, V);
    inputs (
      P a: Table<"bls12-381.fr">,
      P b: Table<"bls12-381.fr">,
      P g: "bls12-381.g1"::Element,
      V r: "bls12-381.fr"::Element
    );
    outputs (P Table<"bls12-381.fr">, P Table<"bls12-381.fr">, P "bls12-381.g1"::Element);
    message [challenge] field-challenge: V(r) -> P(rp);
    local [left] P: let left = FoldLeft(a, rp);
    local [right] P: let right = FoldRight(b, rp);
    local [scale] P: let scaled = Scale(g, rp);
    return (left, right, scaled);
  }

  instance concrete: Round {
    roles (P = P, V = V);
  }

  entry main = concrete;
}

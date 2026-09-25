// Pairing is an algebraic predicate over separately typed source groups.
module {
  bind neg = curve.neg(bn254.g1);
  bind empty1 = curve.empty(bn254.g1);
  bind append1 = curve.append(bn254.g1);
  bind concat1 = curve.concat(bn254.g1);
  bind empty2 = curve.empty(bn254.g2);
  bind append2 = curve.append(bn254.g2);

  fn Pair<F: domain Field>(
    left: Vector<F::PairingG1::Element>,
    right: Vector<F::PairingG2::Element>
  ) -> bool requires (PairingField(F)) {
    [pair] let accepted = pairing::check::<F>(left, right);
    return accepted;
  }

  fn Build(p: "bn254.g1"::Element, q: "bn254.g2"::Element)
      -> (Vector<"bn254.g1"::Element>, Vector<"bn254.g2"::Element>) {
    [neg] let negative = neg(p);
    [empty1] let empty1 = empty1();
    [first] let first = append1(empty1, p);
    [second] let second = append1(empty1, negative);
    [left] let left = concat1(first, second);
    [empty2] let empty2 = empty2();
    [right1] let right1 = append2(empty2, q);
    [right] let right = append2(right1, q);
    return (left, right);
  }

  configure BNPair = Pair(F = bn254.fr);
  protocol Main {
    roles (V);
    inputs (V p: "bn254.g1"::Element, V q: "bn254.g2"::Element);
    outputs (V bool);
    local [build] V: let (left, right) = Build(p, q);
    local [check] V: let accepted = BNPair(left, right);
    return accepted;
  }
  instance concrete: Main { roles (V = V); }
  entry main = concrete;
}

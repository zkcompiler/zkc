module {
  fn Twice<F: domain Field>(x: F::Element) -> F::Element requires (Field(F)) {
    [sum] let y = field::add::<F>(x, x);
    return y;
  }

  fn Four<F: domain Field>(x: F::Element) -> F::Element requires (PrimeField(F)) {
    [first] let a = Chosen::<F>(x);
    [second] let b = Twice::<F>(a);
    return b;
  }

  configure Chosen = Twice();
  configure Left = Four(F = bls12-381.fr);
  configure Right = Four(F = koala-bear);
  fn Closed(x: koala-bear::Element) -> koala-bear::Element {
    [configured] let a = Right(x);
    return a;
  }

  protocol Round {
    roles (P);
    inputs (P x: "bls12-381.fr"::Element, P y: koala-bear::Element);
    outputs (P "bls12-381.fr"::Element, P koala-bear::Element);
    local [left] P: let a = Left(x);
    local [right] P: let b = Closed(y);
    return (a, b);
  }

  instance concrete: Round {
    roles (P = P);
  }

  entry main = concrete;
}

module {
  bind draw = random::draw(bls12-381.fr);
  bind equal = field::equal(bls12-381.fr);
  bind require = control::require();
  fn Draw(r: Rng<"bls12-381.fr">) -> ("bls12-381.fr"::Element, Rng<"bls12-381.fr">) {
    [sample] let (x, next) = draw(r);
    return (x, next);
  }

  fn Two(r: Rng<"bls12-381.fr">) -> ("bls12-381.fr"::Element, Rng<"bls12-381.fr">) {
    [first] let (a, r1) = Draw(r);
    [second] let (b, r2) = Draw(r1);
    return (b, r2);
  }

  fn Check(x: "bls12-381.fr"::Element) -> bool {
    [equal] let ok = equal(x, x);
    [guard] require(ok);
    return ok;
  }

  protocol Main {
    roles (P, V);
    inputs (V coins: Rng<"bls12-381.fr">);
    outputs (V bool, V Rng<"bls12-381.fr">);
    local [draw] V: let (x, r2) = Two(coins);
    message [sample] field: V(x) -> P(seen);
    local [check] V: let ok = Check(x);
    return (ok, r2);
  }

  instance concrete: Main {
    roles (P = P, V = V);
  }

  entry main = concrete;
}

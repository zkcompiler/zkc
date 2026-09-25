// Independent concrete authoring, preserving explicit protocol/local sites.
module {
  fn Sample(coins: Rng<"bls12-381.fr">) -> ("bls12-381.fr"::Element, Rng<"bls12-381.fr">) {
    [draw] let (secret, after) = random::draw(coins);
    return (secret, after);
  }
  fn Multiply(secret: "bls12-381.fr"::Element) -> "bls12-381.g1"::Element {
    let base = curve::generator::<"bls12-381.g1">();
    return curve::scale(base, secret);
  }
  fn Verify(point: "bls12-381.g1"::Element, secret: "bls12-381.fr"::Element) -> bool {
    let base = curve::generator::<"bls12-381.g1">();
    let expected = curve::scale(base, secret);
    let same = curve::equal(point, expected);
    control::require(same);
    return same;
  }
  protocol Agreement {
    roles (P, V); inputs (V coins: Rng<"bls12-381.fr">); outputs (V bool);
    local [sample] V: let (secret, after) = Sample(coins);
    message challenge: V(secret) -> P(received_secret);
    local [public] P: let point = Multiply(received_secret);
    message point: P(point) -> V(received_point);
    local [check] V: let accepted = Verify(received_point, secret);
    return accepted;
  }
  instance run: Agreement { roles (P = P, V = V); }
  entry main = run;
}

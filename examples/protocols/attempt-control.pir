// Lifecycle control fixture, not a cryptographic proof protocol. `retry` is an
// explicit fault-injection input; production code derives it from its guard.
module {
  fn Draw(coins: Rng<"bls12-381.fr">)
      -> ("bls12-381.fr"::Element, Rng<"bls12-381.fr">) {
    let (value, after) = random::draw::<"bls12-381.fr">(coins);
    return (value, after);
  }

  protocol Attempt {
    roles (P, V);
    inputs (P coins: Rng<"bls12-381.fr">, P retry: bool);
    outputs (P Rng<"bls12-381.fr">, P bool);
    local P: let (value, after) = Draw(coins);
    message candidate: P(value) -> V(received);
    return (after, retry);
  }

  instance Main: Attempt { roles (P = P, V = V); }
  entry main = Main;
}

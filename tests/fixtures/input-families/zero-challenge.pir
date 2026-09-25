// Retry evidence body, not a complete BP+ proof. The test-only host fault
// oracle replaces a real Monero update result; this source has no retry input.
module {
  fn Draw(coins: Rng<"bls12-381.fr">)
      -> ("bls12-381.fr"::Element, Rng<"bls12-381.fr">) {
    let (value, after) = random::draw::<"bls12-381.fr">(coins);
    return (value, after);
  }

  fn Challenge(state: Indices, items: Indices) -> (Indices, Indices, bool) {
    let (next, challenge) = external::monero::update(state, items);
    let mut zero = true;
    for i in 0..challenge.len() {
      if index::equal(challenge[i], 0) {
      } else {
        zero = false;
      }
    }
    return (next, challenge, zero);
  }

  protocol Attempt {
    roles (P, V);
    inputs (P coins: Rng<"bls12-381.fr">, P state: Indices, P items: Indices);
    outputs (P Rng<"bls12-381.fr">, P Indices, P Indices, P bool);
    local P: let (value, after) = Draw(coins);
    message candidate: P(value) -> V(received);
    local P: let (next, challenge, retry) = Challenge(state, items);
    return (after, next, challenge, retry);
  }

  instance Main: Attempt { roles (P = P, V = V); }
  entry main = Main;
}

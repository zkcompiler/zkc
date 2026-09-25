module {
  fn Select(n: index) -> index { return n; }
  fn Work<F: domain Field>(x: F::Element, coins: Rng<F>) -> (F::Element, Rng<F>) requires (Field(F)) {
    [draw] let (sample, next_coins) = random::draw::<F>(coins);
    [double] let next = field::add::<F>(x, x);
    return (next, next_coins);
  }
  configure WorkField = Work(F = bls12-381.fr);
  protocol Family {
    roles (P, V);
    parameters (rounds);
    inputs (P pn: index, P witness: bls12-381.fr::Element,
            P coins: Rng<"bls12-381.fr">, V vn: index, V initial: bls12-381.fr::Element);
    outputs (P bls12-381.fr::Element, P Rng<"bls12-381.fr">, V bls12-381.fr::Element);
    loop [round] rounds carry (x = witness, rng = coins, y = initial) -> (out, after, seen) {
      local [work] P: let (next, next_rng) = WorkField(x, rng);
      message [value] field: P(next) -> V(got);
      yield (next, next_rng, got);
    }
    return (out, after, seen);
  }
  instance Main: Family {
    parameters (rounds = ingress(10, P = Select(pn), V = Select(vn)));
    roles (P = P, V = V);
  }
  entry main = Main;
}

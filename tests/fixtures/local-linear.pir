module {
  bind draw = random::draw(bls12-381.fr);
  bind require = control::require();
  bind fold = poly::fold(bls12-381.fr);
  fn Draw(rng: Rng<"bls12-381.fr">) -> ("bls12-381.fr"::Element, Rng<"bls12-381.fr">) {
    [draw] let (challenge, next) = draw(rng);
    return (challenge, next);
  }

  fn Guard(allowed: bool) -> () {
    [require] require(allowed);
    return;
  }

  fn Fold(table: Table<"bls12-381.fr">, challenge: "bls12-381.fr"::Element) -> Table<"bls12-381.fr"> {
    [fold] let result = fold(table, challenge);
    return result;
  }

  fn Step(
    rng: Rng<"bls12-381.fr">,
    table: Table<"bls12-381.fr">,
    allowed: bool
  ) -> (Table<"bls12-381.fr">, Rng<"bls12-381.fr">) {
    [draw] let (challenge, next) = Draw(rng);
    [check] Guard(allowed);
    [first] let one = Fold(table, challenge);
    [second] let two = Fold(one, challenge);
    return (two, next);
  }

  protocol OneStep {
    roles (P);
    inputs (P rng: Rng<"bls12-381.fr">, P table: Table<"bls12-381.fr">, P allowed: bool);
    outputs (P Table<"bls12-381.fr">, P Rng<"bls12-381.fr">);
    local [step] P: let (result, next) = Step(rng, table, allowed);
    return (result, next);
  }

  instance concrete: OneStep {
    roles (P = P);
  }

  entry main = concrete;
}

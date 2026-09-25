module {
  fn Step<F: domain Field>(rng: Rng<F>, table: Table<F>, allowed: bool) -> (Table<F>, Rng<F>) requires (
    Field(F)
  ) {
    [draw] let (r, next) = random::draw::<F>(rng);
    [guard] control::require(allowed);
    [fold] let result = poly::fold::<F>(table, r);
    return (result, next);
  }

  configure StepMsb = Step(F = bls12-381.fr) using (fold = "arkworks-msb/poly.fold");
  protocol OneStep {
    roles (P);
    inputs (P rng: Rng<"bls12-381.fr">, P table: Table<"bls12-381.fr">, P allowed: bool);
    outputs (P Table<"bls12-381.fr">, P Rng<"bls12-381.fr">);
    local [step] P: let (result, next) = StepMsb(rng, table, allowed);
    return (result, next);
  }

  instance concrete: OneStep {
    roles (P = P);
  }

  entry main = concrete;
}

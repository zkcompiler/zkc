use zkc::algebra::{
  Field
};
use zkc::core;
use zkc::poly::{
  Table
};
use zkc::poly;
use zkc::random::{
  Rng
};
use zkc::random;
fn Step<F: domain Field>(rng: Rng<F>, table: Table<F>, allowed: bool) -> (Table<F>, Rng<F>) requires (
  Field(F)
) {
  [draw] let (r, next) = zkc::random::draw::<F>(rng);
  [guard] zkc::core::require(allowed);
  [r#fold] let result = zkc::poly::r#fold::<F>(table, r);
  return (result, next);
}

configure StepMsb = Step(F = "bls12-381.fr") using (r#fold = "arkworks-msb/poly.fold");
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

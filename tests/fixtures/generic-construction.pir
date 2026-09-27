use zkc::algebra::{
  Field
};
use zkc::algebra;
use zkc::core;
use zkc::random::{
  Rng
};
use zkc::random;
fn Draw<F: domain Field>(r: Rng<F>) -> (F::Element, Rng<F>) requires (Field(F)) {
  [sample] let (x, next) = zkc::random::draw::<F>(r);
  return (x, next);
}

fn Two<F: domain Field>(r: Rng<F>) -> (F::Element, Rng<F>) requires (Field(F)) {
  [first] let (a, r1) = SelectedDraw::<F>(r);
  [second] let (b, r2) = Draw::<F>(r1);
  return (b, r2);
}

fn Check<F: domain Field>(x: F::Element) -> bool requires (Field(F)) {
  [equal] let ok = zkc::algebra::equal::<F>(x, x);
  [guard] zkc::core::require(ok);
  return ok;
}

configure SelectedDraw = Draw();
configure DrawTwo = Two(F = "bls12-381.fr");
configure CheckField = Check(F = "bls12-381.fr");
protocol Main {
  roles (P, V);
  inputs (V coins: Rng<"bls12-381.fr">);
  outputs (V bool, V Rng<"bls12-381.fr">);
  local [draw] V: let (x, r2) = DrawTwo(coins);
  message [sample] field: V(x) -> P(seen);
  local [check] V: let ok = CheckField(x);
  return (ok, r2);
}

instance concrete: Main {
  roles (P = P, V = V);
}

entry main = concrete;

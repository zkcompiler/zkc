use zkc::curve::{
  ScalarAction
};
use zkc::algebra::{
  Field,
  Vector
};
use zkc::core;
use zkc::curve;
use zkc::random::{
  Nonce
};
fn Commit<G: domain Group>(
  bases: Vector<G::Element>,
  nonce: Nonce<G::Scalar>
) -> (Vector<G::Element>, Nonce<G::Scalar>) requires (ScalarAction(G)) {
  [commit] let (commitments, ready) = zkc::curve::commit::<G>(bases, nonce);
  return (commitments, ready);
}

fn Respond<F: domain Field>(secret: F::Element, challenge: F::Element, ready: Nonce<F>) -> F::Element requires (
  Field(F)
) {
  [respond] let response = zkc::curve::response::<F>(secret, challenge, ready);
  return response;
}

fn Guard<>(allowed: bool) -> () {
  [guard] zkc::core::require(allowed);
  return;
}

configure Commitment = Commit(G = "bls12-381.g1");
configure Response = Respond(F = "bls12-381.fr");
configure Require = Guard();
protocol NonceResponse {
  roles (P);
  inputs (
    P bases: Vector<"bls12-381.g1"::Element>,
    P nonce: Nonce<"bls12-381.fr">,
    P secret: "bls12-381.fr"::Element,
    P challenge: "bls12-381.fr"::Element,
    P before: bool,
    P after: bool
  );
  outputs (P Vector<"bls12-381.g1"::Element>, P "bls12-381.fr"::Element);
  local [before] P: Require(before);
  local [commit] P: let (commitments, ready) = Commitment(bases, nonce);
  local [after] P: Require(after);
  local [respond] P: let response = Response(secret, challenge, ready);
  return (commitments, response);
}

instance concrete: NonceResponse {
  roles (P = P);
}

entry main = concrete;

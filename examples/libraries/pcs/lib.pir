// Ordinary multilinear KZG checking. Native CheckedIndex never enters PIR.
module {
  use zkc::core;
  use zkc::pcs::{Commitment, MultilinearOpening, Proof, VerifierKey};
  use zkc::pcs;
  use zkc::poly::{Point};
  library(namespace="zkc.examples", name="pcs", version="1", resolution="source-v1");
  pub fn Check<C: domain Commitment>(key: VerifierKey<C>, root: Commitment<C>,
      point: Point<C::PointField>, value: C::EvaluationField::Element, proof: Proof<C>)
      -> bool requires (MultilinearOpening(C)) {
    [opening] let accepted = zkc::pcs::check::<C>(key, root, point, value, proof);
    [require] zkc::core::require(accepted);
    return accepted;
  }
  pub configure CheckIndexOpening = Check(C = "multilinear.kzg.bls12-381/1");
}

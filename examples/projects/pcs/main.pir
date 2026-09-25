// Host premise: key, commitment and opening belong to the exact checked index
// for the independently selected relation, layout, encoding and dimensions.
// This protocol checks only an ordinary KZG opening, not that host premise.
module {
  dependency pcs = library(namespace="zkc.examples", name="pcs", version="1", resolution="source-v1");
  use pcs::CheckIndexOpening;
  protocol IndexOpening {
    roles (V);
    inputs (V key: VerifierKey<"multilinear.kzg.bls12-381/1">,
            V root: Commitment<"multilinear.kzg.bls12-381/1">,
            V point: Point<"bls12-381.fr">,
            V value: "bls12-381.fr"::Element,
            V proof: Proof<"multilinear.kzg.bls12-381/1">);
    outputs (V bool);
    local [check] V: let accepted = CheckIndexOpening(key, root, point, value, proof);
    return accepted;
  }
  instance run: IndexOpening { roles (V = V); }
  entry main = run;
}

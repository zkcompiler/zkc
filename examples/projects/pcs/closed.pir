// Independently authored concrete opening checker; no importer or generic API.
module {
  fn Verify(key: VerifierKey<"multilinear.kzg.bls12-381/1">,
      root: Commitment<"multilinear.kzg.bls12-381/1">,
      point: Point<"bls12-381.fr">, value: "bls12-381.fr"::Element,
      proof: Proof<"multilinear.kzg.bls12-381/1">) -> bool {
    [opening] let accepted = pcs::check::<"multilinear.kzg.bls12-381/1">(key, root, point, value, proof);
    [require] control::require(accepted);
    return accepted;
  }
  protocol Direct {
    roles (V);
    inputs (V key: VerifierKey<"multilinear.kzg.bls12-381/1">,
            V root: Commitment<"multilinear.kzg.bls12-381/1">,
            V point: Point<"bls12-381.fr">,
            V value: "bls12-381.fr"::Element,
            V proof: Proof<"multilinear.kzg.bls12-381/1">);
    outputs (V bool);
    local [check] V: let accepted = Verify(key, root, point, value, proof);
    return accepted;
  }
  instance run: Direct { roles (V = V); }
  entry main = run;
}

module {
  fn Verify<C: domain Commitment>(
    key: VerifierKey<C>,
    commitment: Commitment<C>,
    point: Point<C::PointField>,
    value: C::EvaluationField::Element,
    proof: Proof<C>
  ) -> bool requires (MultilinearOpening(C)) {
    [check] let accepted = pcs::check::<C>(key, commitment, point, value, proof);
    return accepted;
  }

  configure VerifyOpening = Verify(C = "multilinear.kzg.bls12-381/1");
  protocol Opening {
    roles (V);
    inputs (
      V key: VerifierKey<"multilinear.kzg.bls12-381/1">,
      V commitment: Commitment<"multilinear.kzg.bls12-381/1">,
      V point: Point<"bls12-381.fr">,
      V value: "bls12-381.fr"::Element,
      V proof: Proof<"multilinear.kzg.bls12-381/1">
    );
    outputs (V bool);
    local [verify] V: let accepted = VerifyOpening(key, commitment, point, value, proof);
    return accepted;
  }

  instance concrete: Opening {
    roles (V = V);
  }

  entry main = concrete;
}

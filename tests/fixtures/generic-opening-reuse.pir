module {
  fn Commit<C: domain Commitment>(
    key: ProverKey<C>,
    table: Table<C::ValueField>
  ) -> (Commitment<C>, OpeningState<C>) requires (MultilinearOpening(C)) {
    [commit] let (public, original) = pcs::commit::<C>(key, table);
    return (public, original);
  }

  fn Open<C: domain Commitment>(
    original: OpeningState<C>,
    point: Point<C::PointField>
  ) -> (C::EvaluationField::Element, Proof<C>) requires (MultilinearOpening(C)) {
    [open] let (value, proof) = pcs::open::<C>(original, point);
    return (value, proof);
  }

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

  fn Fold<F: domain Field>(table: Table<F>, point: F::Element) -> Table<F> requires (CommRing(F)) {
    [fold] let scratch = poly::fold::<F>(table, point);
    return scratch;
  }

  configure Commitment = Commit(C = "multilinear.kzg.bls12-381/1");
  configure Opening = Open(C = "multilinear.kzg.bls12-381/1");
  configure Check = Verify(C = "multilinear.kzg.bls12-381/1");
  configure Scratch = Fold(F = bls12-381.fr) using (fold = "arkworks-msb/poly.fold");
  protocol RepeatedOpening {
    roles (P);
    inputs (
      P key: ProverKey<"multilinear.kzg.bls12-381/1">,
      P verifier: VerifierKey<"multilinear.kzg.bls12-381/1">,
      P table: Table<"bls12-381.fr">,
      P first: Point<"bls12-381.fr">,
      P second: Point<"bls12-381.fr">,
      P r: "bls12-381.fr"::Element
    );
    outputs (
      P "bls12-381.fr"::Element,
      P "bls12-381.fr"::Element,
      P bool,
      P bool,
      P Table<"bls12-381.fr">
    );
    local [commit] P: let (commitment, original) = Commitment(key, table);
    local [first] P: let (a, pa) = Opening(original, first);
    local [scratch] P: let scratch = Scratch(table, r);
    local [second] P: let (b, pb) = Opening(original, second);
    local [verify_first] P: let a_ok = Check(verifier, commitment, first, a, pa);
    local [verify_second] P: let b_ok = Check(verifier, commitment, second, b, pb);
    return (a, b, a_ok, b_ok, scratch);
  }

  instance concrete: RepeatedOpening {
    roles (P = P);
  }

  entry main = concrete;
}

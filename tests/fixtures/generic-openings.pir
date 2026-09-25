module {
  fn Prove<C: domain Commitment>(
    key: ProverKey<C>,
    table: Table<C::ValueField>,
    point: Point<C::PointField>
  ) -> (Commitment<C>, C::EvaluationField::Element, Proof<C>) requires (MultilinearOpening(C)) {
    [commit] let (commitment, state) = pcs::commit::<C>(key, table);
    [open] let (value, proof) = pcs::open::<C>(state, point);
    return (commitment, value, proof);
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

  configure Prover = Prove(C = "multilinear.kzg.bls12-381/1");
  configure Verifier = Verify(C = "multilinear.kzg.bls12-381/1");
  // Setup identity and rank belong to each dynamic instance's inputs. Sharing
  // the same closed algorithm does not identify its keys or committed originals.
  protocol TwoOpenings {
    roles (P, V);
    inputs (
      P ka: ProverKey<"multilinear.kzg.bls12-381/1">,
      P kb: ProverKey<"multilinear.kzg.bls12-381/1">,
      P a: Table<"bls12-381.fr">,
      P b: Table<"bls12-381.fr">,
      V va: VerifierKey<"multilinear.kzg.bls12-381/1">,
      V vb: VerifierKey<"multilinear.kzg.bls12-381/1">,
      V ra: Point<"bls12-381.fr">,
      V rb: Point<"bls12-381.fr">
    );
    outputs (V bool, V bool);
    message [query_a] query: V(ra) -> P(pa);
    message [query_b] query: V(rb) -> P(pb);
    local [prove_a] P: let (ca, ya, oa) = Prover(ka, a, pa);
    local [prove_b] P: let (cb, yb, ob) = Prover(kb, b, pb);
    message [commit_a] commitment: P(ca) -> V(cva);
    message [value_a] evaluation: P(ya) -> V(yva);
    message [proof_a] opening: P(oa) -> V(ova);
    message [commit_b] commitment: P(cb) -> V(cvb);
    message [value_b] evaluation: P(yb) -> V(yvb);
    message [proof_b] opening: P(ob) -> V(ovb);
    local [check_a] V: let a_ok = Verifier(va, cva, ra, yva, ova);
    local [check_b] V: let b_ok = Verifier(vb, cvb, rb, yvb, ovb);
    return (a_ok, b_ok);
  }

  instance concrete: TwoOpenings {
    roles (P = P, V = V);
  }

  entry main = concrete;
}

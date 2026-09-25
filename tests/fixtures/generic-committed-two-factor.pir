// Generic PCS and polynomial algorithms with explicit MSB folding.
module {
  fn CommitFactorsAlgorithm<C: domain Commitment>(
    key: ProverKey<C>,
    f: Table<C::ValueField>,
    g: Table<C::ValueField>
  ) -> (Commitment<C>, Commitment<C>, OpeningState<C>, OpeningState<C>) requires (
    MultilinearOpening(C)
  ) {
    [commit_f] let (cf, sf) = pcs::commit::<C>(key, f);
    [commit_g] let (cg, sg) = pcs::commit::<C>(key, g);
    return (cf, cg, sf, sg);
  }

  fn EmptyPointAlgorithm<F: domain Field>() -> Point<F> requires (Field(F)) {
    [point] let p = poly::empty_point::<F>();
    return p;
  }

  fn ProductRoundAlgorithm<F: domain Field>(f: Table<F>, g: Table<F>) -> Round<F> requires (
    Field(F)
  ) {
    [round] let q = poly::product_round::<F>(f, g);
    return q;
  }

  fn CheckRoundAndDrawAlgorithm<F: domain Field>(
    q: Round<F>,
    claim: F::Element,
    coins: Rng<F>
  ) -> (F::Element, F::Element, Rng<F>) requires (Field(F)) {
    [boundary] let sum = poly::boundary::<F>(q);
    [equal] let valid = field::equal::<F>(sum, claim);
    [require] control::require(valid);
    [draw] let (r, next_coins) = random::draw::<F>(coins);
    [evaluate] let next_claim = poly::round_evaluate::<F>(q, r);
    return (r, next_claim, next_coins);
  }

  fn FoldFactorsAlgorithm<F: domain Field>(
    f: Table<F>,
    g: Table<F>,
    r: F::Element
  ) -> (Table<F>, Table<F>) requires (Field(F)) {
    [fold_f] let ff = poly::fold::<F>(f, r);
    [fold_g] let gg = poly::fold::<F>(g, r);
    return (ff, gg);
  }

  fn AppendPointAlgorithm<F: domain Field>(p: Point<F>, r: F::Element) -> Point<F> requires (
    Field(F)
  ) {
    [append] let next = poly::append_point::<F>(p, r);
    return next;
  }

  fn OpenFactorAlgorithm<C: domain Commitment>(
    state: OpeningState<C>,
    p: Point<C::PointField>
  ) -> (C::EvaluationField::Element, Proof<C>) requires (MultilinearOpening(C)) {
    [open] let (value, proof) = pcs::open::<C>(state, p);
    return (value, proof);
  }

  fn CheckOpeningAlgorithm<C: domain Commitment>(
    key: VerifierKey<C>,
    commitment: Commitment<C>,
    p: Point<C::PointField>,
    value: C::EvaluationField::Element,
    proof: Proof<C>
  ) -> C::EvaluationField::Element requires (MultilinearOpening(C)) {
    [check] let valid = pcs::check::<C>(key, commitment, p, value, proof);
    [require] control::require(valid);
    return value;
  }

  fn CheckTerminalAlgorithm<F: domain Field>(f: F::Element, g: F::Element, claim: F::Element) -> bool requires (
    Field(F)
  ) {
    [product] let product = field::mul::<F>(f, g);
    [equal] let accepted = field::equal::<F>(product, claim);
    return accepted;
  }

  fn CheckExpectedRootsAlgorithm<C: domain Commitment>(
    actual_f: Commitment<C>,
    actual_g: Commitment<C>,
    expected_f: Commitment<C>,
    expected_g: Commitment<C>
  ) -> () requires (MultilinearOpening(C)) {
    [equal_f] let f_ok = pcs::equal::<C>(actual_f, expected_f);
    [require_f] control::require(f_ok);
    [equal_g] let g_ok = pcs::equal::<C>(actual_g, expected_g);
    [require_g] control::require(g_ok);
    return;
  }

  configure CommitFactors = CommitFactorsAlgorithm(C = "multilinear.kzg.bls12-381/1");
  configure EmptyPoint = EmptyPointAlgorithm(F = bls12-381.fr);
  configure ProductRound = ProductRoundAlgorithm(F = bls12-381.fr);
  configure CheckRoundAndDraw = CheckRoundAndDrawAlgorithm(F = bls12-381.fr);
  configure FoldFactors = FoldFactorsAlgorithm(F = bls12-381.fr) using (
    fold_f = "arkworks-msb/poly.fold",
    fold_g = "arkworks-msb/poly.fold"
  );
  configure AppendPoint = AppendPointAlgorithm(F = bls12-381.fr);
  configure OpenFactor = OpenFactorAlgorithm(C = "multilinear.kzg.bls12-381/1");
  configure CheckOpening = CheckOpeningAlgorithm(C = "multilinear.kzg.bls12-381/1");
  configure CheckTerminal = CheckTerminalAlgorithm(F = bls12-381.fr);
  configure CheckExpectedRoots = CheckExpectedRootsAlgorithm(C = "multilinear.kzg.bls12-381/1");
  protocol ProductSumcheck {
    roles (P, V);
    parameters (n);
    inputs (
      P f: Table<"bls12-381.fr">,
      P g: Table<"bls12-381.fr">,
      V claim: "bls12-381.fr"::Element,
      V coins: Rng<"bls12-381.fr">
    );
    outputs (
      P Point<"bls12-381.fr">,
      V Point<"bls12-381.fr">,
      V "bls12-381.fr"::Element,
      V Rng<"bls12-381.fr">
    );
    local [init_p] P: let pp = EmptyPoint();
    local [init_v] V: let vp = EmptyPoint();
    loop [rounds] n carry (
      left = f,
      right = g,
      p_point = pp,
      v_point = vp,
      current = claim,
      random = coins
    ) -> (residual_f, residual_g, p_end, v_end, claim_end, coins_end) {
      local [make_round] P: let q = ProductRound(left, right);
      message [round_message] quadratic: P(q) -> V(received_q);
      local [check_and_draw] V: let (challenge, next_claim, next_random) = CheckRoundAndDraw(
        received_q,
        current,
        random
      );
      message [challenge_message] challenge: V(challenge) -> P(received_r);
      local [fold] P: let (next_f, next_g) = FoldFactors(left, right, received_r);
      local [append_p] P: let next_p = AppendPoint(p_point, received_r);
      local [append_v] V: let next_v = AppendPoint(v_point, challenge);
      yield (next_f, next_g, next_p, next_v, next_claim, next_random);
    }
    return (p_end, v_end, claim_end, coins_end);
  }

  protocol FactorOpening {
    roles (P, V);
    inputs (
      P state: OpeningState<"multilinear.kzg.bls12-381/1">,
      P p_point: Point<"bls12-381.fr">,
      V vk: VerifierKey<"multilinear.kzg.bls12-381/1">,
      V root: Commitment<"multilinear.kzg.bls12-381/1">,
      V v_point: Point<"bls12-381.fr">
    );
    outputs (V "bls12-381.fr"::Element);
    local [make_opening] P: let (evaluation, proof) = OpenFactor(state, p_point);
    message [evaluation_message] evaluation: P(evaluation) -> V(received_value);
    message [proof_message] opening: P(proof) -> V(received_proof);
    local [check_opening] V: let checked_value = CheckOpening(
      vk,
      root,
      v_point,
      received_value,
      received_proof
    );
    return checked_value;
  }

  protocol CommittedTwoFactorArgument {
    roles (P, V);
    parameters (n);
    inputs (
      P pk: ProverKey<"multilinear.kzg.bls12-381/1">,
      P f: Table<"bls12-381.fr">,
      P g: Table<"bls12-381.fr">,
      V vk: VerifierKey<"multilinear.kzg.bls12-381/1">,
      V claim: "bls12-381.fr"::Element,
      V coins: Rng<"bls12-381.fr">,
      V expected_f: Commitment<"multilinear.kzg.bls12-381/1">,
      V expected_g: Commitment<"multilinear.kzg.bls12-381/1">
    );
    outputs (V bool, V Rng<"bls12-381.fr">);
    dependencies (sumcheck: ProductSumcheck(n = n), opening: FactorOpening());
    local [commit_factors] P: let (cf, cg, sf, sg) = CommitFactors(pk, f, g);
    message [root_f] commitment: P(cf) -> V(root_f);
    message [root_g] commitment: P(cg) -> V(root_g);
    local [check_expected_roots] V: CheckExpectedRoots(root_f, root_g, expected_f, expected_g);
    invoke [sumcheck_call] sumcheck(
      f,
      g,
      claim,
      coins
    ) -> (p_point, v_point, terminal_claim, next_coins);
    invoke [open_f] opening(sf, p_point, vk, root_f, v_point) -> (f_value);
    invoke [open_g] opening(sg, p_point, vk, root_g, v_point) -> (g_value);
    local [terminal] V: let accepted = CheckTerminal(f_value, g_value, terminal_claim);
    return (accepted, next_coins);
  }

  instance sumcheck: ProductSumcheck {
    parameters (n = 3);
    roles (P = P, V = V);
  }

  instance opening: FactorOpening {
    roles (P = P, V = V);
  }

  instance interactive: CommittedTwoFactorArgument {
    parameters (n = 3);
    dependencies (sumcheck = sumcheck, opening = opening);
    roles (P = P, V = V);
  }

  entry main = interactive;
}

// Product Sumcheck with openings of two prover-selected committed tables.
// Use committed-two-factor.pir when the validator must pin expected roots.
module {
  bind pcs.commit = pcs::commit("multilinear.kzg.bls12-381/1") using "arkworks/pcs.commit";
  bind poly.empty_point = poly::empty_point(bls12-381.fr) using "arkworks/poly.empty_point";
  bind poly.product_round = poly::product_round(bls12-381.fr) using "arkworks/poly.product_round";
  bind poly.boundary = poly::boundary(bls12-381.fr) using "arkworks/poly.boundary";
  bind field.equal = field::equal(bls12-381.fr) using "arkworks/field.equal";
  bind control.require = control::require() using "arkworks/control.require";
  bind random.draw = random::draw(bls12-381.fr) using "arkworks/random.draw";
  bind poly.round_evaluate = poly::round_evaluate(bls12-381.fr) using "arkworks/poly.round_evaluate";
  bind poly.fold = poly::fold(bls12-381.fr) using "arkworks/poly.fold";
  bind poly.append_point = poly::append_point(bls12-381.fr) using "arkworks/poly.append_point";
  bind pcs.open = pcs::open("multilinear.kzg.bls12-381/1") using "arkworks/pcs.open";
  bind pcs.check = pcs::check("multilinear.kzg.bls12-381/1") using "arkworks/pcs.check";
  bind field.mul = field::mul(bls12-381.fr) using "arkworks/field.mul";
  fn CommitFactors(
    key: ProverKey<"multilinear.kzg.bls12-381/1">,
    f: Table<"bls12-381.fr">,
    g: Table<"bls12-381.fr">
  ) -> (
    Commitment<"multilinear.kzg.bls12-381/1">,
    Commitment<"multilinear.kzg.bls12-381/1">,
    OpeningState<"multilinear.kzg.bls12-381/1">,
    OpeningState<"multilinear.kzg.bls12-381/1">
  ) {
    [commit_f] let (cf, sf) = pcs.commit(key, f);
    [commit_g] let (cg, sg) = pcs.commit(key, g);
    return (cf, cg, sf, sg);
  }

  fn EmptyPoint() -> Point<"bls12-381.fr"> {
    [point] let p = poly.empty_point();
    return p;
  }

  fn ProductRound(f: Table<"bls12-381.fr">, g: Table<"bls12-381.fr">) -> Round<"bls12-381.fr"> {
    [round] let q = poly.product_round(f, g);
    return q;
  }

  fn CheckRoundAndDraw(
    q: Round<"bls12-381.fr">,
    claim: "bls12-381.fr"::Element,
    coins: Rng<"bls12-381.fr">
  ) -> ("bls12-381.fr"::Element, "bls12-381.fr"::Element, Rng<"bls12-381.fr">) {
    [boundary] let sum = poly.boundary(q);
    [equal] let valid = field.equal(sum, claim);
    [require] control.require(valid);
    [draw] let (r, next_coins) = random.draw(coins);
    [evaluate] let next_claim = poly.round_evaluate(q, r);
    return (r, next_claim, next_coins);
  }

  fn FoldFactors(
    f: Table<"bls12-381.fr">,
    g: Table<"bls12-381.fr">,
    r: "bls12-381.fr"::Element
  ) -> (Table<"bls12-381.fr">, Table<"bls12-381.fr">) {
    [fold_f] let ff = poly.fold(f, r);
    [fold_g] let gg = poly.fold(g, r);
    return (ff, gg);
  }

  fn AppendPoint(p: Point<"bls12-381.fr">, r: "bls12-381.fr"::Element) -> Point<"bls12-381.fr"> {
    [append] let next = poly.append_point(p, r);
    return next;
  }

  fn OpenFactor(
    state: OpeningState<"multilinear.kzg.bls12-381/1">,
    p: Point<"bls12-381.fr">
  ) -> ("bls12-381.fr"::Element, Proof<"multilinear.kzg.bls12-381/1">) {
    [open] let (value, proof) = pcs.open(state, p);
    return (value, proof);
  }

  fn CheckOpening(
    key: VerifierKey<"multilinear.kzg.bls12-381/1">,
    commitment: Commitment<"multilinear.kzg.bls12-381/1">,
    p: Point<"bls12-381.fr">,
    value: "bls12-381.fr"::Element,
    proof: Proof<"multilinear.kzg.bls12-381/1">
  ) -> "bls12-381.fr"::Element {
    [check] let valid = pcs.check(key, commitment, p, value, proof);
    [require] control.require(valid);
    return value;
  }

  fn CheckTerminal(
    f: "bls12-381.fr"::Element,
    g: "bls12-381.fr"::Element,
    claim: "bls12-381.fr"::Element
  ) -> bool {
    [product] let product = field.mul(f, g);
    [equal] let accepted = field.equal(product, claim);
    return accepted;
  }

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

  protocol TwoFactorArgument {
    roles (P, V);
    parameters (n);
    inputs (
      P pk: ProverKey<"multilinear.kzg.bls12-381/1">,
      P f: Table<"bls12-381.fr">,
      P g: Table<"bls12-381.fr">,
      V vk: VerifierKey<"multilinear.kzg.bls12-381/1">,
      V claim: "bls12-381.fr"::Element,
      V coins: Rng<"bls12-381.fr">
    );
    outputs (V bool, V Rng<"bls12-381.fr">);
    dependencies (sumcheck: ProductSumcheck(n = n), opening: FactorOpening());
    local [commit_factors] P: let (cf, cg, sf, sg) = CommitFactors(pk, f, g);
    message [root_f] commitment: P(cf) -> V(root_f);
    message [root_g] commitment: P(cg) -> V(root_g);
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

  instance interactive: TwoFactorArgument {
    parameters (n = 3);
    dependencies (sumcheck = sumcheck, opening = opening);
    roles (P = P, V = V);
  }

  entry main = interactive;
}

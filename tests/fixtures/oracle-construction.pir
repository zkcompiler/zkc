module {
  fn Commit<C: domain Commitment>(
    values: Vector<C::ValueField::Element>,
    width: index
  ) -> (Commitments<C>, OpeningStates<C>) requires (VectorCommitment(C)) {
    [__site_0] let (root, state) = oracle::commit::<C>(values, width);
    [__site_1] let empty_roots = commitments::empty::<C>();
    [__site_2] let roots = commitments::append::<C>(empty_roots, root);
    [__site_3] let empty_states = opening_states::empty::<C>();
    [__site_4] let states = opening_states::append::<C>(empty_states, state);
    return (roots, states);
  }

  fn Open<C: domain Commitment>(
    states: OpeningStates<C>,
    query: index
  ) -> (Vector<C::ValueField::Element>, Proof<C>) requires (VectorCommitment(C)) {
    [__site_0] let zero = index::constant() attributes ("0");
    [__site_1] let state = opening_states::at::<C>(states, zero);
    [__site_2] let (row, path) = oracle::open::<C>(state, query);
    return (row, path);
  }

  fn Check<C: domain Commitment>(
    roots: Commitments<C>,
    width: index,
    height: index,
    query: index,
    row: Vector<C::ValueField::Element>,
    path: Proof<C>
  ) -> bool requires (VectorCommitment(C)) {
    [__site_0] let zero = index::constant() attributes ("0");
    [__site_1] let root = commitments::at::<C>(roots, zero);
    [__site_2] let valid = oracle::check::<C>(root, width, height, query, row, path);
    [__site_3] control::require(valid);
    return valid;
  }

  fn Challenge<E: domain Field>(r: Rng<E>) -> (E::Element, Rng<E>) requires (Field(E)) {
    [draw] let (c, next) = random::draw::<E>(r);
    return (c, next);
  }

  fn Query<E: domain Field>(r: Rng<E>, bound: index) -> (index, Rng<E>) requires (
    IndexRandomness(E)
  ) {
    [draw] let (i, next) = random::index::<E>(r, bound);
    return (i, next);
  }

  configure CommitRows = Commit(C = "rows.merkle-keccak256.koala-bear/1");
  configure OpenRow = Open(C = "rows.merkle-keccak256.koala-bear/1");
  configure CheckRow = Check(C = "rows.merkle-keccak256.koala-bear/1");
  configure Draw = Challenge(E = koala-bear.ext8-binomial3);
  configure Select = Query(E = koala-bear.ext8-binomial3);
  protocol Main {
    roles (P, V);
    inputs (
      P values: Vector<koala-bear::Element>,
      P width: index,
      V expected_width: index,
      V expected_height: index,
      V coins: Rng<"koala-bear.ext8-binomial3">
    );
    outputs (
      V bool,
      V Commitments<"rows.merkle-keccak256.koala-bear/1">,
      V Vector<koala-bear::Element>,
      V Proof<"rows.merkle-keccak256.koala-bear/1">
    );
    local [__site_0] P: let (roots, states) = CommitRows(values, width);
    message [__site_1] roots: P(roots) -> V(received_roots);
    local [__site_2] V: let (beta, rng1) = Draw(coins);
    message [__site_3] beta: V(beta) -> P(p_beta);
    local [__site_4] V: let (selected, rng2) = Select(rng1, expected_height);
    message [__site_5] index: V(selected) -> P(query);
    local [__site_6] P: let (row, path) = OpenRow(states, query);
    message [__site_7] row: P(row) -> V(received_row);
    message [__site_8] path: P(path) -> V(received_path);
    local [__site_9] V: let valid = CheckRow(
      received_roots,
      expected_width,
      expected_height,
      selected,
      received_row,
      received_path
    );
    return (valid, received_roots, received_row, received_path);
  }

  instance concrete: Main {
    roles (P = P, V = V);
  }

  entry main = concrete;
}

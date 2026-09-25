module {
  fn Commit<C: domain Commitment>(
    values: Vector<C::ValueField::Element>,
    width: index
  ) -> (Commitment<C>, OpeningState<C>) requires (VectorCommitment(C)) {
    [__site_0] let (root, state) = oracle::commit::<C>(values, width);
    return (root, state);
  }

  fn Open<C: domain Commitment>(
    state: OpeningState<C>,
    query: index
  ) -> (Vector<C::ValueField::Element>, Proof<C>) requires (VectorCommitment(C)) {
    [__site_0] let (row, path) = oracle::open::<C>(state, query);
    return (row, path);
  }

  fn Check<C: domain Commitment>(
    root: Commitment<C>,
    width: index,
    height: index,
    query: index,
    row: Vector<C::ValueField::Element>,
    path: Proof<C>
  ) -> bool requires (VectorCommitment(C)) {
    [__site_0] let ok = oracle::check::<C>(root, width, height, query, row, path);
    [__site_1] control::require(ok);
    return ok;
  }

  fn Draw<E: domain Field>(coins: Rng<E>, bound: index) -> (index, Rng<E>) requires (
    IndexRandomness(E)
  ) {
    [draw] let (value, after) = random::index::<E>(coins, bound);
    return (value, after);
  }

  configure CommitRows = Commit(C = "rows.merkle-keccak256.koala-bear/1");
  configure OpenRow = Open(C = "rows.merkle-keccak256.koala-bear/1");
  configure CheckRow = Check(C = "rows.merkle-keccak256.koala-bear/1");
  configure DrawIndex = Draw(E = koala-bear.ext8-binomial3);
  protocol Main {
    roles (P, V);
    inputs (
      P values: Vector<koala-bear::Element>,
      P width: index,
      V height: index,
      V expected_width: index,
      V coins: Rng<"koala-bear.ext8-binomial3">
    );
    outputs (V bool);
    local [__site_0] P: let (root, state) = CommitRows(values, width);
    message [__site_1] root: P(root) -> V(received_root);
    local [__site_2] V: let (query, after) = DrawIndex(coins, height);
    message [__site_3] query: V(query) -> P(received_query);
    local [__site_4] P: let (row, path) = OpenRow(state, received_query);
    message [__site_5] row: P(row) -> V(received_row);
    message [__site_6] path: P(path) -> V(received_path);
    local [__site_7] V: let ok = CheckRow(
      received_root,
      expected_width,
      height,
      query,
      received_row,
      received_path
    );
    return ok;
  }

  instance concrete: Main {
    roles (P = P, V = V);
  }

  entry main = concrete;
}

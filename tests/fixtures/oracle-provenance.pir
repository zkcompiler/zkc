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

  fn Draw<D: domain Transcript>(coins: Transcript<D>, bound: index) -> (index, Transcript<D>) requires (
    IndexTranscript(D)
  ) {
    [__site_0] let (value, after) = transcript::draw_index::<D>(coins, bound) attributes (
      oracle-query,
      main,
      query,
      V,
      index
    );
    return (value, after);
  }

  fn Observe<T: domain Transcript, C: domain Commitment, E: domain Codec>(
    coins: Transcript<T>,
    root: Commitment<C>
  ) -> Transcript<T> requires (Transcript(T), Encodes.commitment(E, C)) {
    [__site_0] let after = transcript::observe::commitment::<T, C, E>(coins, root) attributes (
      oracle-query,
      main,
      root,
      P,
      V
    );
    return after;
  }

  fn One<>() -> index {
    [__site_0] let n = index::constant() attributes ("1");
    return n;
  }

  fn Zero<>() -> index {
    [__site_0] let n = index::constant() attributes ("0");
    return n;
  }

  fn Mod<>(value: index, modulus: index) -> index {
    [__site_0] let n = index::mod(value, modulus);
    return n;
  }

  fn Singleton<C: domain Commitment>(root: Commitment<C>) -> Commitments<C> requires (
    VectorCommitment(C)
  ) {
    [__site_0] let empty = commitments::empty::<C>();
    [__site_1] let roots = commitments::append::<C>(empty, root);
    return roots;
  }

  fn Length<C: domain Commitment>(roots: Commitments<C>) -> index requires (VectorCommitment(C)) {
    [__site_0] let n = commitments::length::<C>(roots);
    return n;
  }

  fn First<C: domain Commitment>(roots: Commitments<C>) -> Commitment<C> requires (
    VectorCommitment(C)
  ) {
    [__site_0] let zero = index::constant() attributes ("0");
    [__site_1] let root = commitments::at::<C>(roots, zero);
    return root;
  }

  fn ObserveIndex<T: domain Transcript, E: domain Codec>(coins: Transcript<T>, value: index) -> Transcript<T> requires (
    Transcript(T),
    Encodes.index(E)
  ) {
    [__site_0] let after = transcript::observe::index::<T, E>(coins, value) attributes (
      oracle-query,
      main,
      statistic,
      P,
      V
    );
    return after;
  }

  fn ObserveList<T: domain Transcript, C: domain Commitment, E: domain Codec>(
    coins: Transcript<T>,
    roots: Commitments<C>
  ) -> Transcript<T> requires (Transcript(T), Encodes.commitments(E, C)) {
    [__site_0] let after = transcript::observe::commitments::<T, C, E>(coins, roots) attributes (
      oracle-query,
      main,
      roots,
      P,
      V
    );
    return after;
  }

  configure CommitRows = Commit(C = "rows.merkle-keccak256.koala-bear/1");
  configure OpenRow = Open(C = "rows.merkle-keccak256.koala-bear/1");
  configure CheckRow = Check(C = "rows.merkle-keccak256.koala-bear/1");
  configure DrawIndex = Draw(D = "merlin3.koala-bear.ext8-binomial3.rejection31le/1");
  configure ObserveRoot = Observe(
    T = "merlin3.koala-bear.ext8-binomial3.rejection31le/1",
    C = "rows.merkle-keccak256.koala-bear/1",
    E = "zkcv.commitment.rows-merkle-keccak256.koala-bear/1"
  );
  configure RootList = Singleton(C = "rows.merkle-keccak256.koala-bear/1");
  configure RootCount = Length(C = "rows.merkle-keccak256.koala-bear/1");
  configure FirstRoot = First(C = "rows.merkle-keccak256.koala-bear/1");
  configure ObserveStatistic = ObserveIndex(
    T = "merlin3.koala-bear.ext8-binomial3.rejection31le/1",
    E = "zkcv.index/1"
  );
  configure ObserveRoots = ObserveList(
    T = "merlin3.koala-bear.ext8-binomial3.rejection31le/1",
    C = "rows.merkle-keccak256.koala-bear/1",
    E = "zkcv.commitments.rows-merkle-keccak256.koala-bear/1"
  );
  configure OneIndex = One();
  configure ZeroIndex = Zero();
  configure ModIndex = Mod();
  protocol Main {
    roles (P, V);
    inputs (
      P values: Vector<koala-bear::Element>,
      P width: index,
      V height: index,
      V expected_width: index,
      V coins: Transcript<"merlin3.koala-bear.ext8-binomial3.rejection31le/1">
    );
    outputs (V bool);
    local [__site_0] P: let (root, state) = CommitRows(values, width);
    message [__site_1] root: P(root) -> V(received_root);
    local [__site_2] V: let observed = ObserveRoot(coins, received_root);
    local [__site_3] V: let (query, after) = DrawIndex(observed, height);
    message [__site_4] query: V(query) -> P(received_query);
    local [__site_5] P: let (row, path) = OpenRow(state, received_query);
    message [__site_6] row: P(row) -> V(received_row);
    message [__site_7] path: P(path) -> V(received_path);
    local [__site_8] V: let ok = CheckRow(
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

module {
  use zkc::algebra::{
    Vector
  };
  use zkc::algebra;
  use zkc::core;
  use zkc::oracle::{
    Commitments,
    OpeningStates,
    VectorCommitment
  };
  use zkc::oracle;
  use zkc::pcs::{
    Proof
  };
  fn Commit<C: domain Commitment>(
    values: Vector<C::ValueField::Element>,
    width: index
  ) -> (Commitments<C>, OpeningStates<C>) requires (VectorCommitment(C)) {
    [__site_0] let (root, state) = zkc::oracle::commit::<C>(values, width);
    [__site_1] let empty_roots = zkc::oracle::commitments_empty::<C>();
    [__site_2] let roots = zkc::oracle::commitments_append::<C>(empty_roots, root);
    [__site_3] let empty_states = zkc::oracle::opening_states_empty::<C>();
    [__site_4] let states = zkc::oracle::opening_states_append::<C>(empty_states, state);
    return (roots, states);
  }

  fn Open<C: domain Commitment>(
    states: OpeningStates<C>,
    query: index
  ) -> (Vector<C::ValueField::Element>, Proof<C>) requires (VectorCommitment(C)) {
    [__site_0] let zero = zkc::algebra::index_constant() attributes ("0");
    [__site_1] let state = zkc::oracle::opening_states_at::<C>(states, zero);
    [__site_2] let (row, path) = zkc::oracle::open::<C>(state, query);
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
    [__site_0] let zero = zkc::algebra::index_constant() attributes ("0");
    [__site_1] let root = zkc::oracle::commitments_at::<C>(roots, zero);
    [__site_2] let valid = zkc::oracle::check::<C>(root, width, height, query, row, path);
    [__site_3] zkc::core::require(valid);
    return valid;
  }

  configure CommitRows = Commit(C = "rows.merkle-keccak256.koala-bear/1");
  configure OpenRow = Open(C = "rows.merkle-keccak256.koala-bear/1");
  configure CheckRow = Check(C = "rows.merkle-keccak256.koala-bear/1");
  protocol Main {
    roles (P, V);
    inputs (
      P values: Vector<koala-bear::Element>,
      P width: index,
      P query: index,
      V expected_width: index,
      V expected_height: index,
      V selected: index
    );
    outputs (
      V bool,
      V Commitments<"rows.merkle-keccak256.koala-bear/1">,
      V Vector<koala-bear::Element>,
      V Proof<"rows.merkle-keccak256.koala-bear/1">
    );
    local [__site_0] P: let (roots, states) = CommitRows(values, width);
    message [__site_1] roots: P(roots) -> V(received_roots);
    local [__site_2] P: let (row, path) = OpenRow(states, query);
    message [__site_3] row: P(row) -> V(received_row);
    message [__site_4] path: P(path) -> V(received_path);
    local [__site_5] V: let valid = CheckRow(
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

// Sampled affine-table consistency, without FRI or AIR.
module {
  fn CommitBaseAlgorithm<C: domain Commitment>(
    values: Vector<C::ValueField::Element>,
    width: index
  ) -> (Commitment<C>, OpeningState<C>) requires (VectorCommitment(C)) {
    let (value00, value01) = oracle.commit::<C>(values, width);
    return (value00, value01);
  }

  configure CommitBase = CommitBaseAlgorithm(C = "rows.merkle-keccak256.koala-bear/1");
  fn CommitExtensionAlgorithm<C: domain Commitment>(
    values: Vector<C::ValueField::Element>,
    width: index
  ) -> (Commitment<C>, OpeningState<C>) requires (VectorCommitment(C)) {
    let (value00, value01) = oracle.commit::<C>(values, width);
    return (value00, value01);
  }

  configure CommitExtension = CommitExtensionAlgorithm(
    C = "rows.merkle-keccak256.koala-bear.ext8-binomial3/1"
  );
  fn OpenBaseAlgorithm<C: domain Commitment>(
    state: OpeningState<C>,
    index: index
  ) -> (Vector<C::ValueField::Element>, Proof<C>) requires (VectorCommitment(C)) {
    let (value00, value01) = oracle.open::<C>(state, index);
    return (value00, value01);
  }

  configure OpenBase = OpenBaseAlgorithm(C = "rows.merkle-keccak256.koala-bear/1");
  fn OpenExtensionAlgorithm<C: domain Commitment>(
    state: OpeningState<C>,
    index: index
  ) -> (Vector<C::ValueField::Element>, Proof<C>) requires (VectorCommitment(C)) {
    let (value00, value01) = oracle.open::<C>(state, index);
    return (value00, value01);
  }

  configure OpenExtension = OpenExtensionAlgorithm(
    C = "rows.merkle-keccak256.koala-bear.ext8-binomial3/1"
  );
  fn CheckBaseAlgorithm<C: domain Commitment>(
    root: Commitment<C>,
    width: index,
    height: index,
    index: index,
    row: Vector<C::ValueField::Element>,
    path: Proof<C>
  ) -> (bool) requires (VectorCommitment(C)) {
    let (value0) = oracle.check::<C>(root, width, height, index, row, path);
    control.require(value0);
    return (value0);
  }

  configure CheckBase = CheckBaseAlgorithm(C = "rows.merkle-keccak256.koala-bear/1");
  fn CheckExtensionAlgorithm<C: domain Commitment>(
    root: Commitment<C>,
    width: index,
    height: index,
    index: index,
    row: Vector<C::ValueField::Element>,
    path: Proof<C>
  ) -> (bool) requires (VectorCommitment(C)) {
    let (value0) = oracle.check::<C>(root, width, height, index, row, path);
    control.require(value0);
    return (value0);
  }

  configure CheckExtension = CheckExtensionAlgorithm(
    C = "rows.merkle-keccak256.koala-bear.ext8-binomial3/1"
  );
  fn DrawAlgorithm<F: domain Field>(coins: Rng<F>) -> (F::Element, Rng<F>) requires (Field(F)) {
    [draw] let (value00, value01) = random.draw::<F>(coins);
    return (value00, value01);
  }

  configure Draw = DrawAlgorithm(F = "koala-bear.ext8-binomial3");
  fn QueryAlgorithm<F: domain Field>(coins: Rng<F>, bound: index) -> (index, Rng<F>) requires (
    IndexRandomness(F)
  ) {
    [draw] let (value00, value01) = random.index::<F>(coins, bound);
    return (value00, value01);
  }

  configure Query = QueryAlgorithm(F = "koala-bear.ext8-binomial3");
  fn CombineAlgorithm<F: domain Field>(
    x: Vector<F::BaseField::Element>,
    y: Vector<F::BaseField::Element>,
    alpha: F::Element
  ) -> (Vector<F::Element>) requires (ExtensionField(F)) {
    let (value0) = vector.embed::<F>(x);
    let (value1) = vector.embed::<F>(y);
    let (value2) = vector.scale::<F>(value0, alpha);
    let (value3) = vector.add::<F>(value2, value1);
    return (value3);
  }

  configure Combine = CombineAlgorithm(F = "koala-bear.ext8-binomial3");
  fn CheckAffineAlgorithm<F: domain Field>(
    x: Vector<F::BaseField::Element>,
    y: Vector<F::BaseField::Element>,
    z: Vector<F::Element>,
    alpha: F::Element
  ) -> (bool) requires (ExtensionField(F), Field(F::BaseField)) {
    let (value0) = index.constant() attributes ("0");
    let (value1) = vector.get::<F::BaseField>(x, value0);
    let (value2) = field.embed::<F>(value1);
    let (value3) = vector.get::<F::BaseField>(y, value0);
    let (value4) = field.embed::<F>(value3);
    let (value5) = vector.get::<F>(z, value0);
    let (value6) = field.mul::<F>(value2, alpha);
    let (value7) = field.add::<F>(value6, value4);
    let (value8) = field.equal::<F>(value7, value5);
    control.require(value8);
    return (value8);
  }

  configure CheckAffine = CheckAffineAlgorithm(F = "koala-bear.ext8-binomial3");
  fn ShapeAlgorithm<F: domain Field>() -> (index, index) requires (Field(F)) {
    let (value0) = index.constant() attributes ("1");
    let (value1) = index.constant() attributes ("8");
    return (value0, value1);
  }

  configure Shape = ShapeAlgorithm(F = "koala-bear.ext8-binomial3");
  protocol Affine {
    roles (P, V);
    inputs (
      P x: Vector<koala-bear::Element>,
      P y: Vector<koala-bear::Element>,
      V coins: Rng<koala-bear.ext8-binomial3>
    );
    outputs (V bool);
    local P: let (p_width, p_height) = Shape();
    local V: let (v_width, v_height) = Shape();
    local P: let (x_root, x_state) = CommitBase(x, p_width);
    message x_root: P(x_root) -> V(v_x_root);
    local P: let (y_root, y_state) = CommitBase(y, p_width);
    message y_root: P(y_root) -> V(v_y_root);
    local V: let (alpha, coins_alpha) = Draw(coins);
    message alpha: V(alpha) -> P(p_alpha);
    local P: let (z) = Combine(x, y, p_alpha);
    local P: let (z_root, z_state) = CommitExtension(z, p_width);
    message z_root: P(z_root) -> V(v_z_root);
    local V: let (query0, coins_query0) = Query(coins_alpha, v_height);
    message query0: V(query0) -> P(p_query0);
    local V: let (query1, coins_query1) = Query(coins_query0, v_height);
    message query1: V(query1) -> P(p_query1);
    local V: let (query2, coins_query2) = Query(coins_query1, v_height);
    message query2: V(query2) -> P(p_query2);
    local P: let (x0_row, x0_path) = OpenBase(x_state, p_query0);
    message x0_row: P(x0_row) -> V(v_x0_row);
    message x0_path: P(x0_path) -> V(v_x0_path);
    local V: let (x0_authenticated) = CheckBase(
      v_x_root,
      v_width,
      v_height,
      query0,
      v_x0_row,
      v_x0_path
    );
    local P: let (y0_row, y0_path) = OpenBase(y_state, p_query0);
    message y0_row: P(y0_row) -> V(v_y0_row);
    message y0_path: P(y0_path) -> V(v_y0_path);
    local V: let (y0_authenticated) = CheckBase(
      v_y_root,
      v_width,
      v_height,
      query0,
      v_y0_row,
      v_y0_path
    );
    local P: let (z0_row, z0_path) = OpenExtension(z_state, p_query0);
    message z0_row: P(z0_row) -> V(v_z0_row);
    message z0_path: P(z0_path) -> V(v_z0_path);
    local V: let (z0_authenticated) = CheckExtension(
      v_z_root,
      v_width,
      v_height,
      query0,
      v_z0_row,
      v_z0_path
    );
    local V: let (accepted0) = CheckAffine(v_x0_row, v_y0_row, v_z0_row, alpha);
    local P: let (x1_row, x1_path) = OpenBase(x_state, p_query1);
    message x1_row: P(x1_row) -> V(v_x1_row);
    message x1_path: P(x1_path) -> V(v_x1_path);
    local V: let (x1_authenticated) = CheckBase(
      v_x_root,
      v_width,
      v_height,
      query1,
      v_x1_row,
      v_x1_path
    );
    local P: let (y1_row, y1_path) = OpenBase(y_state, p_query1);
    message y1_row: P(y1_row) -> V(v_y1_row);
    message y1_path: P(y1_path) -> V(v_y1_path);
    local V: let (y1_authenticated) = CheckBase(
      v_y_root,
      v_width,
      v_height,
      query1,
      v_y1_row,
      v_y1_path
    );
    local P: let (z1_row, z1_path) = OpenExtension(z_state, p_query1);
    message z1_row: P(z1_row) -> V(v_z1_row);
    message z1_path: P(z1_path) -> V(v_z1_path);
    local V: let (z1_authenticated) = CheckExtension(
      v_z_root,
      v_width,
      v_height,
      query1,
      v_z1_row,
      v_z1_path
    );
    local V: let (accepted1) = CheckAffine(v_x1_row, v_y1_row, v_z1_row, alpha);
    local P: let (x2_row, x2_path) = OpenBase(x_state, p_query2);
    message x2_row: P(x2_row) -> V(v_x2_row);
    message x2_path: P(x2_path) -> V(v_x2_path);
    local V: let (x2_authenticated) = CheckBase(
      v_x_root,
      v_width,
      v_height,
      query2,
      v_x2_row,
      v_x2_path
    );
    local P: let (y2_row, y2_path) = OpenBase(y_state, p_query2);
    message y2_row: P(y2_row) -> V(v_y2_row);
    message y2_path: P(y2_path) -> V(v_y2_path);
    local V: let (y2_authenticated) = CheckBase(
      v_y_root,
      v_width,
      v_height,
      query2,
      v_y2_row,
      v_y2_path
    );
    local P: let (z2_row, z2_path) = OpenExtension(z_state, p_query2);
    message z2_row: P(z2_row) -> V(v_z2_row);
    message z2_path: P(z2_path) -> V(v_z2_path);
    local V: let (z2_authenticated) = CheckExtension(
      v_z_root,
      v_width,
      v_height,
      query2,
      v_z2_row,
      v_z2_path
    );
    local V: let (accepted2) = CheckAffine(v_x2_row, v_y2_row, v_z2_row, alpha);
    return (accepted2);
  }

  instance concrete: Affine {
    roles (P = P, V = V);
  }

  entry main = concrete;
}

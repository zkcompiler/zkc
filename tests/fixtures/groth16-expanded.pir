// examples/protocols/groth16.pir in the expanded notation: every struct as its
// ordered leaves, every operator as its declared call, the bundle as its
// requirements. Both sources must produce the same common records.
module {
  relation Circuit = r1cs("circuit.r1cs");
  derive Core = rank_one(Circuit, public_matrices);

  fn CosetNumerator<F: TwoAdicField>(
    assignment: Vector<F::Element>,
    qap.matrix_a: Matrix<F::Element>,
    qap.matrix_b: Matrix<F::Element>,
    qap.coset: F::Element,
    qap.domain_size: index
  ) -> Vector<F::Element> {
    let a = matrix::mul_vector(qap.matrix_a, assignment);
    let b = matrix::mul_vector(qap.matrix_b, assignment);
    let c = vector::mul(a, b);
    let one = field::constant::<F>() attributes ("1");
    let ap = poly::coset_interpolate(a, one);
    let bp = poly::coset_interpolate(b, one);
    let cp = poly::coset_interpolate(c, one);
    let ao = poly::coset_evaluate(ap, qap.coset, qap.domain_size);
    let bo = poly::coset_evaluate(bp, qap.coset, qap.domain_size);
    let co = poly::coset_evaluate(cp, qap.coset, qap.domain_size);
    let numerator = vector::sub(vector::mul(ao, bo), co);
    return numerator;
  }

  fn Prove<F: PairingField>(
    satisfied.bound.assignment: Vector<F::Element>,
    satisfied.bound.statement: Vector<F::Element>,
    satisfied.bound.private_assignment: Vector<F::Element>,
    qap.matrix_a: Matrix<F::Element>,
    qap.matrix_b: Matrix<F::Element>,
    qap.coset: F::Element,
    qap.domain_size: index,
    key.alpha: F::PairingG1::Element,
    key.beta_g1: F::PairingG1::Element,
    key.beta_g2: F::PairingG2::Element,
    key.delta_g1: F::PairingG1::Element,
    key.delta_g2: F::PairingG2::Element,
    key.a_query: Vector<F::PairingG1::Element>,
    key.b_g1_query: Vector<F::PairingG1::Element>,
    key.b_g2_query: Vector<F::PairingG2::Element>,
    key.private_query: Vector<F::PairingG1::Element>,
    key.h_query: Vector<F::PairingG1::Element>,
    r: F::Element,
    s: F::Element
  ) -> (F::PairingG1::Element, F::PairingG2::Element, F::PairingG1::Element) requires (
    TwoAdicField(F),
    ScalarAction(F::PairingG1),
    ScalarAction(F::PairingG2),
    "="(F::PairingG1::Scalar, F),
    "="(F::PairingG2::Scalar, F)
  ) {
    let assignment = satisfied.bound.assignment;
    let numerator = CosetNumerator::<F>(
      assignment, qap.matrix_a, qap.matrix_b, qap.coset, qap.domain_size
    );
    let linear_a = curve::msm(assignment, key.a_query);
    let linear_b1 = curve::msm(assignment, key.b_g1_query);
    let linear_b2 = curve::msm(assignment, key.b_g2_query);
    let linear_private = curve::msm(satisfied.bound.private_assignment, key.private_query);
    let h = curve::msm(numerator, key.h_query);
    let a = curve::add(curve::add(key.alpha, linear_a), curve::scale(key.delta_g1, r));
    let b1 = curve::add(curve::add(key.beta_g1, linear_b1), curve::scale(key.delta_g1, s));
    let b2 = curve::add(curve::add(key.beta_g2, linear_b2), curve::scale(key.delta_g2, s));
    let c = curve::add(
      curve::add(
        curve::add(curve::add(linear_private, h), curve::scale(a, s)),
        curve::scale(b1, r)
      ),
      curve::neg(curve::scale(key.delta_g1, field::mul(r, s)))
    );
    return (a, b2, c);
  }

  fn Verify<F: PairingField>(
    statement: Vector<F::Element>,
    vk.input_query: Vector<F::PairingG1::Element>,
    vk.alpha: F::PairingG1::Element,
    vk.beta: F::PairingG2::Element,
    vk.gamma: F::PairingG2::Element,
    vk.delta: F::PairingG2::Element,
    a: F::PairingG1::Element,
    b: F::PairingG2::Element,
    c: F::PairingG1::Element
  ) -> bool requires (
    ScalarAction(F::PairingG1),
    ScalarAction(F::PairingG2),
    "="(F::PairingG1::Scalar, F),
    "="(F::PairingG2::Scalar, F)
  ) {
    let one = field::constant::<F>() attributes ("1");
    let public_assignment = vector::concat([one], statement);
    let public_point = curve::msm(public_assignment, vk.input_query);
    let left = [curve::neg(a), public_point, c, vk.alpha];
    let right = [b, vk.gamma, vk.delta, vk.beta];
    let accepted = pairing::check::<F>(left, right);
    return accepted;
  }

  fn Draw<F: Field>(coins: Rng<F>) -> (F::Element, F::Element) {
    let (r, after_r) = random::draw(coins);
    let (s, after_s) = random::draw(after_r);
    return (r, s);
  }

  fn RequireZero<F: Field>(values: Vector<F::Element>) -> () {
    let polynomial = poly::from_coefficients(values);
    control::require(index::equal(poly::coefficient_count(polynomial), 0));
    return ();
  }

  fn BindAssignment<F: Field>(
    assignment: Vector<F::Element>,
    statement: Vector<F::Element>,
    n_public: index
  ) -> (Vector<F::Element>, Vector<F::Element>, Vector<F::Element>) {
    let one = field::constant::<F>() attributes ("1");
    control::require(field::equal(assignment[0], one));
    control::require(index::equal(statement.len(), n_public));
    let actual_public = vector::slice(assignment, 1, n_public);
    RequireZero(vector::sub(actual_public, statement));
    let start = index::add(n_public, 1);
    let private_count = index::sub(assignment.len(), start);
    let private_assignment = vector::slice(assignment, start, private_count);
    return (assignment, statement, private_assignment);
  }

  configure Groth16Prove = Prove(F = bn254.fr);
  configure Groth16Verify = Verify(F = bn254.fr);
  configure Groth16Draw = Draw(F = bn254.fr);
  configure Groth16Bind = BindAssignment(F = bn254.fr);
  configure Groth16Zero = RequireZero(F = bn254.fr);
  fn Satisfy(
    bound.assignment: Vector<bn254.fr::Element>,
    bound.statement: Vector<bn254.fr::Element>,
    bound.private_assignment: Vector<bn254.fr::Element>,
    relation.a: Matrix<bn254.fr::Element>,
    relation.b: Matrix<bn254.fr::Element>,
    relation.c: Matrix<bn254.fr::Element>
  ) -> (Vector<bn254.fr::Element>, Vector<bn254.fr::Element>, Vector<bn254.fr::Element>) {
    let (az, bz, cz) = Core_Products(relation.a, relation.b, relation.c, bound.assignment);
    let residuals = Core_Residuals(az, bz, cz);
    Groth16Zero(residuals);
    return (bound.assignment, bound.statement, bound.private_assignment);
  }

  protocol Groth16 {
    roles (P, V);
    inputs (
      P assignment: Vector<bn254.fr::Element>,
      P expected_statement: Vector<bn254.fr::Element>,
      P n_public: index,
      P relation.a: Matrix<bn254.fr::Element>,
      P relation.b: Matrix<bn254.fr::Element>,
      P relation.c: Matrix<bn254.fr::Element>,
      P qap.matrix_a: Matrix<bn254.fr::Element>,
      P qap.matrix_b: Matrix<bn254.fr::Element>,
      P qap.coset: bn254.fr::Element,
      P qap.domain_size: index,
      P key.alpha: bn254.g1::Element,
      P key.beta_g1: bn254.g1::Element,
      P key.beta_g2: bn254.g2::Element,
      P key.delta_g1: bn254.g1::Element,
      P key.delta_g2: bn254.g2::Element,
      P key.a_query: Vector<bn254.g1::Element>,
      P key.b_g1_query: Vector<bn254.g1::Element>,
      P key.b_g2_query: Vector<bn254.g2::Element>,
      P key.private_query: Vector<bn254.g1::Element>,
      P key.h_query: Vector<bn254.g1::Element>,
      P coins: Rng<bn254.fr>,
      V statement: Vector<bn254.fr::Element>,
      V vk.input_query: Vector<bn254.g1::Element>,
      V vk.alpha: bn254.g1::Element,
      V vk.beta: bn254.g2::Element,
      V vk.gamma: bn254.g2::Element,
      V vk.delta: bn254.g2::Element
    );
    outputs (V bool);
    local P: let (bound.assignment, bound.statement, bound.private_assignment) = Groth16Bind(
      assignment, expected_statement, n_public
    );
    local P: let (
      satisfied.bound.assignment, satisfied.bound.statement, satisfied.bound.private_assignment
    ) = Satisfy(
      bound.assignment, bound.statement, bound.private_assignment, relation.a, relation.b, relation.c
    );
    local P: let (r, s) = Groth16Draw(coins);
    local P: let (proof.a, proof.b, proof.c) = Groth16Prove(
      satisfied.bound.assignment, satisfied.bound.statement, satisfied.bound.private_assignment,
      qap.matrix_a, qap.matrix_b, qap.coset, qap.domain_size,
      key.alpha, key.beta_g1, key.beta_g2, key.delta_g1, key.delta_g2,
      key.a_query, key.b_g1_query, key.b_g2_query, key.private_query, key.h_query,
      r, s
    );
    message proof_a: P(proof.a) -> V(received_a);
    message proof_b: P(proof.b) -> V(received_b);
    message proof_c: P(proof.c) -> V(received_c);
    local V: let accepted = Groth16Verify(
      statement, vk.input_query, vk.alpha, vk.beta, vk.gamma, vk.delta,
      received_a, received_b, received_c
    );
    return accepted;
  }

  instance proof: Groth16 {
    roles (P = P, V = V);
  }

  entry main = proof;
}

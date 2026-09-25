// Reused arithmetic from examples/protocols/groth16.pir.
module {
  library(namespace="zkc.examples", name="groth16", version="1", resolution="source-v1");

  relation Circuit = r1cs("circuit.json");
  derive Core = rank_one(Circuit, public_matrices);
  // Both pairing groups are acted on by the scalar field itself.
  pub bundle PairingScalars(F) = (
    ScalarAction(F::PairingG1),
    ScalarAction(F::PairingG2),
    "="(F::PairingG1::Scalar, F),
    "="(F::PairingG2::Scalar, F)
  );

  pub struct RelationMatrices<F: domain Field> {
    a: Matrix<F::Element>,
    b: Matrix<F::Element>,
    c: Matrix<F::Element>
  }

  // QAP evaluation data. snarkjs H queries already incorporate the quotient
  // basis transform, so the numerator is evaluated on the shifted coset.
  pub struct QuotientDomain<F: domain Field> {
    matrix_a: Matrix<F::Element>,
    matrix_b: Matrix<F::Element>,
    coset: F::Element,
    domain_size: index
  }

  pub struct ProvingKey<F: domain Field> {
    alpha: F::PairingG1::Element,
    beta_g1: F::PairingG1::Element,
    beta_g2: F::PairingG2::Element,
    delta_g1: F::PairingG1::Element,
    delta_g2: F::PairingG2::Element,
    a_query: Vector<F::PairingG1::Element>,
    b_g1_query: Vector<F::PairingG1::Element>,
    b_g2_query: Vector<F::PairingG2::Element>,
    private_query: Vector<F::PairingG1::Element>,
    h_query: Vector<F::PairingG1::Element>
  }

  pub struct VerifyingKey<F: domain Field> {
    input_query: Vector<F::PairingG1::Element>,
    alpha: F::PairingG1::Element,
    beta: F::PairingG2::Element,
    gamma: F::PairingG2::Element,
    delta: F::PairingG2::Element
  }

  pub struct Groth16Proof<F: domain Field> {
    a: F::PairingG1::Element,
    b: F::PairingG2::Element,
    c: F::PairingG1::Element
  }

  // An assignment whose layout agrees with the statement it carries:
  // [ONE, public inputs..., private inputs...]. Layout is not satisfaction.
  pub struct BoundAssignment<F: domain Field> constructors (BindAssignment) {
    assignment: Vector<F::Element>,
    statement: Vector<F::Element>,
    private_assignment: Vector<F::Element>
  }

  // A bound assignment satisfying the supplied matrices. With public_matrices,
  // the Groth16 host binds those matrices to the retained Circuit descriptor;
  // this source constructor alone does not establish that host binding.
  pub struct SatisfiedAssignment<F: domain Field> constructors (Satisfy) {
    bound: BoundAssignment<F>
  }

  pub fn CosetNumerator<F: TwoAdicField>(assignment: Vector<F::Element>, qap: QuotientDomain<F>) -> Vector<F::Element> {
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
    let numerator = vector::mul(ao, bo) - co;
    return numerator;
  }

  pub fn Prove<F: PairingField>(
    satisfied: SatisfiedAssignment<F>,
    qap: QuotientDomain<F>,
    key: ProvingKey<F>,
    r: F::Element,
    s: F::Element
  ) -> Groth16Proof<F> requires (TwoAdicField(F), PairingScalars(F)) {
    let assignment = satisfied.bound.assignment;
    let numerator = CosetNumerator::<F>(assignment, qap);
    let linear_a = curve::msm(assignment, key.a_query);
    let linear_b1 = curve::msm(assignment, key.b_g1_query);
    let linear_b2 = curve::msm(assignment, key.b_g2_query);
    let linear_private = curve::msm(satisfied.bound.private_assignment, key.private_query);
    let h = curve::msm(numerator, key.h_query);
    // A = alpha + A(w) + r * delta, and the two group versions of B.
    let a = key.alpha + linear_a + key.delta_g1 * r;
    let b1 = key.beta_g1 + linear_b1 + key.delta_g1 * s;
    let b2 = key.beta_g2 + linear_b2 + key.delta_g2 * s;
    // C = private(w) + H + s*A + r*B1 - r*s*delta.
    let c = linear_private + h + a * s + b1 * r + -(key.delta_g1 * (r * s));
    let proof = Groth16Proof::<F> {
      a,
      b: b2,
      c
    };
    return proof;
  }

  pub fn Verify<F: PairingField>(
    statement: Vector<F::Element>,
    vk: VerifyingKey<F>,
    a: F::PairingG1::Element,
    b: F::PairingG2::Element,
    c: F::PairingG1::Element
  ) -> bool requires (PairingScalars(F)) {
    let one = field::constant::<F>() attributes ("1");
    let public_assignment = vector::concat([one], statement);
    let public_point = curve::msm(public_assignment, vk.input_query);
    // e(-A, B) * e(public_point, gamma) * e(C, delta) * e(alpha, beta) = 1.
    let left = [-a, public_point, c, vk.alpha];
    let right = [b, vk.gamma, vk.delta, vk.beta];
    let accepted = pairing::check::<F>(left, right);
    return accepted;
  }

  pub fn Draw<F: Field>(coins: Rng<F>) -> (F::Element, F::Element) {
    let (r, after_r) = random::draw(coins);
    let (s, after_s) = random::draw(after_r);
    return (r, s);
  }

  // Exact zero-vector check via canonical polynomial coefficient trimming.
  pub fn RequireZero<F: Field>(values: Vector<F::Element>) -> () {
    let polynomial = poly::from_coefficients(values);
    control::require(index::equal(poly::coefficient_count(polynomial), 0));
    return ();
  }

  pub fn BindAssignment<F: Field>(
    assignment: Vector<F::Element>,
    statement: Vector<F::Element>,
    n_public: index
  ) -> BoundAssignment<F> {
    let one = field::constant::<F>() attributes ("1");
    control::require(field::equal(assignment[0], one));
    control::require(index::equal(statement.len(), n_public));
    let actual_public = vector::slice(assignment, 1, n_public);
    RequireZero(actual_public - statement);
    let start = index::add(n_public, 1);
    let private_count = index::sub(assignment.len(), start);
    let private_assignment = vector::slice(assignment, start, private_count);
    let bound = BoundAssignment {
      assignment,
      statement,
      private_assignment
    };
    return bound;
  }

  pub configure Groth16Prove = Prove(F = bn254.fr);
  pub configure Groth16Verify = Verify(F = bn254.fr);
  pub configure Groth16Draw = Draw(F = bn254.fr);
  pub configure Groth16Bind = BindAssignment(F = bn254.fr);
  pub configure Groth16Zero = RequireZero(F = bn254.fr);
  pub fn Satisfy(bound: BoundAssignment<bn254.fr>, relation: RelationMatrices<bn254.fr>) -> SatisfiedAssignment<bn254.fr> {
    let (az, bz, cz) = Core_Products(relation.a, relation.b, relation.c, bound.assignment);
    let residuals = Core_Residuals(az, bz, cz);
    Groth16Zero(residuals);
    let satisfied = SatisfiedAssignment {
      bound
    };
    return satisfied;
  }

}

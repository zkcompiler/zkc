// examples/protocols/groth16.pir in the expanded notation: every struct as its
// ordered leaves, every operator as its declared call, the bundle as its
// requirements. Both sources must produce the same common records.

use zkc::curve::{ScalarAction};
use zkc::algebra::{Field, Matrix, PairingField, TwoAdicField, Vector};
use zkc::algebra;
use zkc::core;
use zkc::curve;
use zkc::poly;
use zkc::random::{Rng};
use zkc::random;
relation Circuit = r1cs("circuit.r1cs");
derive Core = rank_one(Circuit, public_matrices);

fn CosetNumerator<F: TwoAdicField>(
  assignment: Vector<F::Element>,
  qap_matrix_a: Matrix<F::Element>,
  qap_matrix_b: Matrix<F::Element>,
  qap_coset: F::Element,
  qap_domain_size: index
) -> Vector<F::Element> {
  let a = zkc::algebra::matrix_mul_vector(qap_matrix_a, assignment);
  let b = zkc::algebra::matrix_mul_vector(qap_matrix_b, assignment);
  let c = zkc::algebra::vector_mul(a, b);
  let one = zkc::algebra::constant::<F>() attributes ("1");
  let ap = zkc::poly::coset_interpolate(a, one);
  let bp = zkc::poly::coset_interpolate(b, one);
  let cp = zkc::poly::coset_interpolate(c, one);
  let ao = zkc::poly::coset_evaluate(ap, qap_coset, qap_domain_size);
  let bo = zkc::poly::coset_evaluate(bp, qap_coset, qap_domain_size);
  let co = zkc::poly::coset_evaluate(cp, qap_coset, qap_domain_size);
  let numerator = zkc::algebra::vector_sub(zkc::algebra::vector_mul(ao, bo), co);
  return numerator;
}

fn Prove<F: PairingField>(
  satisfied_bound_assignment: Vector<F::Element>,
  satisfied_bound_statement: Vector<F::Element>,
  satisfied_bound_private_assignment: Vector<F::Element>,
  qap_matrix_a: Matrix<F::Element>,
  qap_matrix_b: Matrix<F::Element>,
  qap_coset: F::Element,
  qap_domain_size: index,
  key_alpha: F::PairingG1::Element,
  key_beta_g1: F::PairingG1::Element,
  key_beta_g2: F::PairingG2::Element,
  key_delta_g1: F::PairingG1::Element,
  key_delta_g2: F::PairingG2::Element,
  key_a_query: Vector<F::PairingG1::Element>,
  key_b_g1_query: Vector<F::PairingG1::Element>,
  key_b_g2_query: Vector<F::PairingG2::Element>,
  key_private_query: Vector<F::PairingG1::Element>,
  key_h_query: Vector<F::PairingG1::Element>,
  r: F::Element,
  s: F::Element
) -> (F::PairingG1::Element, F::PairingG2::Element, F::PairingG1::Element) requires (
  TwoAdicField(F),
  ScalarAction(F::PairingG1),
  ScalarAction(F::PairingG2),
  F::PairingG1::Scalar == F,
  F::PairingG2::Scalar == F
) {
  let assignment = satisfied_bound_assignment;
  let numerator = CosetNumerator::<F>(
    assignment, qap_matrix_a, qap_matrix_b, qap_coset, qap_domain_size
  );
  let linear_a = zkc::curve::msm(assignment, key_a_query);
  let linear_b1 = zkc::curve::msm(assignment, key_b_g1_query);
  let linear_b2 = zkc::curve::msm(assignment, key_b_g2_query);
  let linear_private = zkc::curve::msm(satisfied_bound_private_assignment, key_private_query);
  let h = zkc::curve::msm(numerator, key_h_query);
  let a = zkc::curve::add(zkc::curve::add(key_alpha, linear_a), zkc::curve::scale(key_delta_g1, r));
  let b1 = zkc::curve::add(zkc::curve::add(key_beta_g1, linear_b1), zkc::curve::scale(key_delta_g1, s));
  let b2 = zkc::curve::add(zkc::curve::add(key_beta_g2, linear_b2), zkc::curve::scale(key_delta_g2, s));
  let c = zkc::curve::add(
    zkc::curve::add(
      zkc::curve::add(zkc::curve::add(linear_private, h), zkc::curve::scale(a, s)),
      zkc::curve::scale(b1, r)
    ),
    zkc::curve::neg(zkc::curve::scale(key_delta_g1, zkc::algebra::mul(r, s)))
  );
  return (a, b2, c);
}

fn Verify<F: PairingField>(
  statement: Vector<F::Element>,
  vk_input_query: Vector<F::PairingG1::Element>,
  vk_alpha: F::PairingG1::Element,
  vk_beta: F::PairingG2::Element,
  vk_gamma: F::PairingG2::Element,
  vk_delta: F::PairingG2::Element,
  a: F::PairingG1::Element,
  b: F::PairingG2::Element,
  c: F::PairingG1::Element
) -> bool requires (
  ScalarAction(F::PairingG1),
  ScalarAction(F::PairingG2),
  F::PairingG1::Scalar == F,
  F::PairingG2::Scalar == F
) {
  let one = zkc::algebra::constant::<F>() attributes ("1");
  let public_assignment = zkc::algebra::vector_concat([one], statement);
  let public_point = zkc::curve::msm(public_assignment, vk_input_query);
  let left = [zkc::curve::neg(a), public_point, c, vk_alpha];
  let right = [b, vk_gamma, vk_delta, vk_beta];
  let accepted = zkc::curve::pairing_check::<F>(left, right);
  return accepted;
}

fn Draw<F: Field>(coins: Rng<F>) -> (F::Element, F::Element) {
  let (r, after_r) = zkc::random::draw(coins);
  let (s, after_s) = zkc::random::draw(after_r);
  return (r, s);
}

fn RequireZero<F: Field>(values: Vector<F::Element>) -> () {
  let polynomial = zkc::poly::from_coefficients(values);
  zkc::core::require(zkc::algebra::index_equal(zkc::poly::coefficient_count(polynomial), 0));
  return ();
}

fn BindAssignment<F: Field>(
  assignment: Vector<F::Element>,
  statement: Vector<F::Element>,
  n_public: index
) -> (Vector<F::Element>, Vector<F::Element>, Vector<F::Element>) {
  let one = zkc::algebra::constant::<F>() attributes ("1");
  zkc::core::require(zkc::algebra::equal(assignment[0], one));
  zkc::core::require(zkc::algebra::index_equal(statement.len(), n_public));
  let actual_public = zkc::algebra::vector_slice(assignment, 1, n_public);
  RequireZero(zkc::algebra::vector_sub(actual_public, statement));
  let start = zkc::algebra::index_add(n_public, 1);
  let private_count = zkc::algebra::index_sub(assignment.len(), start);
  let private_assignment = zkc::algebra::vector_slice(assignment, start, private_count);
  return (assignment, statement, private_assignment);
}

configure Groth16Prove = Prove(F = "bn254.fr");
configure Groth16Verify = Verify(F = "bn254.fr");
configure Groth16Draw = Draw(F = "bn254.fr");
configure Groth16Bind = BindAssignment(F = "bn254.fr");
configure Groth16Zero = RequireZero(F = "bn254.fr");
fn Satisfy(
  bound_assignment: Vector<"bn254.fr"::Element>,
  bound_statement: Vector<"bn254.fr"::Element>,
  bound_private_assignment: Vector<"bn254.fr"::Element>,
  relation_a: Matrix<"bn254.fr"::Element>,
  relation_b: Matrix<"bn254.fr"::Element>,
  relation_c: Matrix<"bn254.fr"::Element>
) -> (Vector<"bn254.fr"::Element>, Vector<"bn254.fr"::Element>, Vector<"bn254.fr"::Element>) {
  let (az, bz, cz) = Core_Products(relation_a, relation_b, relation_c, bound_assignment);
  let residuals = Core_Residuals(az, bz, cz);
  Groth16Zero(residuals);
  return (bound_assignment, bound_statement, bound_private_assignment);
}

protocol Groth16 {
  roles (P, V);
  inputs (
    P assignment: Vector<"bn254.fr"::Element>,
    P expected_statement: Vector<"bn254.fr"::Element>,
    P n_public: index,
    P relation_a: Matrix<"bn254.fr"::Element>,
    P relation_b: Matrix<"bn254.fr"::Element>,
    P relation_c: Matrix<"bn254.fr"::Element>,
    P qap_matrix_a: Matrix<"bn254.fr"::Element>,
    P qap_matrix_b: Matrix<"bn254.fr"::Element>,
    P qap_coset: "bn254.fr"::Element,
    P qap_domain_size: index,
    P key_alpha: "bn254.g1"::Element,
    P key_beta_g1: "bn254.g1"::Element,
    P key_beta_g2: "bn254.g2"::Element,
    P key_delta_g1: "bn254.g1"::Element,
    P key_delta_g2: "bn254.g2"::Element,
    P key_a_query: Vector<"bn254.g1"::Element>,
    P key_b_g1_query: Vector<"bn254.g1"::Element>,
    P key_b_g2_query: Vector<"bn254.g2"::Element>,
    P key_private_query: Vector<"bn254.g1"::Element>,
    P key_h_query: Vector<"bn254.g1"::Element>,
    P coins: Rng<"bn254.fr">,
    V statement: Vector<"bn254.fr"::Element>,
    V vk_input_query: Vector<"bn254.g1"::Element>,
    V vk_alpha: "bn254.g1"::Element,
    V vk_beta: "bn254.g2"::Element,
    V vk_gamma: "bn254.g2"::Element,
    V vk_delta: "bn254.g2"::Element
  );
  outputs (V bool);
  local P: let (bound_assignment, bound_statement, bound_private_assignment) = Groth16Bind(
    assignment, expected_statement, n_public
  );
  local P: let (
    satisfied_bound_assignment, satisfied_bound_statement, satisfied_bound_private_assignment
  ) = Satisfy(
    bound_assignment, bound_statement, bound_private_assignment, relation_a, relation_b, relation_c
  );
  local P: let (r, s) = Groth16Draw(coins);
  local P: let (proof_a, proof_b, proof_c) = Groth16Prove(
    satisfied_bound_assignment, satisfied_bound_statement, satisfied_bound_private_assignment,
    qap_matrix_a, qap_matrix_b, qap_coset, qap_domain_size,
    key_alpha, key_beta_g1, key_beta_g2, key_delta_g1, key_delta_g2,
    key_a_query, key_b_g1_query, key_b_g2_query, key_private_query, key_h_query,
    r, s
  );
  message proof_a: P(proof_a) -> V(received_a);
  message proof_b: P(proof_b) -> V(received_b);
  message proof_c: P(proof_c) -> V(received_c);
  local V: let accepted = Groth16Verify(
    statement, vk_input_query, vk_alpha, vk_beta, vk_gamma, vk_delta,
    received_a, received_b, received_c
  );
  return accepted;
}

instance proof: Groth16 {
  roles (P = P, V = V);
}

entry main = proof;

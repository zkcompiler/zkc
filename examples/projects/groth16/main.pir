// Protocol schedule using separately resolved implementation helpers.
module {
  dependency helpers = library(namespace="zkc.examples", name="groth16", version="1", resolution="source-v1");
  use helpers::{
    RelationMatrices,
    QuotientDomain,
    ProvingKey,
    VerifyingKey,
    Groth16Bind,
    Satisfy,
    Groth16Draw,
    Groth16Prove,
    Groth16Verify
  };
  // The production host supplies an OS-seeded typed RNG. Finite tapes are test-only.
  protocol Groth16 {
    roles (P, V);
    inputs (
      P assignment: Vector<bn254.fr::Element>,
      P expected_statement: Vector<bn254.fr::Element>,
      P n_public: index,
      P relation: RelationMatrices<bn254.fr>,
      P qap: QuotientDomain<bn254.fr>,
      P key: ProvingKey<bn254.fr>,
      P coins: Rng<bn254.fr>,
      V statement: Vector<bn254.fr::Element>,
      V vk: VerifyingKey<bn254.fr>
    );
    outputs (V bool);
    local P: let bound = Groth16Bind(assignment, expected_statement, n_public);
    local P: let satisfied = Satisfy(bound, relation);
    local P: let (r, s) = Groth16Draw(coins);
    local P: let proof = Groth16Prove(satisfied, qap, key, r, s);
    message proof_a: P(proof.a) -> V(received_a);
    message proof_b: P(proof.b) -> V(received_b);
    message proof_c: P(proof.c) -> V(received_c);
    local V: let accepted = Groth16Verify(statement, vk, received_a, received_b, received_c);
    return accepted;
  }

  instance proof: Groth16 {
    roles (P = P, V = V);
  }

  entry main = proof;
}

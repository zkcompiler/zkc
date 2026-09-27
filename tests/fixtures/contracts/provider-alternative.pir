// The helper preserves the bulk contract; the caller selects its algorithm.
module {
  use zkc::algebra::{Field, Vector};
  use zkc::algebra;

  pub fn Dot<F: Field>(left: Vector<F::Element>, right: Vector<F::Element>)
      -> F::Element {
    [product] let result = algebra::vector_dot::<F>(left, right);
    return result;
  }

  configure Default = Dot(F = "bls12-381.fr");
  configure Pairwise = Dot(F = "bls12-381.fr")
    using (product = "arkworks-pairwise/vector.dot");

  protocol InnerProduct {
    roles (P, V);
    inputs (P left: Vector<"bls12-381.fr"::Element>,
            P right: Vector<"bls12-381.fr"::Element>);
    outputs (V "bls12-381.fr"::Element, V "bls12-381.fr"::Element);
    local P: let ordinary = Default(left, right);
    local P: let alternate = Pairwise(left, right);
    message first: P(ordinary) -> V(receivedDefault);
    message second: P(alternate) -> V(receivedPairwise);
    return (receivedDefault, receivedPairwise);
  }

  instance concrete: InnerProduct { roles (P = P, V = V); }
  entry main = concrete;
}

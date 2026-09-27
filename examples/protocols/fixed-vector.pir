// A bulk value carries its element type and exact length through compilation.
// FixedVector<T, N> is one value; [T; N] is a source aggregate of N ports.
module {
  use zkc::algebra::{Field, FixedVector, Vector};
  use zkc::algebra;

  fn Dot<F: Field, N: nat>(left: Vector<F::Element>, right: Vector<F::Element>)
      -> F::Element {
    let x: FixedVector<F::Element, N> = algebra::fixed_vector_from_vector(left);
    let y: FixedVector<F::Element, N> = algebra::fixed_vector_from_vector(right);
    let product = algebra::fixed_vector_dot(x, y);
    return product;
  }

  configure DotFour = Dot(F = koala-bear, N = 4);

  protocol InnerProduct {
    roles (P, V);
    inputs (P left: Vector<koala-bear::Element>, P right: Vector<koala-bear::Element>);
    outputs (V koala-bear::Element);
    local P: let product = DotFour(left, right);
    message result: P(product) -> V(received);
    return received;
  }

  instance concrete: InnerProduct {
    roles (P = P, V = V);
  }
  entry main = concrete;
}

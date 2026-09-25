// Authoring-layer example: inferred calls remain explicit in common source.
// The exchange illustrates composition, not a cryptographic proof.
module {
  fn One<F: Field>() -> F::Element {
    let one: F::Element = field::constant() attributes (1);
    return one;
  }

  fn Twice<F: Field>(x: F::Element) -> F::Element {
    let y = field::add(x, x);
    return y;
  }

  fn Four<F: Field>(x: F::Element) -> F::Element {
    let y = Twice(x);
    let z: F::Element = Twice(y);
    return z;
  }

  configure Calculate = Four(F = koala-bear);
  protocol Demo {
    roles (P, V);
    inputs (P x: koala-bear::Element);
    outputs (V koala-bear::Element);
    local P: let y = Calculate(x);
    message result: P(y) -> V(received);
    return received;
  }

  instance concrete: Demo {
    roles (P = P, V = V);
  }

  entry main = concrete;
}

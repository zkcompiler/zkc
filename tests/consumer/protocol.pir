module {
  fn Identity(x: bool) -> bool { x }
  fn Nested(flag: bool, x: bool) -> bool {
    let mut result = x;
    if flag { result = Identity(x); }
    return result;
  }
  protocol Send {
    roles(P, V);
    inputs(P flag: bool, P x: bool);
    outputs(V bool);
    local P: let a = Nested(flag, x);
    message value: P(a) -> V(y);
    return y;
  }
  instance run: Send { roles(P = prover, V = verifier); }
  entry main = run;
}

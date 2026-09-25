module {
  bind add = field::add(bls12-381.fr);
  bind scale = curve::scale(bls12-381.g1);
  bind sum = curve::add(bls12-381.g1);
  bind guard = control::require();
  bind commit = curve::commit(bls12-381.g1);
  bind response = curve::response(bls12-381.fr);
  fn Twice(x: "bls12-381.fr"::Element) -> "bls12-381.fr"::Element {
    [add] let y = add(x, x);
    return y;
  }

  fn Scale(g: "bls12-381.g1"::Element, x: "bls12-381.fr"::Element) -> "bls12-381.g1"::Element {
    [scale] let y = scale(g, x);
    return y;
  }

  fn Linear(g: "bls12-381.g1"::Element, x: "bls12-381.fr"::Element) -> "bls12-381.g1"::Element {
    [twice] let two = Twice(x);
    [left] let a = Scale(g, two);
    [right] let b = Scale(g, x);
    [sum] let r = sum(a, b);
    return r;
  }

  fn Commit(
    bases: Vector<"bls12-381.g1"::Element>,
    n: Nonce<"bls12-381.fr">
  ) -> (Vector<"bls12-381.g1"::Element>, Nonce<"bls12-381.fr">) {
    [commit] let (c, ready) = commit(bases, n);
    return (c, ready);
  }

  fn Respond(x: "bls12-381.fr"::Element, c: "bls12-381.fr"::Element, n: Nonce<"bls12-381.fr">) -> "bls12-381.fr"::Element {
    [response] let s = response(x, c, n);
    return s;
  }

  fn Authenticate(
    bases: Vector<"bls12-381.g1"::Element>,
    n: Nonce<"bls12-381.fr">,
    x: "bls12-381.fr"::Element,
    c: "bls12-381.fr"::Element,
    ok: bool
  ) -> (Vector<"bls12-381.g1"::Element>, "bls12-381.fr"::Element) {
    [commit] let (committed, ready) = Commit(bases, n);
    [guard] guard(ok);
    [response] let s = Respond(x, c, ready);
    return (committed, s);
  }

  protocol Main {
    roles (P);
    inputs (
      P g: "bls12-381.g1"::Element,
      P bases: Vector<"bls12-381.g1"::Element>,
      P n: Nonce<"bls12-381.fr">,
      P x: "bls12-381.fr"::Element,
      P c: "bls12-381.fr"::Element,
      P ok: bool
    );
    outputs (
      P "bls12-381.g1"::Element,
      P Vector<"bls12-381.g1"::Element>,
      P "bls12-381.fr"::Element
    );
    local [linear] P: let r = Linear(g, x);
    local [auth] P: let (commitments, s) = Authenticate(bases, n, x, c, ok);
    return (r, commitments, s);
  }

  instance concrete: Main {
    roles (P = P);
  }

  entry main = concrete;
}

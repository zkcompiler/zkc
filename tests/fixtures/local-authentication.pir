module {
  bind commit = curve::commit(bls12-381.g1);
  bind respond = curve::response(bls12-381.fr);
  bind guard = control::require();
  fn Guard(ok: bool) -> () {
    [guard] guard(ok);
    return;
  }

  fn Commit(
    bases: Vector<"bls12-381.g1"::Element>,
    n: Nonce<"bls12-381.fr">
  ) -> (Vector<"bls12-381.g1"::Element>, Nonce<"bls12-381.fr">) {
    [commit] let (points, ready) = commit(bases, n);
    return (points, ready);
  }

  fn Respond(x: "bls12-381.fr"::Element, c: "bls12-381.fr"::Element, n: Nonce<"bls12-381.fr">) -> "bls12-381.fr"::Element {
    [respond] let s = respond(x, c, n);
    return s;
  }

  fn Authenticate(
    bases: Vector<"bls12-381.g1"::Element>,
    n: Nonce<"bls12-381.fr">,
    x: "bls12-381.fr"::Element,
    c: "bls12-381.fr"::Element,
    before: bool,
    after: bool
  ) -> (Vector<"bls12-381.g1"::Element>, "bls12-381.fr"::Element) {
    [before] Guard(before);
    [commit] let (points, ready) = Commit(bases, n);
    [after] Guard(after);
    [response] let s = Respond(x, c, ready);
    return (points, s);
  }

  protocol NonceResponse {
    roles (P);
    inputs (
      P bases: Vector<"bls12-381.g1"::Element>,
      P nonce: Nonce<"bls12-381.fr">,
      P secret: "bls12-381.fr"::Element,
      P challenge: "bls12-381.fr"::Element,
      P before: bool,
      P after: bool
    );
    outputs (P Vector<"bls12-381.g1"::Element>, P "bls12-381.fr"::Element);
    local [authenticate] P: let (points, response) = Authenticate(
      bases,
      nonce,
      secret,
      challenge,
      before,
      after
    );
    return (points, response);
  }

  instance concrete: NonceResponse {
    roles (P = P);
  }

  entry main = concrete;
}

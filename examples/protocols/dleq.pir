// Two DLEQ invocations over the same bases and images, with distinct nonces.
// Group arithmetic and affine nonce state are explicit local operations.
module {
  bind curve.empty = curve::empty(bls12-381.g1) using "arkworks/curve.empty";
  bind curve.append = curve::append(bls12-381.g1) using "arkworks/curve.append";
  bind curve.commit = curve::commit(bls12-381.g1) using "arkworks/curve.commit";
  bind curve.at = curve::at(bls12-381.g1) using "arkworks/curve.at";
  bind random.draw = random::draw(bls12-381.fr) using "arkworks/random.draw";
  bind curve.response = curve::response(bls12-381.fr) using "arkworks/curve.response";
  bind curve.scale = curve::scale(bls12-381.g1) using "arkworks/curve.scale";
  bind curve.add = curve::add(bls12-381.g1) using "arkworks/curve.add";
  bind curve.equal = curve::equal(bls12-381.g1) using "arkworks/curve.equal";
  bind control.require = control::require() using "arkworks/control.require";
  bind bool.and = bool::and() using "arkworks/bool.and";
  fn DLEQCommit(
    base_0: "bls12-381.g1"::Element,
    base_1: "bls12-381.g1"::Element,
    nonce: Nonce<"bls12-381.fr">
  ) -> ("bls12-381.g1"::Element, "bls12-381.g1"::Element, Nonce<"bls12-381.fr">) {
    [empty] let empty = curve.empty();
    [append_0] let one = curve.append(empty, base_0);
    [append_1] let bases = curve.append(one, base_1);
    [commit] let (points, ready) = curve.commit(bases, nonce);
    [at_0] let a_0 = curve.at(points) attributes ("0");
    [at_1] let a_1 = curve.at(points) attributes ("1");
    return (a_0, a_1, ready);
  }

  fn DLEQDraw(coins: Rng<"bls12-381.fr">) -> ("bls12-381.fr"::Element, Rng<"bls12-381.fr">) {
    [draw] let (c, after) = random.draw(coins);
    return (c, after);
  }

  fn DLEQRespond(
    x: "bls12-381.fr"::Element,
    c: "bls12-381.fr"::Element,
    ready: Nonce<"bls12-381.fr">
  ) -> "bls12-381.fr"::Element {
    [respond] let z = curve.response(x, c, ready);
    return z;
  }

  fn DLEQCheck(
    base_0: "bls12-381.g1"::Element,
    base_1: "bls12-381.g1"::Element,
    image_0: "bls12-381.g1"::Element,
    image_1: "bls12-381.g1"::Element,
    a_0: "bls12-381.g1"::Element,
    a_1: "bls12-381.g1"::Element,
    c: "bls12-381.fr"::Element,
    z: "bls12-381.fr"::Element
  ) -> bool {
    [left_0] let left_0 = curve.scale(base_0, z);
    [image_0] let cx_0 = curve.scale(image_0, c);
    [right_0] let right_0 = curve.add(a_0, cx_0);
    [equal_0] let ok_0 = curve.equal(left_0, right_0);
    [require_0] control.require(ok_0);
    [left_1] let left_1 = curve.scale(base_1, z);
    [image_1] let cx_1 = curve.scale(image_1, c);
    [right_1] let right_1 = curve.add(a_1, cx_1);
    [equal_1] let ok_1 = curve.equal(left_1, right_1);
    [require_1] control.require(ok_1);
    [both] let ok = bool.and(ok_0, ok_1);
    return ok;
  }

  fn DLEQBoth(first: bool, second: bool) -> bool {
    [both] let ok = bool.and(first, second);
    return ok;
  }

  // Commit, challenge, respond, and check both group equations.
  protocol DLEQArgument {
    roles (P, V);
    inputs (
      P p_base_0: "bls12-381.g1"::Element,
      P p_base_1: "bls12-381.g1"::Element,
      P x: "bls12-381.fr"::Element,
      P nonce: Nonce<"bls12-381.fr">,
      V base_0: "bls12-381.g1"::Element,
      V base_1: "bls12-381.g1"::Element,
      V image_0: "bls12-381.g1"::Element,
      V image_1: "bls12-381.g1"::Element,
      V coins: Rng<"bls12-381.fr">
    );
    outputs (V bool, V Rng<"bls12-381.fr">);
    local [commit] P: let (a_0, a_1, ready) = DLEQCommit(p_base_0, p_base_1, nonce);
    message [commitment_0] g1: P(a_0) -> V(received_a_0);
    message [commitment_1] g1: P(a_1) -> V(received_a_1);
    local [challenge] V: let (c, after) = DLEQDraw(coins);
    message [challenge_message] fr: V(c) -> P(received_c);
    local [response] P: let z = DLEQRespond(x, received_c, ready);
    message [response_message] fr: P(z) -> V(received_z);
    local [equations] V: let ok = DLEQCheck(
      base_0,
      base_1,
      image_0,
      image_1,
      received_a_0,
      received_a_1,
      c,
      received_z
    );
    return (ok, after);
  }

  // Reusing a child definition does not reuse its per-invocation nonce.
  protocol RepeatedDLEQ {
    roles (P, V);
    inputs (
      P p_base_0: "bls12-381.g1"::Element,
      P p_base_1: "bls12-381.g1"::Element,
      P x: "bls12-381.fr"::Element,
      P nonce_first: Nonce<"bls12-381.fr">,
      P nonce_second: Nonce<"bls12-381.fr">,
      V base_0: "bls12-381.g1"::Element,
      V base_1: "bls12-381.g1"::Element,
      V image_0: "bls12-381.g1"::Element,
      V image_1: "bls12-381.g1"::Element,
      V coins: Rng<"bls12-381.fr">
    );
    outputs (V bool, V Rng<"bls12-381.fr">);
    dependencies (argument: DLEQArgument());
    invoke [first] argument(
      p_base_0,
      p_base_1,
      x,
      nonce_first,
      base_0,
      base_1,
      image_0,
      image_1,
      coins
    ) -> (first_ok, after_first);
    invoke [second] argument(
      p_base_0,
      p_base_1,
      x,
      nonce_second,
      base_0,
      base_1,
      image_0,
      image_1,
      after_first
    ) -> (second_ok, after_second);
    local [both] V: let accepted = DLEQBoth(first_ok, second_ok);
    return (accepted, after_second);
  }

  instance argument: DLEQArgument {
    roles (P = P, V = V);
  }

  instance repeated: RepeatedDLEQ {
    dependencies (argument = argument);
    roles (P = P, V = V);
  }

  entry main = repeated;
}

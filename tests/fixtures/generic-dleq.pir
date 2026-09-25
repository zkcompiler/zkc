// Generic local algorithms in the repeated DLEQ interaction.
module {
  fn DLEQCommitAlgorithm<G: domain Group>(
    base_0: G::Element,
    base_1: G::Element,
    nonce: Nonce<G::Scalar>
  ) -> (G::Element, G::Element, Nonce<G::Scalar>) requires (ScalarAction(G)) {
    [empty] let empty = curve::empty::<G>();
    [append_0] let one = curve::append::<G>(empty, base_0);
    [append_1] let bases = curve::append::<G>(one, base_1);
    [commit] let (points, ready) = curve::commit::<G>(bases, nonce);
    [at_0] let a_0 = curve::at::<G>(points) attributes ("0");
    [at_1] let a_1 = curve::at::<G>(points) attributes ("1");
    return (a_0, a_1, ready);
  }

  fn DLEQDrawAlgorithm<F: domain Field>(coins: Rng<F>) -> (F::Element, Rng<F>) requires (Field(F)) {
    [draw] let (c, after) = random::draw::<F>(coins);
    return (c, after);
  }

  fn DLEQRespondAlgorithm<F: domain Field>(x: F::Element, c: F::Element, ready: Nonce<F>) -> F::Element requires (
    Field(F)
  ) {
    [respond] let z = curve::response::<F>(x, c, ready);
    return z;
  }

  fn DLEQCheckAlgorithm<G: domain Group>(
    base_0: G::Element,
    base_1: G::Element,
    image_0: G::Element,
    image_1: G::Element,
    a_0: G::Element,
    a_1: G::Element,
    c: G::Scalar::Element,
    z: G::Scalar::Element
  ) -> bool requires (ScalarAction(G)) {
    [left_0] let left_0 = curve::scale::<G>(base_0, z);
    [image_0] let cx_0 = curve::scale::<G>(image_0, c);
    [right_0] let right_0 = curve::add::<G>(a_0, cx_0);
    [equal_0] let ok_0 = curve::equal::<G>(left_0, right_0);
    [require_0] control::require(ok_0);
    [left_1] let left_1 = curve::scale::<G>(base_1, z);
    [image_1] let cx_1 = curve::scale::<G>(image_1, c);
    [right_1] let right_1 = curve::add::<G>(a_1, cx_1);
    [equal_1] let ok_1 = curve::equal::<G>(left_1, right_1);
    [require_1] control::require(ok_1);
    [both] let ok = bool::and(ok_0, ok_1);
    return ok;
  }

  fn DLEQBothAlgorithm<>(first: bool, second: bool) -> bool {
    [both] let ok = bool::and(first, second);
    return ok;
  }

  configure DLEQCommit = DLEQCommitAlgorithm(G = bls12-381.g1);
  configure DLEQDraw = DLEQDrawAlgorithm(F = bls12-381.fr);
  configure DLEQRespond = DLEQRespondAlgorithm(F = bls12-381.fr);
  configure DLEQCheck = DLEQCheckAlgorithm(G = bls12-381.g1);
  configure DLEQBoth = DLEQBothAlgorithm();
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

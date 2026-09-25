// A BLS G1 exchange using the installed affine nonce contract.
// The verifier supplies the challenge; this example makes no security claim.
module {
  bind curve.generator = curve::generator(bls12-381.g1) using "arkworks/curve.generator";
  bind curve.scale = curve::scale(bls12-381.g1) using "arkworks/curve.scale";
  bind curve.empty = curve::empty(bls12-381.g1) using "arkworks/curve.empty";
  bind curve.append = curve::append(bls12-381.g1) using "arkworks/curve.append";
  bind curve.commit = curve::commit(bls12-381.g1) using "arkworks/curve.commit";
  bind curve.at = curve::at(bls12-381.g1) using "arkworks/curve.at";
  bind curve.response = curve::response(bls12-381.fr) using "arkworks/curve.response";
  bind curve.add = curve::add(bls12-381.g1) using "arkworks/curve.add";
  bind curve.equal = curve::equal(bls12-381.g1) using "arkworks/curve.equal";
  bind control.require = control::require() using "arkworks/control.require";
  fn Public(secret: "bls12-381.fr"::Element) -> "bls12-381.g1"::Element {
    [generator] let base = curve.generator();
    [public] let point = curve.scale(base, secret);
    return point;
  }

  fn Commit(nonce: Nonce<"bls12-381.fr">) -> ("bls12-381.g1"::Element, Nonce<"bls12-381.fr">) {
    [generator] let base = curve.generator();
    [empty] let empty = curve.empty();
    [append] let bases = curve.append(empty, base);
    [commit] let (points, ready) = curve.commit(bases, nonce);
    [point] let point = curve.at(points) attributes ("0");
    return (point, ready);
  }

  fn Respond(
    secret: "bls12-381.fr"::Element,
    challenge: "bls12-381.fr"::Element,
    ready: Nonce<"bls12-381.fr">
  ) -> "bls12-381.fr"::Element {
    [respond] let response = curve.response(secret, challenge, ready);
    return response;
  }

  fn Check(
    public: "bls12-381.g1"::Element,
    commitment: "bls12-381.g1"::Element,
    challenge: "bls12-381.fr"::Element,
    response: "bls12-381.fr"::Element
  ) -> bool {
    [generator] let base = curve.generator();
    [left] let left = curve.scale(base, response);
    [public] let scaled = curve.scale(public, challenge);
    [right] let right = curve.add(commitment, scaled);
    [equal] let ok = curve.equal(left, right);
    [require] control.require(ok);
    return ok;
  }

  protocol Exchange {
    roles (P, V);
    inputs (
      P secret: "bls12-381.fr"::Element,
      P nonce: Nonce<"bls12-381.fr">,
      V challenge: "bls12-381.fr"::Element
    );
    outputs (V bool);
    local [public] P: let public = Public(secret);
    message [public_message] group: P(public) -> V(received_public);
    local [commit] P: let (commitment, ready) = Commit(nonce);
    message [commitment_message] group: P(commitment) -> V(received_commitment);
    message [challenge_message] field: V(challenge) -> P(received_challenge);
    local [respond] P: let response = Respond(secret, received_challenge, ready);
    message [response_message] field: P(response) -> V(received_response);
    local [check] V: let ok = Check(
      received_public,
      received_commitment,
      challenge,
      received_response
    );
    return ok;
  }

  instance exchange: Exchange {
    roles (P = P, V = V);
  }

  entry main = exchange;
}

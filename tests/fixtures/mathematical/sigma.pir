bind add = "field.add"("bls12-381.fr");
bind mul = "field.mul"("bls12-381.fr");
bind include_challenge = "field.from_nonzero"("bls12-381.fr");
bind scale = "curve.scale"("bls12-381.g1");
bind group_add = "curve.add"("bls12-381.g1");
bind equal = "curve.equal"("bls12-381.g1");
bind nonce_draw = "random.draw"("bls12-381.fr");
bind challenge_draw = "random.draw_nonzero"("bls12-381.fr");

mathematical protocol Sigma {
  roles (Prover, Verifier);
  inputs (
    Prover witness: "bls12-381.fr"::Element,
    (Prover, Verifier) generator: "bls12-381.g1"::Element,
    (Prover, Verifier) statement: "bls12-381.g1"::Element
  );
  outputs ();
  roots (nonce = nonce_draw owners (Prover),
         challenge = challenge_draw owners (Verifier));

  query [nonce_sample] Prover nonce -> (r);
  let commitment = scale(generator, r);
  message [commitment_sent] commitment: Prover(commitment) -> Verifier(received_commitment);
  query [challenge_sample] Verifier challenge -> (c);
  message [challenge_sent] challenge: Verifier(c) -> Prover(received_challenge);
  let scalar_challenge = include_challenge(received_challenge);
  let product = mul(scalar_challenge, witness);
  let response = add(r, product);
  message [response_sent] response: Prover(response) -> Verifier(received_response);
  let verifier_challenge = include_challenge(c);
  let left = scale(generator, received_response);
  let scaled_statement = scale(statement, verifier_challenge);
  let right = group_add(received_commitment, scaled_statement);
  let accepted = equal(left, right);
  guard [verification] Verifier(accepted);
  return ();
}

instance sigma: Sigma { roles (Prover = Prover, Verifier = Verifier); }
entry main = sigma;

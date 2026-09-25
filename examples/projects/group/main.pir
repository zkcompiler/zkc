// A random scalar and its group multiple; no zero-knowledge claim.
module {
  dependency group = library(namespace="zkc.examples", name="group", version="1", resolution="source-v1");
  use group::{BlsGroup, Draw, Public, Check};
  // The library stays generic over GroupAPI; the client selects the component.
  link DrawScalar = Draw<BlsGroup>;
  link PublicPoint = Public<BlsGroup>;
  link CheckPoint = Check<BlsGroup>;
  protocol Agreement {
    roles (P, V);
    inputs (V coins: Rng<"bls12-381.fr">);
    outputs (V bool);
    local [sample] V: let (secret, after) = DrawScalar(coins);
    message challenge: V(secret) -> P(received_secret);
    local [public] P: let point = PublicPoint(received_secret);
    message point: P(point) -> V(received_point);
    local [check] V: let accepted = CheckPoint(received_point, secret);
    return accepted;
  }
  instance run: Agreement { roles (P = P, V = V); }
  entry main = run;
}

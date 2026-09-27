// A group-valued interaction family, separate from polynomial protocols.
// This checks the generator contract and message typing, not a proof system.
use zkc::curve::{
  ScalarAction
};
use zkc::core;
use zkc::curve;
fn Generator<G: ScalarAction>() -> G::Element {
  let point = zkc::curve::generator::<G>();
  return point;
}
fn CheckGenerator<G: ScalarAction>(point: G::Element) -> bool {
  let expected = zkc::curve::generator::<G>();
  let same = zkc::curve::equal::<G>(point, expected);
  zkc::core::require(same);
  return same;
}
protocol GroupAgreement<G: ScalarAction> {
  roles (Sender, Receiver);
  outputs (Receiver accepted: bool);
  let point = local Sender {
    Generator::<G>()
  };
  message generator: Sender(point) -> Receiver(received);
  let accepted = local Receiver {
    CheckGenerator::<G>(received)
  };
  finish {
    accepted
  };
}
entry main = GroupAgreement::<G = "bls12-381.g1">;

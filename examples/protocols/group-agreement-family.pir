// A group-valued interaction family, separate from polynomial protocols.
// This checks the generator contract and message typing, not a proof system.
module {
  fn Generator<G: ScalarAction>() -> G::Element {
    let point = curve::generator::<G>();
    return point;
  }

  fn CheckGenerator<G: ScalarAction>(point: G::Element) -> bool {
    let expected = curve::generator::<G>();
    let same = curve::equal::<G>(point, expected);
    control::require(same);
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
}

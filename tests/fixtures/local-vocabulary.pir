// Check one selected equation from a runtime commitment batch. The flag changes
// only the resulting predicate: selection and equality have already executed.
module {
  fn BatchCheck<G: domain Group>(
    batch: Vector<G::Element>,
    query: index,
    expected: G::Element,
    enabled: bool
  ) -> (bool, index) requires (ScalarAction(G)) {
    [length] let length = curve::length::<G>(batch);
    [selected] let selected = curve::get::<G>(batch, query);
    [equation] let equation = curve::equal::<G>(selected, expected);
    [disabled] let disabled = bool::not(enabled);
    [accepted] let accepted = bool::or(disabled, equation);
    return (accepted, length);
  }

  configure Check = BatchCheck(G = bls12-381.g1);
  protocol Main {
    roles (V);
    inputs (
      V batch: Vector<"bls12-381.g1"::Element>,
      V query: index,
      V expected: "bls12-381.g1"::Element,
      V enabled: bool
    );
    outputs (V bool, V index);
    local [check] V: let (accepted, length) = Check(batch, query, expected, enabled);
    return (accepted, length);
  }

  instance root: Main {
    roles (V = V);
  }

  entry main = root;
}

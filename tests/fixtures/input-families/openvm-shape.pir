// Minimal received-metadata contract: [rounds, width]. Full AIR/VK admission is
// deliberately outside this fixture. The stored selector requires width one.
module {
  fn Select(metadata: Indices) -> index {
    let size = metadata.len();
    let shaped = index::equal(size, 2);
    control::require(shaped);
    let rounds = metadata[0];
    let width = metadata[1];
    let supported = index::equal(width, 1);
    control::require(supported);
    return rounds;
  }
  fn Zero() -> index { return 0; }
  fn Step(value: index) -> index { let next = value + 1; return next; }
  protocol Family {
    roles (P, V);
    parameters (rounds);
    inputs (P metadata: Indices, V receivedMetadata: Indices);
    outputs (P index, V index);
    local [startP] P: let p = Zero();
    local [startV] V: let v = Zero();
    loop [round] rounds carry (a = p, b = v) -> (x, y) {
      local [step] P: let next = Step(a);
      message [roundMessage] index: P(next) -> V(got);
      yield (next, got);
    }
    return (x, y);
  }
  instance Main: Family {
    parameters (rounds = ingress(10, P = Select(metadata), V = Select(receivedMetadata)));
    roles (P = P, V = V);
  }
  entry main = Main;
}

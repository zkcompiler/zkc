// Each successful selector spends external work before checking actual metadata.
// Three absorbs require no trusted permutation reply in the Lean reference.
module {
  fn Select(metadata: Indices, n: index) -> index {
    let state = external::openvm::init();
    let reached = external::openvm::observe(state, metadata);
    if index::equal(n, 98) {
      let (after, sample) = external::openvm::sample_bits(reached, n);
    }
    let malformed = index::equal(n, 99);
    let accepted = bool::not(malformed);
    control::require(accepted);
    return n;
  }
  protocol Family {
    roles (Worker);
    parameters (rounds, earlier);
    inputs (Worker metadata: Indices, Worker first: index, Worker later: index);
    outputs (Worker index);
    loop [round] rounds carry (a = first) -> (out) {
      yield (a);
    }
    return out;
  }
  instance Main: Family {
    parameters (
      rounds = ingress(10, Worker = Select(metadata, later)),
      earlier = ingress(10, Worker = Select(metadata, first))
    );
    roles (Worker = Worker);
  }
  entry main = Main;
}

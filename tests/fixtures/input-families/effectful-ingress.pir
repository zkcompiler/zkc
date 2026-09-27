// Each successful selector spends external work before checking actual metadata.
// Three absorbs require no trusted permutation reply in the Lean reference.
module {
  use zkc::external;
  use zkc::algebra::{Indices};
  use zkc::algebra;
  use zkc::core;
  fn Select(metadata: Indices, n: index) -> index {
    let state = zkc::external::openvm_init();
    let reached = zkc::external::openvm_observe(state, metadata);
    if zkc::algebra::index_equal(n, 98) {
      let (after, sample) = zkc::external::openvm_sample_bits(reached, n);
    }
    let malformed = zkc::algebra::index_equal(n, 99);
    let accepted = zkc::core::not(malformed);
    zkc::core::require(accepted);
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

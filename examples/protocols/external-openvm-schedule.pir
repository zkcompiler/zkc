// Replay an explicit caller-authored observe/sample schedule. Operations do not
// know proof fields or automatically observe serialization. Zero denotes an
// observation; one a sample, and all other event tags are rejected.
module {
  use zkc::external;
  use zkc::algebra::{Indices};
  use zkc::algebra;
  use zkc::core;
  fn Schedule(tags: Indices, values: Indices) -> (Indices, Indices) {
    let same = zkc::algebra::index_equal(tags.len(), values.len());
    zkc::core::require(same);
    let mut state = zkc::external::openvm_init();
    let mut challenges = zkc::algebra::indices_empty();
    for i in 0..tags.len() {
      let tag = tags[i];
      let observing = zkc::algebra::index_equal(tag, 0);
      if observing {
        let empty = zkc::algebra::indices_empty();
        let input = zkc::algebra::indices_append(empty, values[i]);
        state = zkc::external::openvm_observe(state, input);
      } else {
        let sampling = zkc::algebra::index_equal(tag, 1);
        zkc::core::require(sampling);
        let (next, value) = zkc::external::openvm_sample(state);
        state = next;
        challenges = zkc::algebra::indices_append(challenges, value);
      }
    }
    return (state, challenges);
  }
  protocol Replay {
    roles (Worker);
    inputs (Worker tags: Indices, Worker values: Indices);
    outputs (Worker Indices, Worker Indices);
    local [schedule] Worker: let (state, challenges) = Schedule(tags, values);
    return (state, challenges);
  }
  entry main = Replay;
}

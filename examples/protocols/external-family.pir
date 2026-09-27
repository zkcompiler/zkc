// Input-selected protocol control and exact external transitions compose in one
// stored body. This is a schedule replay, not a complete OpenVM proof algorithm.
module {
  use zkc::external;
  use zkc::algebra::{Indices};
  use zkc::algebra;
  use zkc::core;
  fn Select(tags: Indices, values: Indices) -> index {
    let same = zkc::algebra::index_equal(tags.len(), values.len());
    zkc::core::require(same);
    return tags.len();
  }
  fn Start() -> (Indices, Indices, index) {
    return (zkc::external::openvm_init(), zkc::algebra::indices_empty(), 0);
  }
  fn Step(state: Indices, challenges: Indices, cursor: index,
          tags: Indices, values: Indices) -> (Indices, Indices, index) {
    let mut next = state;
    let mut samples = challenges;
    if zkc::algebra::index_equal(tags[cursor], 0) {
      let input = zkc::algebra::indices_append(zkc::algebra::indices_empty(), values[cursor]);
      next = zkc::external::openvm_observe(state, input);
    } else {
      zkc::core::require(zkc::algebra::index_equal(tags[cursor], 1));
      let (sampled, value) = zkc::external::openvm_sample(state);
      next = sampled;
      samples = zkc::algebra::indices_append(challenges, value);
    }
    return (next, samples, cursor + 1);
  }
  protocol Replay {
    roles (Worker);
    parameters (events);
    inputs (Worker tags: Indices, Worker values: Indices);
    outputs (Worker Indices, Worker Indices);
    local [start] Worker: let (state, samples, cursor) = Start();
    loop [event] events carry (s = state, c = samples, i = cursor, t = tags, v = values) -> (end, output, done, heldTags, heldValues) {
      local [step] Worker: let (next, nextSamples, nextIndex) = Step(s, c, i, t, v);
      yield (next, nextSamples, nextIndex, t, v);
    }
    return (end, output);
  }
  instance Main: Replay {
    parameters (events = ingress(64, Worker = Select(tags, values)));
    roles (Worker = Worker);
  }
  entry main = Main;
}

// Input-selected protocol control and exact external transitions compose in one
// stored body. This is a schedule replay, not a complete OpenVM proof algorithm.
module {
  fn Select(tags: Indices, values: Indices) -> index {
    let same = index::equal(tags.len(), values.len());
    control::require(same);
    return tags.len();
  }
  fn Start() -> (Indices, Indices, index) {
    return (external::openvm::init(), indices::empty(), 0);
  }
  fn Step(state: Indices, challenges: Indices, cursor: index,
          tags: Indices, values: Indices) -> (Indices, Indices, index) {
    let mut next = state;
    let mut samples = challenges;
    if index::equal(tags[cursor], 0) {
      let input = indices::append(indices::empty(), values[cursor]);
      next = external::openvm::observe(state, input);
    } else {
      control::require(index::equal(tags[cursor], 1));
      let (sampled, value) = external::openvm::sample(state);
      next = sampled;
      samples = indices::append(challenges, value);
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

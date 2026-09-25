// Replay an explicit caller-authored observe/sample schedule. Operations do not
// know proof fields or automatically observe serialization. Zero denotes an
// observation; one a sample, and all other event tags are rejected.
module {
  fn Schedule(tags: Indices, values: Indices) -> (Indices, Indices) {
    let same = index::equal(tags.len(), values.len());
    control::require(same);
    let mut state = external::openvm::init();
    let mut challenges = indices::empty();
    for i in 0..tags.len() {
      let tag = tags[i];
      let observing = index::equal(tag, 0);
      if observing {
        let empty = indices::empty();
        let input = indices::append(empty, values[i]);
        state = external::openvm::observe(state, input);
      } else {
        let sampling = index::equal(tag, 1);
        control::require(sampling);
        let (next, value) = external::openvm::sample(state);
        state = next;
        challenges = indices::append(challenges, value);
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

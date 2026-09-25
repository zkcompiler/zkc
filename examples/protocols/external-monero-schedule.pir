// A caller-authored grouped hash schedule. The proof-container mapping stays
// outside this function: lengths explicitly delimit each hash-chain call.
module {
  fn Schedule(initial: Indices, commitments: Indices, messages: Indices, lengths: Indices) -> (Indices, Indices) {
    let first = external::monero::init(initial);
    let digest = external::monero::hash(commitments);
    let (bound, _) = external::monero::update(first, digest);
    let mut state = bound;
    let mut checkpoints = indices::empty();
    let mut cursor: index = 0;
    for group in 0..lengths.len() {
      let mut items = indices::empty();
      for j in 0..lengths[group] {
        items = indices::append(items, messages[cursor]);
        cursor = index::add(cursor, 1);
      }
      let (next, challenge) = external::monero::update(state, items);
      state = next;
      for byte in 0..challenge.len() {
        checkpoints = indices::append(checkpoints, challenge[byte]);
      }
    }
    let complete = index::equal(cursor, messages.len());
    control::require(complete);
    return (state, checkpoints);
  }
  protocol Replay {
    roles (Worker);
    inputs (Worker initial: Indices, Worker commitments: Indices, Worker messages: Indices, Worker lengths: Indices);
    outputs (Worker Indices, Worker Indices);
    local [schedule] Worker: let (state, checkpoints) = Schedule(initial, commitments, messages, lengths);
    return (state, checkpoints);
  }
  entry main = Replay;
}

// A caller-authored grouped hash schedule. The proof-container mapping stays
// outside this function: lengths explicitly delimit each hash-chain call.
use zkc::external;
use zkc::algebra::{
  Indices
};
use zkc::algebra;
use zkc::core;
fn Schedule(
  initial: Indices,
  commitments: Indices,
  messages: Indices,
  lengths: Indices
) -> (Indices, Indices) {
  let first = zkc::external::monero_init(initial);
  let digest = zkc::external::monero_hash(commitments);
  let (bound, _) = zkc::external::monero_update(first, digest);
  let mut state = bound;
  let mut checkpoints = zkc::algebra::indices_empty();
  let mut cursor: index = 0;
  for group in 0..lengths.len() {
    let mut items = zkc::algebra::indices_empty();
    for j in 0..lengths[group] {
      items = zkc::algebra::indices_append(items, messages[cursor]);
      cursor = zkc::algebra::index_add(cursor, 1);
    }
    let (next, challenge) = zkc::external::monero_update(state, items);
    state = next;
    for byte in 0..challenge.len() {
      checkpoints = zkc::algebra::indices_append(checkpoints, challenge[byte]);
    }
  }
  let complete = zkc::algebra::index_equal(cursor, messages.len());
  zkc::core::require(complete);
  return (state, checkpoints);
}
protocol Replay {
  roles (Worker);
  inputs (
    Worker initial: Indices,
    Worker commitments: Indices,
    Worker messages: Indices,
    Worker lengths: Indices
  );
  outputs (Worker Indices, Worker Indices);
  local [schedule] Worker: let (state, checkpoints) = Schedule(
    initial,
    commitments,
    messages,
    lengths
  );
  return (state, checkpoints);
}
entry main = Replay;

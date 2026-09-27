// Shape gate only: original encoded 32-byte commitments and L/R point arrays.
// Scalar/point decoding and complete BP+ verification belong to the adapter.
module {
  use zkc::algebra::{Indices};
  use zkc::algebra;
  use zkc::core;
  fn ByteLength(values: Indices) -> index {
    let length = values.len();
    for i in 0..length {
      let byte = values[i];
      let valid = zkc::algebra::index_less(byte, 256);
      zkc::core::require(valid);
    }
    return length;
  }
  fn Select(commitments: Indices, left: Indices, right: Indices) -> index {
    let bytes = ByteLength(commitments);
    let leftBytes = ByteLength(left);
    let rightBytes = ByteLength(right);
    let width = 32;
    let count = zkc::algebra::index_div(bytes, width);
    let exact = zkc::algebra::index_equal(zkc::algebra::index_mod(bytes, width), 0);
    zkc::core::require(exact);
    let nonempty = zkc::algebra::index_less(0, count);
    zkc::core::require(nonempty);
    let bounded = zkc::algebra::index_less(count, 17);
    zkc::core::require(bounded);
    let mut capacity = 1;
    let mut rounds = 6;
    for i in 0..4 {
      if zkc::algebra::index_less(capacity, count) {
        capacity = capacity * 2;
        rounds = rounds + 1;
      }
    }
    let roundBytes = rounds * width;
    let leftOK = zkc::algebra::index_equal(leftBytes, roundBytes);
    zkc::core::require(leftOK);
    let rightOK = zkc::algebra::index_equal(rightBytes, roundBytes);
    zkc::core::require(rightOK);
    return rounds;
  }
  fn Zero() -> index { return 0; }
  fn Step(value: index) -> index { let next = value + 1; return next; }
  protocol Family {
    roles (P, V);
    parameters (rounds);
    inputs (P commitments: Indices, P left: Indices, P right: Indices,
            V receivedCommitments: Indices, V receivedLeft: Indices, V receivedRight: Indices);
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
    parameters (rounds = ingress(10, P = Select(commitments, left, right), V = Select(receivedCommitments, receivedLeft, receivedRight)));
    roles (P = P, V = V);
  }
  entry main = Main;
}

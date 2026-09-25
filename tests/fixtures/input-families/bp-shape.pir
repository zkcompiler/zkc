// Shape gate only: original encoded 32-byte commitments and L/R point arrays.
// Scalar/point decoding and complete BP+ verification belong to the adapter.
module {
  fn ByteLength(values: Indices) -> index {
    let length = values.len();
    for i in 0..length {
      let byte = values[i];
      let valid = index::less(byte, 256);
      control::require(valid);
    }
    return length;
  }
  fn Select(commitments: Indices, left: Indices, right: Indices) -> index {
    let bytes = ByteLength(commitments);
    let leftBytes = ByteLength(left);
    let rightBytes = ByteLength(right);
    let width = 32;
    let count = index::div(bytes, width);
    let exact = index::equal(index::mod(bytes, width), 0);
    control::require(exact);
    let nonempty = index::less(0, count);
    control::require(nonempty);
    let bounded = index::less(count, 17);
    control::require(bounded);
    let mut capacity = 1;
    let mut rounds = 6;
    for i in 0..4 {
      if index::less(capacity, count) {
        capacity = capacity * 2;
        rounds = rounds + 1;
      }
    }
    let roundBytes = rounds * width;
    let leftOK = index::equal(leftBytes, roundBytes);
    control::require(leftOK);
    let rightOK = index::equal(rightBytes, roundBytes);
    control::require(rightOK);
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

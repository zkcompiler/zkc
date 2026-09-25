// The host searches on transcript clones; this body commits exactly one selected
// witness. It is a construction-boundary fixture, not a complete proof system.
module {
  fn Check(state: Indices, bits: index, witness: index) -> (Indices, bool) {
    let (next, accepted) = external::openvm::check_witness(state, bits, witness);
    return (next, accepted);
  }
  protocol Commit {
    roles (Worker);
    inputs (Worker state: Indices, Worker bits: index, Worker witness: index);
    outputs (Worker Indices, Worker bool);
    local Worker: let (next, accepted) = Check(state, bits, witness);
    return (next, accepted);
  }
  entry main = Commit;
}

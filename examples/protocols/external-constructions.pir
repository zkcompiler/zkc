// Atomic exact external constructions, with explicit copyable data state.
// Indices here are checked bytes/words, not nominal group or field values.
use zkc::external;
use zkc::algebra::{
  Indices
};
use zkc::algebra;
fn Chain(initial: Indices, commitments: Indices, r#message: Indices) -> (Indices, Indices, Indices) {
  let state = zkc::external::monero_init(initial);
  let digest = zkc::external::monero_hash(commitments);
  let (bound, _) = zkc::external::monero_update(state, digest);
  let (next, challenge) = zkc::external::monero_update(bound, r#message);
  let empty = zkc::algebra::indices_empty();
  let (last, empty_challenge) = zkc::external::monero_update(next, empty);
  return (last, challenge, empty_challenge);
}
fn Duplex(
  observations: Indices,
  bits: index,
  witness: index
) -> (Indices, index, Indices, index, bool, Indices, bool) {
  let state = zkc::external::openvm_init();
  let observed = zkc::external::openvm_observe(state, observations);
  let (sampled, challenge) = zkc::external::openvm_sample(observed);
  let (extended, extension) = zkc::external::openvm_sample_ext(sampled);
  let (masked, bit_challenge) = zkc::external::openvm_sample_bits(extended, bits);
  let (checked, accepted) = zkc::external::openvm_check_witness(masked, bits, witness);
  let (unchanged, zero_ok) = zkc::external::openvm_check_witness(checked, 0, witness);
  return (unchanged, challenge, extension, bit_challenge, accepted, masked, zero_ok);
}
protocol ChainDemo {
  roles (Worker);
  inputs (Worker initial: Indices, Worker commitments: Indices, Worker r#message: Indices);
  outputs (Worker Indices, Worker Indices, Worker Indices);
  local [chain] Worker: let (state, challenge, empty_challenge) = Chain(
    initial,
    commitments,
    r#message
  );
  return (state, challenge, empty_challenge);
}
protocol DuplexDemo {
  roles (Worker);
  inputs (Worker observations: Indices, Worker bits: index, Worker witness: index);
  outputs (
    Worker Indices,
    Worker index,
    Worker Indices,
    Worker index,
    Worker bool,
    Worker Indices,
    Worker bool
  );
  local [duplex] Worker: let (
    state,
    challenge,
    extension,
    bit_challenge,
    accepted,
    before_check,
    zero_ok
  ) = Duplex(observations, bits, witness);
  return (state, challenge, extension, bit_challenge, accepted, before_check, zero_ok);
}
entry monero = ChainDemo;
entry openvm = DuplexDemo;

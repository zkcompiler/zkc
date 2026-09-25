// Atomic exact external constructions, with explicit copyable data state.
// Indices here are checked bytes/words, not nominal group or field values.
module {
  fn Chain(initial: Indices, commitments: Indices, message: Indices) -> (Indices, Indices, Indices) {
    let state = external::monero::init(initial);
    let digest = external::monero::hash(commitments);
    let (bound, _) = external::monero::update(state, digest);
    let (next, challenge) = external::monero::update(bound, message);
    let empty = indices::empty();
    let (last, empty_challenge) = external::monero::update(next, empty);
    return (last, challenge, empty_challenge);
  }
  fn Duplex(observations: Indices, bits: index, witness: index) -> (Indices, index, Indices, index, bool, Indices, bool) {
    let state = external::openvm::init();
    let observed = external::openvm::observe(state, observations);
    let (sampled, challenge) = external::openvm::sample(observed);
    let (extended, extension) = external::openvm::sample_ext(sampled);
    let (masked, bit_challenge) = external::openvm::sample_bits(extended, bits);
    let (checked, accepted) = external::openvm::check_witness(masked, bits, witness);
    let (unchanged, zero_ok) = external::openvm::check_witness(checked, 0, witness);
    return (unchanged, challenge, extension, bit_challenge, accepted, masked, zero_ok);
  }
  protocol ChainDemo {
    roles (Worker);
    inputs (Worker initial: Indices, Worker commitments: Indices, Worker message: Indices);
    outputs (Worker Indices, Worker Indices, Worker Indices);
    local [chain] Worker: let (state, challenge, empty_challenge) = Chain(initial, commitments, message);
    return (state, challenge, empty_challenge);
  }
  protocol DuplexDemo {
    roles (Worker);
    inputs (Worker observations: Indices, Worker bits: index, Worker witness: index);
    outputs (Worker Indices, Worker index, Worker Indices, Worker index, Worker bool, Worker Indices, Worker bool);
    local [duplex] Worker: let (state, challenge, extension, bit_challenge, accepted, before_check, zero_ok) = Duplex(observations, bits, witness);
    return (state, challenge, extension, bit_challenge, accepted, before_check, zero_ok);
  }
  entry monero = ChainDemo;
  entry openvm = DuplexDemo;
}

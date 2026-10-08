# External construction primitives

`zkc_backends::external` supplies native primitives and an explicit wire/event
boundary. It adds no zkc prefix. Artifact-bound Merlin/Spongefish providers are
separate and unchanged by this module. Protocol code owns item grouping, event
order, guards, initialization, attempts, and proof encoding.

## Native integration

- `monero::hash_to_scalar(&[Word])`: stateless Keccak-256 over concatenated raw
  32-byte words, followed by little-endian scalar reduction using dalek. Empty
  input still hashes. `Word = [u8;32]`; point encodings are never cleared/decoded.
- `monero::HashChain::new(initial)`, `.state()`, `.update(&[Word])`: exactly
  `Hs(state || items)`. Empty update means `Hs(state)`. A grouped call is not a
  sequence of single-item calls. All scalar outputs, including zero, are returned.
  The protocol's separate zero-challenge policy decides retry/rejection.
- `openvm::Duplex::new()`: zero state, width 16, rate 8, overwrite absorption,
  descending sample positions. `.observe(&[u32])` validates the full canonical
  BabyBear slice before mutation. Empty observation does nothing. `.sample()`
  returns a `Transition<u32>` with value and exact logical work.
- `.sample_ext()` returns four ordered BabyBear basis coefficients, not a
  cross-version p3 extension object. `.sample_bits(bits)` takes one sample then
  masks its canonical integer; the conversion is separately exposed as
  `challenge_bits`. This matches the pinned biased sampler, not a uniform sampler.
- `.check_witness(bits,witness)` mutates live state on both acceptance and
  rejection. `.trial_witness` checks a clone; live state remains untouched, while
  returned work is still consumed work. Zero-bit checks produce no events;
  `sample_bits(0)` DOES consume one sample. Widths 0..=30 are admitted; invalid
  parameters and noncanonical fields return stable `Error` codes before mutation.
- `.snapshot()` returns all 16 canonical state words and both indices. Pending
  absorbs overwrite state immediately. This is the pinned OpenVM representation,
  rather than Plonky3's different buffered internal representation.
  `Duplex::from_snapshot(snapshot)` imports an explicit data state after checking
  all field encodings and both cursor ranges. It validates representation, not
  reachability from zero or authorization to restore a runtime capability.

Adapters must charge resource caps **before** mutation: use
`monero::hash_work(count,include_state)` or duplex
`observe_work(count)`, `sample_work(count)`, `witness_work(bits)`. Returned `Work`
records hash calls/bytes, permutations, observes and samples. These are logical
counts, not elapsed time, allocation/copy costs, randomness consumption, or a
security estimate. In particular clone/search costs need the owner's own
accounting. The primitive helpers install no global counters, RNG or private
attempt buffers. The owning runtime controls handle
identity, snapshot/cloning authorization, capacity, and complete outcomes.

All primitive errors are returned as `external:*` codes. The main adapter selects
the enclosing malformed/refused/exhausted policy; a false witness predicate is a
normal result with its actual state effects. The provider knows no BP+ rounds or
SWIRL stages. Application statement/VK binding remains the caller's responsibility.

## Source/version boundary

[provenance.json](provenance.json) pins exact upstream revisions, six source-file
hashes, crypto crate archive hashes, and the 35 archived fixture files. OpenVM
state transitions are adapted from stark-backend v2.0.1's `DuplexSponge` and
`FiatShamirTranscript`; upstream licenses are retained alongside this file.

The permutation comes directly from `p3-baby-bear =0.4.3`'s
`default_babybear_poseidon2_16`, the constructor used by pinned OpenVM. Field and
symmetric traits are aliased to the same version. No equivalence to workspace
0.5.1 is assumed. Differential tests use p3-challenger 0.4.3's separately
implemented `DuplexChallenger`. Both paths trust the same crypto permutation.

Monero hash and reduction use RustCrypto sha3 0.10.9 (`Keccak256`, **not**
`Sha3_256`) and curve25519-dalek 4.1.3. The saved `BP_PLUS_INITIAL` is an encoded
hash-to-point constant from the pinned upstream harness; this crate does not
implement or independently prove its hash-to-point derivation. Six additional
primitive vectors use the retained pinned native `cn_fast_hash` shared library
and independent Python integer reduction, including empty input.

## Independent validation

`cargo test -p zkc-backends --test external_transcript --all-features` compares
installed primitives with separately implemented pinned challenger transitions
and saved Keccak/scalar vectors. Native authored `external.*` operations also
exercise persistent resource accounting, snapshots, invalid-input refusal and
failed witness checks. Protocol methods own their explicit trial loops and
proof framing. No standalone replay, wire-map or grinding service is installed.

Passing these tests establishes finite primitive correspondence. It does not
establish full external proof verification, decoder/acceptance-set equivalence,
protocol security or a performance claim.

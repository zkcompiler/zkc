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

`grinding::Search` owns a candidate provider, an explicit role/purpose namespace,
and the fixed transcript seed. `advance(fuel)` runs a finite prefix on clones;
its candidate-call limit and `Work::units()` ceiling persist across resumptions.
Provider failures and exhausted deployment budgets stop permanently with retained
counters. Invalid candidates consume a provider call but no cryptographic work.
Zero difficulty returns witness zero without a provider call or trial. Finding
a witness does not mutate a live transcript: the caller explicitly checks that
witness once, including through `external.openvm.check_witness`. A direct failed
check retains its state effects. This sequential driver does not reproduce the
upstream parallel search's choice order or establish a search-success bound.

`WireMap::new(Vec<WireItem>)` admits named values and origins with optional
container positions. Construction never changes a transcript. A wire item is a
vector of raw words, canonical fields, or opaque bytes. `validate_mapping` checks
coverage against explicit observed item identities and `Unobserved {item,guard}`
obligations. Duplicate identities/positions, missing items, uncovered items,
conflicting classifications, and empty guard identities refuse. Repeated
observations are allowed because the selected protocol decides whether they are
required. A guard identity **does not execute or prove** a verifier guard.

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

## JSON replay interface, version 1

```sh
cargo run --offline --locked -p zkc-backends --example external_replay -- input.json
# Omit path, or use -, to read stdin. Success: one JSON result. Failure: exit 1.
```

A document has exactly these members:

```json
{
  "version": 1,
  "profile": "openvm-babybear-poseidon2-v1",
  "items": [
    {"id":"vk", "origin":"application:vk", "wire_index":null,
     "kind":"fields", "values":[17,19]},
    {"id":"response", "origin":"proof:opening", "wire_index":0,
     "kind":"opaque", "values":"1234"}
  ],
  "unobserved": [{"item":"response", "guard":"protocol:authenticated-opening"}],
  "events": [
    {"op":"observe", "items":["vk"]},
    {"op":"sample_ext"},
    {"op":"sample_bits", "bits":3},
    {"op":"trial_witness", "bits":3, "witness":17}
  ]
}
```

`wire_index` is a distinct container ordinal or `null` for external/derived
inputs. It never sorts events. `origin` is required descriptive source metadata,
not an authenticated identity. `kind` is `words` (array of 64 lowercase hex digit
strings), `fields` (array of canonical u32 values), or `opaque` (lowercase hex).
Each named item must be referenced or listed once in `unobserved`. Opaque items
cannot feed a primitive directly; the protocol must decode them into typed items.

Profiles and events:

| Profile | Events |
|---|---|
| `monero-hash-chain-v1` | Required `initial`: 64 hex digits. `hash` with `items` and unique `output` computes a stateless scalar hash, available by that name to later events. `update` with `items` updates the chain. `items:[]` is allowed in both. |
| `openvm-babybear-poseidon2-v1` | No `initial` member. `observe` with `items`; `sample`; `sample_ext`; `sample_bits` with `bits`; `check_witness` or `trial_witness` with `bits,witness`. |

Every event optionally accepts `expect` and `expect_state`. `expect` matches the
result: hex word for hash/update, null for observe, integer for sample/bits, four
integers for extension, boolean for witness checks. `expect_state` matches either
the chain's hex word or `{ "state": [16 integers], "absorb_index": n,
"sample_index": n }`. A mismatch fails replay. Expected values never influence
primitive calculations. Stateless hash and clone trials leave live state intact.

Output contains `version`, `profile`, `checkpoints`, and total `work`. Each
checkpoint contains `index`, `op`, `value`, live `state`, and `work`. Trial work is
included in total work even though its events do not enter the live transcript.
This lets a separate schedule interpreter compare every transition and convert
challenges independently while treating Keccak/Poseidon2 as explicit trusted
primitives. The CLI is a diagnostic replayer, not the complete-outcome runtime;
on malformed input/mismatch/exhaustion it exits without a partial result.

Duplicate JSON keys, unknown members/operations, noninteger inputs, forward or
missing references, wrong value kinds, invalid hex, trailing data, and invalid
profile/parameter combinations refuse. The tool bounds ingress bytes, item/event
counts, per-event values, hashed bytes and permutations through `replay::Limits`.
`replay_json` is the byte ingress; `replay(&Value,limits)` assumes JSON has already
been decoded and cannot retrospectively detect duplicate keys.

## Real fixture replay

```sh
cargo test --offline --locked -p zkc-backends --test external_transcript
python3 tests/external-transcripts/make_replays.py build/reports/external-replays
cargo run --offline --locked -p zkc-backends --example external_replay -- build/reports/external-replays/ordinary-monero-16.replay.json
cargo run --offline --locked -p zkc-backends --example external_replay -- build/reports/external-replays/ordinary-openvm-mixture-4.replay.json
```

The test-only Python converter authors 20 schedules. BP+ decodes bounded saved
proof containers and combines separately supplied V, proving the distinction
between wire order and hash-call grouping. It covers ordinary/instrumented sizes
1,2,3,4,8,9,16 and one accepted consistent-torsion fixture. Native tests author the
same schedule independently in Rust. OpenVM converts all 6,871 recorded scalar
observe/sample events from five real proof executions, including two 12-AIR
interaction/cached/preprocessed mixtures. Their log-origin identities do not
claim a full OpenVM container-field decoder. Synthetic omission tests exercise
mapping obligations separately; full proof-field mapping belongs to the protocol.

Passing replay establishes finite checkpoint correspondence only. It does not
establish proof verification, full decoder/acceptance-set equivalence, native
compiler or Lean integration, full OpenVM guest/recursive endpoints, production
security parameters, independent cryptographic proofs, or a performance claim.

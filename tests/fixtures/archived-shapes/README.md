# Archived input-family shapes

Frozen inputs for `tests/protocol/test_archived_families.py`, which executes
metadata extracted from real archived proofs through ordinary stored PIR
selector functions, native participants, and the independent Lean common-source
interpreter. It supplements the synthetic corpus in `test_input_families.py`.

| file | what it is |
| --- | --- |
| `archives/` | the five OpenVM proof containers |
| `corpus.json` | metadata the pinned upstream typed decoders extracted from every archive, and typed mutations of it |
| `vk-*.json` | the verifying keys reconstructed for the three OpenVM configurations |
| `provenance.json` | the upstream repositories and commits, and the corpus hash |

The BP+ proofs and statements are the transcript corpus's own, under
`tests/fixtures/external-transcript/`. The test hash-binds the corpus, the archives
and the keys, and checks the BP+ V/L/R bytes and the key-derived dimensions
independently.

The corpus is frozen: the typed adapters that extracted it, and the research
inputs they read, are not part of this repository. What follows records how
it was extracted, against the upstream commits in `provenance.json`.

## Adapter boundary and source derivation

The typed Monero adapter uses the unmodified v0.18.5.1 binary codec and
`rct::BulletproofPlus` at revision
`4f92268d7c16741cfb41e5bbe2aa46cc260a9ea5`. That codec omits `V`: it is external
statement data, restored exactly from the archived transcript's `V` array.
`L` and `R` come from decoding the actual proof container, never from an expected
round count. Codec re-encoding must recover exactly the input bytes. The adapter
also checks upstream acceptance, including the consistent-torsion archive.
The unchanged `tests/fixtures/input-families/bp-shape.pir` receives raw original bytes,
checks byte ranges, exact widths and L/R lengths, and computes
`6 + ceil(log2(|V|))`. It does not decode or normalize group elements.
The torsion archive is an accepted upstream proof whose altered A is outside
this V/L/R-only selector; passing shape admission is not a subgroup claim.

The typed OpenVM adapter uses `Proof<BabyBearPoseidon2Config>::decode` from
stark-backend v2.0.1, revision
`362c7ad8c6b042b320471a137e3eadec7ec69a44`. It consumes the whole archived proof
and requires exact codec re-encoding. It reconstructs the selected VK from the
configurations the archives were proved under: three optional Fibonacci AIRs,
or `MixtureFixture::standard(1/4, config)`, with `default_test_params_small()`.
Keygen runs; no new proofs are generated. The three optional cases share the
same reconstructed VK. The two mixtures have different preprocessed data/VKs.
Every original proof is verified by the pinned upstream verifier as a separate
extraction check; that result is never an input to PIR.

Source paths relative to the pinned stark-backend tree:

- `crates/stark-backend/src/proof.rs`: decoded proof/vector/TraceVData types.
- `crates/stark-backend/src/test_utils/mod.rs:478`: actual mixture AIR set and
  widths; `:581`: testing configuration (`l_skip=2`, `n_stack=8`).
- `crates/stark-backend/src/keygen/types.rs:196`: cached parts and number of
  interaction expressions from the symbolic AIR; widths/rotation/public-value
  counts are VK data, not proof assertions.
- `crates/stark-backend/src/verifier/proof_shape.rs:313`: absence, heights,
  public-value/cached counts; `:374`: present AIR order and GKR dimensions;
  `:418`: batch dimensions; `:479`: per-part opening widths.
- `crates/stark-backend/src/verifier/mod.rs:139`: preprocessed height must equal
  `hypercube_dim + l_skip` from the VK, even below `l_skip`.
- `crates/stark-backend/src/lib.rs:75`: interaction dimension uses the bit length
  of total interaction slots, including an extra bit at exact powers of two.

For each present AIR, padded row count is `2^max(log_height,l_skip)`. The total
interaction slots sum that count times the **number of interaction expressions
in the VK**. This is the shape dimension, not the sum of witness multiplicity
values, nor a check of the interaction count expressions/weights or trace-height
linear constraints. GKR layers are zero for total zero, otherwise its bit length.
Batch rounds are `max(0,max_present_log_height-l_skip)`.

PIR computes those dimensions itself and checks actual decoded GKR claim count,
outer and inner sumcheck vector lengths, batch polynomial count/width,
numerator/denominator count, univariate coefficient count, public-value count,
optional/required presence, cached commitment count, preprocessed height and
opening widths. Openings have width `VK_part_width * (1 + need_rot)` in common,
preprocessed (if any), cached order. It checks descending height/AIR-ID tie order
for the adapter's association of original opening vectors to AIRs. Expected
widths are never copied from received opening lengths.

`tests/support/shape_data.py` specifies the flat `Indices` schema and packs it without computing
expected rounds. The upstream typed decoder extracted the actual metadata;
`corpus.json` is its retained result. Actual vector lengths appear as claims
that PIR validates; they are never trusted as selectors.

## Authenticated configuration versus received proof

PIR takes two separate ports per role: caller-selected `key` metadata and
received `proof` metadata. The host/embedding must authenticate the selected
VK/config and bind the external statement. These fixtures record
and hash that key; they do not implement key authentication in PIR. Updating
both key and proof coherently can describe a different instance. A same-count
cross-role test deliberately passes two different archived metadata values to
show that count agreement does not establish metadata or statement equality.

The schema adapter is trusted to decode and associate fields correctly; its
provenance is evidence, not a formal decoder-refinement proof. Typed mutations
alter decoded proof fields without filtering them through upstream acceptance
before emission. Both native and Lean independently reject these metadata
values through the stored ordinary selector. The upstream decoders also emit
no metadata for a truncated container or one with trailing bytes.

## Finite execution evidence

| Archive family | Inputs | Computed schedule |
| --- | --- | --- |
| Ordinary/instrumented BP+ | each 1,2,3,4,8,9,16 commitments | 6,7,8,8,9,10,10 rounds |
| Consistent-torsion BP+ | one commitment | 6 rounds |
| Optional AIRs, cases 0/1/2 | heights [3,4,2], [3,absent,2], [absent,4,absent] in log2 | 2/1/2 batch rounds; zero GKR layers |
| Mixture, fixture log height 1 | 12 present AIRs, heterogeneous heights | 1 batch round + 8 GKR layers (216 interaction slots) |
| Mixture, fixture log height 4 | 12 present AIRs, heterogeneous heights | 2 batch rounds + 10 GKR layers (792 interaction slots) |

`openvm-archived-shape.pir` selects the sum of batch rounds and GKR layers for
one flat schedule skeleton. Each slot sends an incremented index. It is **not**
the full SWIRL execution schedule or arithmetic body. GKR inner vector dimensions
are checked in the selector; this does not execute GKR sumcheck arithmetic.
Both fixture protocols retain one symbolic loop, three round-body nodes, seven
protocol nodes including that body, and two projected participants. Ordinary
selector functions have their own stored bodies (six OpenVM functions, four BP+
functions); compactness does not mean those bodies are absent. Source/participant
hashes remain unchanged across inputs.

The OpenVM schema caps 32 AIRs, log heights 20, l_skip 16, constraint degree 16,
1024 interaction expressions/AIR, 4096 widths/public values and 16 cached
parts/AIR. These are explicit bounded-adapter restrictions, not upstream limits.
Within these bounds 40 bit-length steps and the family bound of 64 suffice.
The normal execution/resource limits remain active.

Limits: no full proof decoder inside PIR, no VK authentication, no proof
acceptance-set equivalence, no transcript/cryptographic verification by this
selector, no WHIR/stacking shape validation, trace-height linear-constraint check,
complete prover/verifier, recursion, production OpenVM configuration, dynamic
children, native/compiler refinement proof, or security/performance conclusion.
Native ingress stop and Lean logical reject are checked using their respective
APIs; this suite does not claim equality of their full physical failure traces.

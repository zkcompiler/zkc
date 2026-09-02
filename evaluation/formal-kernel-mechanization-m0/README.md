# M0 mechanized kernel definition spike

This package measures one bounded question: can the kernel laws that two
research packages mechanize by hand in Python be written as zkc-owned Lean 4
definitions that reproduce the existing Python goldens byte for byte, and what
does one small mechanically checked theorem cost? It is a measurement, not a
migration. The Lean text under `lean/` is definition text under test. It is
not normative: `docs-next/foundation/executable-foundations.md` Section 2 owns
the datum grammar and canonical encoding, and
`docs-next/pir/interactive-core.md` Section 11 and Appendix A own the
`PCClass` lattice, the Kahn order, and `PCNodeBody`. Agreement is claimed for
the exact vectors compared and for nothing else.

Run from the repository root:

```sh
python3 -B evaluation/formal-kernel-mechanization-m0/run.py --check
```

The frozen result is `Affirmative/M0-A-KERNEL-DEFINITIONS-REPRODUCE-GOLDENS`:
34 findings, 25 affirmative and nine `CannotAnswer`. The aggregate is
affirmative only because stages 1 to 3 reproduce every golden and the
stage 4 primary theorem checks without `sorry`.

## Toolchain

`lean/lean-toolchain` pins `leanprover/lean4:v4.33.1`. The Lean text uses the
libraries that ship with that toolchain and nothing else: no Mathlib,
Batteries, Std, VCVio, or ArkLib, and `lean/lakefile.lean` declares no
`require`. The kernel modules (`Datum`, `Encode`, `Decode`, `PCGraph`,
`Theorems`) import only each other; `Transport.lean` imports `Lean.Data.Json`
for the vector transport and `Main.lean` is the executable. `run.py` checks
these facts statically before it builds anything.

`run.py` locates `lake` through `ZKC_LAKE`, then `PATH`, then `~/.elan/bin`.
When elan manages it, the pinned toolchain must already be installed; the
gate never triggers a download. When no usable toolchain exists, the 18
Lean-dependent findings become `Unsupported/M0-U-LEAN-TOOLCHAIN`, the
aggregate becomes `CannotAnswer/M0-C-LEAN-TOOLCHAIN-UNAVAILABLE`, and
`--check` exits 1 with the reason on standard error. It never passes without
building and running the Lean text.

## Contents

| Path | What it holds |
|---|---|
| `lean/M0/Datum.lean` | The datum type: the ten Foundation forms as nine constructors, with one `Bool` constructor for the two Boolean tags exactly as the Python model's host `bool` and the page's `MetaBooleanDatum`; `wellFormed`; root-zero `depth`, `nodes`, `edges`; a hand-written `beq`. |
| `lean/M0/Encode.lean` | `u64`, the minimal `magnitude`, `frame`, the total `encode`, the four constitutional limits, `encodeChecked`; the arithmetic lemmas that read fixed-width and minimal magnitudes back. |
| `lean/M0/Decode.lean` | `readOctets`, `readU64`, `readFrame`, the fuel-indexed `parse` that consumes exactly one value, and the strict `decode` (no trailing octets, byte limit on input, the other three limits on the value, fuel equal to the depth limit plus one). |
| `lean/M0/PCGraph.lean` | `PCClass`, `Join` as Section 11 writes it, `Publish`, `pcNodeBody` from Appendix A, lexicographic `lexLt`, `kahnOrder` with the least-body tie-break, the `Transfer` kinds, `challengeClass` in the D1 reading and in the positional reading, and `foldClasses`. |
| `lean/M0/Theorems.lean` | `parse_encode` and its corollaries `decode_encode`, `encode_injective`, `encode_prefix_free`, `encodeChecked_injective`; `Join_cons`, `Join_eq_foldr`, the lattice laws of the binary join, `Publish_idem`. |
| `lean/M0/Transport.lean`, `lean/Main.lean` | The oracle's JSON value transport read into a datum, hex, the carrier tables, and the `lake exe m0 <input.json>` report. |
| `lean/Axioms.lean` | `#print axioms` for every statement the findings rely on; `run.py` elaborates it after the build. |
| `export_vectors.py` | Deterministic export of the goldens from the two predecessor packages; `--check` compares a fresh export with `vectors/`. |
| `vectors/` | The committed goldens (below). |
| `run.py`, `expected-findings.json` | The gate and its frozen 34 findings. |

## Vectors

| File | Source | Content |
|---|---:|---|
| `k1-encoding-vectors.json` | `evaluation/k1-executable-foundations/oracle/cases` | The 12 frozen oracle cases whose expected record carries a canonical body (four `encode`, one `decode`, three prior-meta descriptor bodies, four ordinary subject bodies) in the oracle's JSON transport with their hex, and the two malformed `decode` cases. Ten cases without a canonical body, and the `resource-wide` case that exercises the oracle's local resource profile rather than a constitutional rule, are listed as skipped. |
| `structural-negatives.json` | Foundation Section 2.1 malformation list | 23 crafted octet strings, one per named malformation (unknown tag, trailing octet, empty or overlong magnitude, negative zero, bad sign, empty or non-printable symbol, length disagreement, short counts, child frames with trailing octets, duplicate and unsorted ordinals, missing payloads); each is confirmed refused by the K1 Python decoder at export time. |
| `body-digests.json` | `evaluation/formal-source-integrated-graph-f0v2b2d1` | The length and SHA-256 of the five profiled Core bodies and five `PublicCoinView` bodies. They total about 430 KiB, so the gate regenerates them from the D1 typed model, checks the digests, and hands them to Lean as hex plus transport. |
| `pcgraph-tables.json` | D1 `derive_graph` | For each of the five carriers: the 91 nodes with tag, reference arguments, and canonical body bytes; the 151 or 146 edges; the per-node transfer kind; and the expected topological order and class table. |

The Lean executable receives 22 encode vectors (12 oracle, five Core bodies,
five `PublicCoinView` bodies), 25 reject vectors, and five carrier tables.

## Stages and findings

| Stage | Findings | Result |
|---|---|---|
| Pins | `M0-A-PREDECESSOR-PIN`, `M0-A-TARGET-LAW-PIN`, `M0-A-NONPUBLICATION`, `M0-A-VECTOR-EXPORT-STABLE`, `M0-A-CORE-LEAN-ONLY`, `M0-A-LEAN-BUILD` | D1 findings, oracle case files, the law sentences, and the export are pinned; the Lean text has no external dependency, `sorry`, or `axiom`; it builds. |
| 1. Datum type and encoder | `M0-A-S1-K1-ORACLE-VECTORS`, `M0-A-S1-CORE-BODIES`, `M0-A-S1-PUBLIC-COIN-BODIES`, `M0-A-S1-ENCODER-REPRODUCES-GOLDENS` | `encodeChecked` of the transport value equals the golden bytes for all 22 bodies. |
| 2. Decoder and round trip | `M0-A-S2-ROUNDTRIP`, `M0-A-S2-ORACLE-REJECTS`, `M0-A-S2-CRAFTED-REJECTS`, `M0-A-S2-DECODER-REPRODUCES-GOLDENS`; `CannotAnswer` `M0-C-NAT-BYTE-BOUND`, `M0-C-DECODER-CANONICITY-UNPROVED` | Every body decodes to a datum that re-encodes to the same bytes and equals the transport value; all 25 noncanonical inputs are refused. |
| 3. Lattice, Kahn order, class fold | `M0-A-S3-PCNODE-KEYS`, `M0-A-S3-KAHN-ORDER`, `M0-A-S3-CLASS-FOLD`, `M0-A-S3-LATTICE-REPRODUCES-GOLDENS`; `CannotAnswer` `M0-C-CHALLENGE-DEPENDENCY-ORDER`, `M0-C-TRANSFER-NODE-COORDINATE`, `M0-C-EDGE-CONSTRUCTION-NEXT-INCREMENT` | The exported node keys are the Appendix A `PCNodeBody` encodings; the Lean Kahn order and class fold reproduce all five order and class tables. |
| 4. Theorems | `M0-A-S4-DECODE-ENCODE-PROVED`, `M0-A-S4-INJECTIVITY-PROVED`, `M0-A-S4-PREFIX-FREEDOM-PROVED`, `M0-A-S4-JOIN-LATTICE-LAWS-PROVED`, `M0-A-S4-STANDARD-AXIOMS-ONLY`; `CannotAnswer` `M0-C-S4-ORDER-INDEPENDENCE-NOT-PROVED` | Proved on `propext`, `Classical.choice`, `Quot.sound` at most; the lattice laws use no axiom. |
| 5. Cost ledger | `M0-A-S5-COST-LEDGER-RECORDED` | Recorded in the run metrics and below. |
| Non-claims | `M0-C-NOT-NORMATIVE`, `M0-C-NO-IMPLEMENTATION-CORRESPONDENCE`, `M0-C-NO-SECURITY-OR-APPLICABILITY-CLAIM` | Stated as findings so that a green run cannot be read past them. |

## The theorems

`parse_encode` states that for every datum `d` with `wellFormed d = true` and
an encoding shorter than `2^64` octets, and every remainder `r`,
`parse fuel (encode d ++ r) = some (d, r)` whenever `fuel` exceeds the
root-zero depth of `d`. It is a mutual structural recursion over the nested
inductive datum type together with `parseFramed_encodeSeq` and
`parseFields_encodeFields`. From it:

- `decode_encode`: `decode (encode d) = some d` for every well-formed datum
  within the four limits;
- `encode_injective`: two well-formed data with the same canonical bytes are
  equal;
- `encode_prefix_free`: if `encode d₁ ++ r = encode d₂` then `d₁ = d₂` and
  `r = []`, which is the mechanized form of "a decoder consumes exactly one
  value"; and
- `encodeChecked_injective`: the checked encoder used for the golden
  comparison is injective.

The encoding therefore satisfies both properties the brief allowed for;
prefix-freedom is the stronger one and injectivity is its instance at
`r = []`.

`Join_cons` shows that the membership definition of `Join` in Section 11 is
the right fold of a binary join, and the binary join is associative,
commutative, and idempotent with `Invalid` absorbing and `StaticPublic` as
identity (`PCClass.join_*`). Together they say that `Join` of a list depends
neither on order nor on multiplicity, so the page's set-valued reading and any
list-valued implementation agree.

The converse of `parse_encode`, that every input the strict parser accepts
re-encodes to itself, is not proved (`M0-C-DECODER-CANONICITY-UNPROVED`); the
Python decoder checks it at run time and the Lean parser is strict by
construction, but the statement remains a next increment. Independence of the
class fold from the choice of topological order was not attempted
(`M0-C-S4-ORDER-INDEPENDENCE-NOT-PROVED`).

## Underdeterminations found

- `M0-C-NAT-BYTE-BOUND`. Foundation Section 2.1 says reaching a bound is
  allowed. The K1 encoder refuses a natural whose canonical encoding is
  exactly `2^20` octets (`_magnitude_size` subtracts the ten-octet overhead of
  a signed integer for naturals too), and its decoder refuses the
  corresponding exact-bound input because of the re-encoding check, while a
  symbol, an octet string, and a signed integer with the same total length are
  accepted. The gate measures this in Python on every run. The Lean
  `encodeChecked` follows the page and accepts by definition; it is not
  executed at that size because the minimal-magnitude definition divides
  repeatedly and is quadratic in the magnitude. Which side is right belongs to
  the Foundation owner.
- `M0-C-CHALLENGE-DEPENDENCY-ORDER`. Section 11 says a Challenge that fails
  is "`Invalid` or `VerifierPrivate` by the first failed dependency". The D1
  typed model lets an `Invalid` dependency anywhere win over a
  `VerifierPrivate` one; reading "first" positionally over activity,
  conditions, then joint members gives a different class when an earlier
  dependency is `VerifierPrivate` and a later one `Invalid`. Lean computes both
  readings; they agree on all fifteen Challenge nodes of the five carriers, so
  the goldens cannot discriminate them.
- `M0-C-TRANSFER-NODE-COORDINATE`. The transfer paragraph of Section 11 names
  occurrence kinds, not graph nodes. D1 places `Publish(activity)` on output
  nodes, `Join` of the incoming edges on effect nodes, and three transfers read
  named nodes rather than the incoming edge set: a public Query joins its
  activity and index producer and ignores its publication-effect edge; a
  deterministic Verifier message joins its activity and its inputs, which are
  edges of its effect node rather than of the output node; a LogicalAccess
  publication effect uses `Publish(activity)`. The Lean fold takes these
  placements as exported transfer kinds. Their coordinates are a target
  wording obligation, alongside the two D1 already recorded.
- The brief listed "content references" among the datum constructors. Neither
  the Foundation page nor the K1 model has one: a content reference is a
  framed octet string inside a preimage, and the tenth form is the signed
  integer. The transcription follows the page.

## Cost ledger

| Item | Measure |
|---|---:|
| Lean text, kernel modules (`Datum`, `Encode`, `Decode`, `PCGraph`, `Theorems`) | 655 code lines, 968 lines with comments |
| Lean text, transport and executable (`Transport`, `Main`, `Axioms`, root, lakefile) | 305 code lines, 378 lines with comments |
| Datum type, well-formedness, measures, `beq` | 99 code lines |
| Encoder, limits, arithmetic lemmas | 89 code lines |
| Strict parser and decoder | 118 code lines |
| Lattice, Kahn order, transfer kinds, fold, `PCNodeBody` | 121 code lines |
| Proofs (parser inverts encoder and corollaries, lattice laws) | 228 code lines |
| Python (`export_vectors.py`, `run.py`) | about 1,000 lines |
| `lake build`, cold, 32 hardware threads | 7.3 s wall, 10.4 s CPU |
| `lake build`, warm | 0.4 s |
| `lake exe m0` over 22 bodies (about 478 KiB) and five carriers | 0.7 s |
| Axiom report | 0.5 s |
| Whole gate, warm | 4.4 s |
| Agent wall-clock, reading the owner pages and both predecessor packages and probing the toolchain, to the first Lean line | about 17 minutes |
| Agent wall-clock, first Lean line to the frozen 34-finding gate | about 18 minutes; the mutual theorem checked on its second build |
| Agent wall-clock, manifest, lifecycle, index row, note | about 10 minutes |

What was hard, in order: the pinned toolchain derives no `DecidableEq` for a
nested inductive type and its `induction` tactic refuses one, so equality is
a hand-written test and every proof over the datum is a recursive theorem by
pattern matching in a `mutual` block; `rw` leaves `match some (...)` blocks
unreduced after rewriting a parser call, so the parse proofs use `simp only`;
an `omega` goal stated over the `Octet` abbreviation failed on a literal and
the lemma was restated over `Nat`; two small API differences of Lean 4.33
(`String.drop` yields a slice, `String.mk` is deprecated). Nothing required
an external library.

## Result boundary

This is finite known-answer, negative, round-trip, and differential evidence
about definition text, plus five mechanically checked statements about that
text. It is not:

- normative semantics: the Foundation page and Section 11 own the laws;
- correspondence for the C++ implementation, or for the Python twin beyond
  the exact vectors compared;
- a port of the `PCGraph(core)` edge construction from a Core, which is the
  next increment;
- a proof that the strict decoder accepts only canonical input;
- a statement about theorem applicability, protocol soundness, Fiat--Shamir
  security, or any random-oracle or concrete-hash property; or
- a proposal to adopt Lean as a reference twin or a specification language.
  That decision belongs to the design lane, and this package exists so it can
  be taken with numbers.

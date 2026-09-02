# M0 Mechanized Kernel Definition Feasibility

> **State:** `Affirmative/M0-A-KERNEL-DEFINITIONS-REPRODUCE-GOLDENS` for the
> bounded vector set; 34 findings, nine of them `CannotAnswer`
> **Authority:** None. The experiment edits no target page, publishes no
> profile, and makes no Lean text normative.
> **Executable evidence:**
> [`evaluation/formal-kernel-mechanization-m0`](../../../../evaluation/formal-kernel-mechanization-m0/README.md)

## 1. Question and answer

The program reassessment
([`f0-program-reassessment-and-direction.md`](f0-program-reassessment-and-direction.md),
Sections 2.3 and 5) observed that the lane already mechanizes its kernel by
hand, in Python, twice per package, over one shared constitutional encoder.
The repository's own mechanization boundary
([`checks/README.md`](../../../../checks/README.md)) defers a proof-assistant
decision until duplicated hand-written semantics become a measurable cost, and
asks that the decision be taken on machine-readable artifacts rather than on a
new toolchain dependency. This spike supplies the first number: can the
load-bearing kernel laws be zkc-owned Lean 4 definitions that reproduce the
existing Python goldens byte for byte, and what does one mechanically checked
theorem cost?

The answer is affirmative for the bounded set and cheap. Core-only Lean 4
definitions of the constitutional datum grammar, its canonical encoder, a
strict decoder, and the `PCClass` lattice with its Kahn order and class fold
reproduce every K1 oracle body, all ten D1 Core and `PublicCoinView` bodies,
and all five D1 class and topological-order tables. The parser-inverts-encoder
theorem, with injectivity and prefix-freedom as corollaries, and the lattice
laws of `Join` check without `sorry` on the standard axioms. The whole
package took about forty minutes of one agent session from reading the owner
pages to a frozen 34-finding gate, of which about eighteen were spent between
the first Lean line and the frozen gate, and it is 655 code lines of Lean.

The answer is also bounded in the ways Section 8 lists, and it exposed one
disagreement between the Python model and the prose page and two Section 11
readings the goldens cannot tell apart.

## 2. What was transcribed

The transcription follows the owner pages, not the Python model, wherever the
two could differ, and records where they do.

**Datum.** `docs-next/foundation/executable-foundations.md` Section 2.1 fixes
ten tagged forms. The Lean type has nine constructors: unit, Boolean over
`Bool`, natural, signed integer, bytes, symbol, sequence, record over
`(ordinal, value)` pairs, and variant. One `Bool` constructor for the two
Boolean tags is exactly what the page's total `MetaBooleanDatum` notation and
the K1 model's host `bool` do. Octets are natural numbers below `256`; the
well-formedness predicate requires that bound inside byte strings and symbols,
and requires what the page requires of a symbol (nonempty, `0x21..0x7e`), of
record ordinals (strictly increasing), and of every length, count, ordinal,
and case (fits `u64`).

**Encoder.** `encode` is total over the type, so that it can be reasoned
about without an option monad; `encodeChecked` refuses what `wellFormed`
refuses and the four constitutional limits (`2^20` octets, `2^14` nodes,
`2^14` child edges, root-zero depth `384`), which is what the Python
`encode_datum` refuses with `CanonicalError`.

**Decoder.** `parse` consumes exactly one value and returns the remainder; it
is structurally recursive on a fuel argument that bounds the nesting it will
follow, and `decode` supplies the depth limit plus one as fuel, so fuel
exhaustion and the depth limit coincide. `decode` additionally refuses trailing
octets, input above the byte limit, and a value that crosses the node or edge
limits. The page's malformation list (unknown tag, trailing bytes, invalid
symbol, duplicate or unsorted fields, overlong magnitude, length disagreement)
is exercised by 23 crafted inputs, each confirmed refused by the Python decoder
at export time.

**Lattice and order.** `Join` is written as Section 11 writes it, by
membership; `Publish` likewise. `PCNodeBody` is built from Appendix A. The
Kahn order emits at each step the available node whose canonical body is
lexicographically least. The class fold applies exported per-node transfer
kinds: a constant class, `Join` of the incoming edges, `Publish` of that join,
`Publish` of a named activity, `Join` of a named node list, or the specialised
Challenge transfer. The transfer kinds and the node and edge tables are
exported from the D1 typed model; the construction of `PCGraph(core)` from a
Core is deliberately not ported.

## 3. Evidence design

`export_vectors.py` produces the goldens deterministically from the two
predecessor packages and asserts, at export time, that the K1 reference
encoder agrees with each frozen oracle body and refuses each crafted
negative. `run.py` regenerates the export on every run and compares it with
the committed files, so a drift in either predecessor is reported. The ten D1
bodies are pinned by digest and regenerated at check time because they total
about 430 KiB.

The Lean executable receives the oracle's own JSON value transport
(`evaluation/k1-executable-foundations/oracle/CONTRACT.md` Section 3) and the
golden hex. For every body it checks three things: that `encodeChecked` of
the transport value equals the golden bytes; that `decode` of the golden bytes
yields a datum whose checked encoding is again the golden bytes; and that the
decoded datum equals the transport value. Because `encodeChecked_injective`
is proved, the second check already implies the third for well-formed values;
the third is retained as an executable cross-check of the hand-written
equality test.

For every carrier it checks that each exported node key is the encoding of
the Appendix A body for that node's tag and arguments, that its Kahn order
equals the D1 topological order, and that its class fold equals the D1 class
table. It also computes the positional reading of the Challenge transfer and
reports whether the two readings agree.

`run.py` then elaborates `Axioms.lean` and requires every statement to rest on
`propext`, `Classical.choice`, and `Quot.sound` at most. It also refuses
statically any `sorry`, any `axiom`, any `require` in the lakefile, and any
import outside the toolchain's own libraries; the kernel modules import only
each other and only `Transport.lean` imports `Lean.Data.Json`.

## 4. Results

| Stage | Subject | Result |
|---|---|---|
| 1 | 12 oracle bodies, five Core bodies, five `PublicCoinView` bodies | all 22 encode to the golden bytes |
| 2 | the same 22 bodies; two oracle and 23 crafted noncanonical inputs | all round-trip; all 25 refused |
| 3 | five carriers, 91 nodes each, 151 or 146 edges | keys are Appendix A bodies; order and class tables reproduce; both Challenge readings agree on all 15 Challenge nodes |
| 4 | `parse_encode`, `decode_encode`, `encode_injective`, `encode_prefix_free`, `encodeChecked_injective` | proved; axioms `propext`, `Classical.choice`, `Quot.sound` |
| 4 | `Join_cons`, `Join_eq_foldr`, associativity, commutativity, idempotence, `Invalid` absorbing, `StaticPublic` identity, `Publish_idem` | proved; `Join_cons` uses `propext`, the rest no axiom |
| 4 | class fold independent of the topological order | not attempted |

The five class distributions computed in Lean are the D1 distributions: 55,
28, 5, 3 for the baseline; 53, 28, 7, 3 for the private Verifier-output sink;
55, 28, 5, 3 for the invalid module control; 54, 12, 5, 20 for the history
Challenge condition; 54, 29, 5, 3 for the logical Reject preemption, in the
order `StaticPublic`, `PublicHistory`, `VerifierPrivate`, `Invalid`.

## 5. The theorem and what it cost

`parse_encode` says: for every datum `d` with `wellFormed d = true` and an
encoding shorter than `2^64` octets, every remainder `r`, and every fuel above
the root-zero depth of `d`, `parse fuel (encode d ++ r) = some (d, r)`. Its
proof is a mutual structural recursion over the nested inductive type with two
list companions, one per aggregate form, and it rests on four small facts:
that eight big-endian octets read back as the number modulo `2^64`, that the
minimal magnitude reads back exactly and passes the minimality test, that a
frame reads back its body and remainder, and that the length, depth, and
well-formedness of an aggregate bound those of its children.

Prefix-freedom is the property the encoding actually has, and it is the
mechanized form of the page's sentence "a decoder consumes exactly one value";
injectivity is its instance at an empty remainder. Both are one-line
corollaries once `parse_encode` exists, which is why the round trip was proved
rather than injectivity directly.

The proof is 228 code lines including the lattice laws. It checked on its
second build: the first attempt used `rw` where the rewritten parser call
left a `match` on `some` unreduced, and `simp only` was the fix. Two features
of the pinned toolchain shaped the text: `deriving DecidableEq` does not apply
to a nested inductive type, so equality is a hand-written Boolean test, and
the `induction` tactic refuses a nested inductive type, so every proof over
the datum is a recursive theorem by pattern matching. Neither required an
external library. The cold build is 7.3 seconds of wall clock; the warm gate
is 4.4 seconds end to end.

## 6. Underdeterminations found

Each is a finding with a stable code in the frozen record.

1. **`M0-C-NAT-BYTE-BOUND`, Python against prose.** Section 2.1 says
   reaching a bound is allowed. The K1 encoder refuses a natural whose
   canonical encoding is exactly `2^20` octets, because `_magnitude_size`
   subtracts the ten-octet overhead of a signed integer for naturals as well,
   and its decoder refuses the exact-bound input through the re-encoding
   check; a symbol, an octet string, and a signed integer of the same total
   length are accepted. The gate measures this in Python on every run. The
   Lean `encodeChecked` follows the page by definition and is not executed at
   that size, because the minimal-magnitude definition divides repeatedly and
   is quadratic in the magnitude; a definition that is adequate for proof is
   not automatically an adequate algorithm. Resolution belongs to the
   Foundation owner: one octet of the byte bound, one way or the other.
2. **`M0-C-CHALLENGE-DEPENDENCY-ORDER`, prose.** "By the first failed
   dependency" admits a lattice-priority reading, which D1 implements
   (`Invalid` anywhere beats `VerifierPrivate` anywhere), and a positional
   reading over activity, conditions, then joint members. They differ when an
   earlier dependency is `VerifierPrivate` and a later one `Invalid`. The five
   carriers contain no such Challenge, so the goldens do not decide it.
3. **`M0-C-TRANSFER-NODE-COORDINATE`, prose.** The transfer paragraph names
   occurrence kinds, not the effect or output node that carries the transfer,
   and three of D1's transfers read named nodes rather than the incoming edge
   set: a public Query joins activity and index producer and ignores its
   publication-effect edge, as the page's `Join(activity,index)` says; a
   deterministic Verifier message joins its activity and inputs, which are
   edges of the effect node and not of the output node; a LogicalAccess
   publication effect takes `Publish(activity)`, the reading D1 already
   recorded. A transcription must be told these coordinates; they are a
   wording obligation of the same kind as the two D1 recorded.
4. **`M0-C-DECODER-CANONICITY-UNPROVED`, gap rather than ambiguity.** The
   converse of `parse_encode`, that every accepted input re-encodes to itself,
   is what the Python decoder checks at run time. The Lean parser is strict by
   construction and refuses all 25 negatives, but the statement is not proved.
5. **The brief.** It listed "content references" among the datum constructors
   and omitted the signed integer. Neither the Foundation page nor the K1
   model has a content-reference datum; a content reference is a framed octet
   string inside a preimage. The transcription follows the page, and the
   package records the correction so the next brief does not repeat it.

## 7. What this changes for the program, and what it does not

The reassessment's Section 2.3 noted that the only pair in the lane with
separately implemented canonical encoders is F1-R0's Python and Rust checkers,
and that D1's typed and cold paths share the K1 encoder. There is now a third
separately written encoder, and it agrees byte for byte with K1 on 22 bodies
including all five `PublicCoinView` bodies. That narrows the shared-encoder
caveat for those bytes; it does not change the D1 cold path, which still
imports K1, and it says nothing about bytes the vectors do not contain.

The cost number is the other result. One session produced definitions that
reproduce the goldens and a checked statement about them; the definitions are
smaller than either Python path and carry a theorem the Python paths cannot.
That is an input to the mechanization decision the checks README defers, not
the decision. This note proposes no adoption, no third leg of the reference
twin, and no change to the F2-O0 recommendation.

## 8. Next increment

- Port `PCGraph(core)` edge construction from an admitted Core and compare
  the derived edge tables with D1's, so that the exported transfer kinds and
  edges stop being inputs.
- Prove decoder canonicity, `decode b = some d → encodeChecked d = some b`,
  which turns the Python run-time re-encoding check into a theorem.
- Prove that the class fold is independent of the choice of topological
  order, which is what makes the Kahn tie-break a determinism convenience
  rather than a semantic input.
- Replace the quadratic minimal-magnitude definition by one that is both
  provable and linear, then execute the `2^20` boundary in Lean as well.

## 9. Nonclaims

The 34-finding aggregate is finite executable evidence about definition text,
together with five mechanically checked statements about that text. It does
not make any Lean text normative, establish correspondence for the C++
implementation or for the Python twin beyond the compared vectors, port the
edge construction, prove decoder canonicity, or establish any theorem
applicability, protocol soundness, Fiat--Shamir security, random-oracle, or
concrete-hash property. Without the pinned toolchain the gate reports
`Unsupported` for every Lean-dependent finding and fails closed.

# Structured native import

## Purpose and subjects

The shared `Source.Region` carrier needs a checked connection to actual native
structured programs. Its generic formation laws do not establish that a native
helper, capture map, domain, or result list was imported faithfully. The scalar
`zkc.common-source/0` bridge also cannot express these subjects: it expands pure
helpers and has neither declaration identity nor structured callbacks.

Import the original protocol-profile module after native formation and before
preparation. Keep its declarations and contracts. Preparation can select finite
algorithms without scalar simplification, expands Local helpers, and eventually
realizes total mathematics. A snapshot taken there is a different subject; it
cannot establish the source side of a transformation it has already applied.
Native MLIR remains the production representation.

The structured format is a sibling of the scalar format. Native parsing and
verification precede export. Lean independently checks the supported vocabulary,
binding interfaces, declaration references and static profile restrictions before
constructing canonical regions. It supplies the operation meanings; input files
cannot supply a semantic oracle.

## Protocol verification targets

### Schnorr

The first endpoint is the actual library Interactive Schnorr original-stage
unit, together with the maintained Helpers and Reordered forms. Its open process
receives a commitment, queries the actual challenge
service, sends the challenge, receives an independent response, and returns the
Schnorr equation's Boolean result. This equation must hold for arbitrary replies
and stopping prefixes, with the public inputs and service binding explicit.

`ZkcExamples.Structured.SchnorrInteractive` kernel-admits the actual unit and
proves both participants' process equations. Its explicit effect adapter supplies
`Protocols.Schnorr.Common.VerifierContract`; the existing consumers give perfect
completeness and special soundness, and the optional VCVio consumer uses the same
contract. The dormant named DLog formula has its own full-table equation; its
association with the retained relation is not inferred. Native group arithmetic,
probabilistic knowledge extraction, and Fiat–Shamir require further arguments.
Interactive tests participant binding and metadata. Its formula is dormant; the
Helpers form exercises named calls, while split-scope `first` controls distinguish
faithful component calls from an all-input approximation. `SchnorrVariants`
proves the shared contract for Helpers and Reordered. Its admitted EarlyChallenge
unit queries before receiving the commitment; an exact first-action observation
refutes the shared contract for this counterexample.

### Sumcheck

The next library target is the actual multilinear protocol in
`libraries/sumcheck/lib.zkc`. Each round sends a pair `(a0, a1)`, checks the
current claim against `a0 + a1`, obtains a fresh challenge `r`, and updates the
claim to `(1-r) * a0 + r * a1`. Its runtime round count and repeated interactions
require an open structured repeat model.

`Reduce` returns an evaluation obligation. A separate public-table or opening
consumer must discharge that obligation before it yields an acceptance claim.
The full public-table protocol additionally needs vector operations and the
imported `has_shape` and `fix_prefix` helpers. Source records already flatten into
ports; each pair message becomes two ordered scalar exchanges, so no tuple-valued
action or new carrier is required. Count agreement
and valid native dimensions are explicit premises.

The maintained two-round quadratic scalar verifier and its `4 / |F|` theorem
remain useful regression clients. They are a different protocol from the
multilinear pair-message library. Connecting the library to ArkLib requires a
new library polynomial adapter and an arbitrary-round causal experiment equation;
the generic degree-bound theorem alone does not establish that correspondence.

## Structural and semantic requirements

The maintained whole-unit profile has per-root participants/scopes, immutable
Booleans, unsigned indices, nominal BLS12-381 scalar/vector/group values, and
root-owned random-service handles. Closed Math/Local helpers remain separate from
open roots. Math uses optional named closures; Local calls sequence all arguments
and run only at their owner. Finite/control work remains available in closed
Local bodies. Multi-role roots refuse transitive Math folds and checked reads;
affine resources and general interactive repetition remain future work.

Both dialects instantiate the existing Source.Region. One evaluator uses explicit
F/G and lawful module operations; SiteObservations abstracts only internal source
marks. Generic operation/Region/table naturality gives site erasure and closed
lifting. The checked closed view has a semantic correspondence at the same value
assignment, with complete one-role port scopes certified by the closed view.

- Preserve ordered result tuples, including no results. A zero-result operation
  can still stop or interact.
- Preserve closed helper definitions and references. Capture order, helper
  identity, call ownership and the state/item/argument/capture partition are
  checked interfaces.
- Keep every domain constructor in admission order, including unused ones.
  Empty iteration cannot bypass failed admission.
- Check dormant branches and callbacks. Dynamic nonexecution is not permission
  to admit malformed or unsupported syntax.
- Keep Algebra and Local admission distinct. Algebra callbacks require the
  appropriate totality and bound provenance; Local callbacks can stop. Initial
  supported types can exclude affine resources rather than invent ownership
  laws for them.
- Interpret indexed reads as checked reads. A static bound discharges a failure
  case; it does not redefine an invalid read to return an arbitrary value.
- Retain source identity, relation annotations, roles, sites, helper origins and
  preconditions separately from dynamic process equality. Equal processes can
  have different static contracts.

The first import gates are the actual `finite/total-state.mlir` and
`finite/unit-state.mlir` fixtures. They exercise a two-result accumulator and a
zero-result stopping fold, respectively. Result swaps and changed helper bodies
can be well-formed programs with different meanings; the checker must not
misclassify every semantic difference as malformed input.

## Initial checkpoint and next obligations

The maintained clients now prove complete process equations for both actual
exported fixtures, universally over vectors and scalar/Boolean inputs. The
total-state client returns the ordered pair fold. The unit-state client aborts
exactly when enabled and nonempty. Both retain the `2^64` vector-length admission
condition and prove refusal outside it. Transparent constructor data is checked
against fresh native exports; the proof clients compute admission of that data
and use the common region and finite semantics, rather than assuming a source
correspondence equation.

This establishes a usable import and proof interface for structured immutable
programs. It also exposes the next proof obligations: semantic soundness of exact return-identity and bound propagation, and general
read safety under an explicit valid-input relation. Those results are needed
before using Math totality to justify eliminating or moving calls. They should
precede a generic native realization theorem; finite Runner comparisons remain
regression evidence for that later boundary.

The checked operation tree is the authority for helper references and instruction
counts. Deriving that inventory after formation avoids a second mutable list
that can drift when a new operation or region is added. The inventory includes
the full helper signature and is proved equal to the typed body's erasure.
The independent linking check now supplies unique declaration names and exact
signature membership in each strict prefix. Lookup laws expose the corresponding
body; table-frame laws isolate the helper meanings each region actually uses.

The [scalar inlining clients](../../bridges/structured/README.md#scalar-inlining-pairs)
now exercise this interface on two actual authored Entries. Schnorr response
computes `nonce + challenge * secret`. The multilinear claim client computes
`(1 - r) * a0 + r * a1` in any commutative ring, through the authored expression
`weighted(a0, 1 - r) + weighted(a1, r)`. The two calls share a nested helper;
the decimal literal and both exact bodies have kernel-checked admission witnesses.

Each proof concerns the retained native original and the actual output of
`zkc-opt --zkc-prepare-protocol="simplify=false optimize-finite=false"`.
The reusable inlining law preserves the complete helper process and suffix;
it does not use a Math-totality assumption. The source/candidate equation is
specific to each pair, with checked named body contracts. Regeneration compares
native bytes, exports and transparent constructor data. No universal optimizer,
exporter or frontend correspondence follows from these checks.

The linker independently validates exact links in the proposed order. It does
not prove that sorting preserved every input declaration or body; preservation
and candidate-generation completeness remain separate properties. Proving the
whole Kahn implementation would couple each lookup client to incidental sorting
and lowering details. A small decidable predicate instead checks exact helper
signatures in the preceding declarations and supplies its proof to `Payload`.
The cost is another bounded traversal of at most 128 declarations and the formed
helper inventory. Name lookup remains simple; typed declaration indices would
be worth revisiting if later substitution or linking proofs demonstrate a
concrete benefit. This check does not prove the exporter or identity analysis.

Keep identity analysis separate from typed formation. Its proof needs an explicit
environment invariant: positions with the same known origin denote the same
value, and each retained index/container fact holds for those values. Calls
transfer that invariant through return summaries; folds discharge bounds using
domain items and invariant arguments/captures. A totality theorem must quantify
over valid inputs satisfying the function's declared preconditions. Merely
moving this analysis after formation would not prove these semantic properties.

The next whole-protocol extension adds the actual multilinear Sumcheck library
and interactive repetition. Availability admission already substitutes both
per-result dependencies and each intermediate requirement over the checked helper
order, with incremental budgets. A general availability-soundness/presence theorem
and a native demand-projection relation remain separate obligations. These extensions reuse this declaration and
region boundary. They must establish the verifier contracts above before
transporting the existing security proofs to their imported subjects.

## Evidence boundaries

Formation proves typed interfaces. Static admission checks the selected profile's
additional contracts. A source-to-reference equation concerns the elaborated
Lean process. Native export tests check that the writer emits the intended
subject. These obligations have different owners and cannot replace each other.

The byte digest identifies a subject; it does not establish its meaning. The
export writer and native formation remain reviewed executable components. The
imported denotation does not prove frontend translation, participant projection,
finite realization, native backend arithmetic, runtime cleanup or capacity
behavior. Unbounded semantic equations require a separate realization relation
before they can justify claims about a bounded native execution.

MLIR's [language reference](https://mlir.llvm.org/docs/LangRef/) explains region
dominance and `IsolatedFromAbove`; zkc's native regions already require explicit
captures. Its [dialect conversion framework](https://mlir.llvm.org/docs/DialectConversion/)
checks configured legality. Neither mechanism supplies a denotational correctness
theorem by itself.

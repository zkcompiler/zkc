# Structured native import

The [native export contract](../../../docs/spec/formats/structured-source.md)
owns `zkc.structured-source/0`. This page owns independent Lean admission and
logical meaning. Source/native correspondence is a separate boundary.

## Checked subject

`Structured.Snapshot` retains source identity, selected entry, all domains,
relations and definitions, exact function kinds, per-protocol rosters and port
scopes, visibility, origins, preconditions, sites and ordered operands/results.
There is one current strict wire schema. The reader rejects unknown tags, extra
fields, objects and noncanonical numeric tokens, including in unused bodies.
Canonical decimals use the shared bounded ASCII-digit fold, which reduces in
the Lean kernel. Parsing JSON and matching an export digest to MLIR remain
executable boundaries.

Relations are noncallable metadata. Their input types, Boolean result, purposes,
kind, key and revision are retained. A statement checks exact entry operands,
role selectors and the Boolean acceptance-result index. It does not evaluate a
relation or identify different participants' acceptance values. The association
between a relation and a formula is absent from this MLIR and is not inferred
from symbol spelling. Logical-origin binding values also remain opaque metadata;
Lean checks their shape, size, nonemptiness and key uniqueness.

`check` resolves kinds, signatures, exact bound provenance, capture forwarding,
rosters and scopes, then forms existing `Source.Region` bodies through
`RawRegion.elaborate`. There is no additional source IR. One checked body is
stored per named helper; calls retain names and never expand syntax.

`UnitPayload` separates kinded Math/Local `CheckedDefinition`s from
`CheckedProtocol` roots. Helpers use `dialect`; roots use `protocolDialect` on
the same carrier. Root operations resolve role strings to indices in that
root's roster. Protocol roots cannot occur in a `Helper` signature or helper
table. The calculation boundary admits only Math references and region-free
calculations; Local invocation carries a checked Local signature and owner.

The existing declaration order is a candidate, independently checked by
`DeclarationsLinked`. Exact signatures include Math/Local kind, ordered inputs
and ordered outputs, including both finite callbacks. Dormant callbacks and
stopped suffixes remain dependencies. Roots separately check their references
against the complete helper table. Identity summaries order their Math call
subgraph for bound discharge; availability reuses the final checked order and
introduces no additional sorter.

`Imported snapshot` carries successful admission of that exact constructor
subject. `Imported.exactSubject` and `check_ok_inversion` retain subject identity
and successful checking. Typed erasure/formation laws recover exact stored
bodies. These facts do not prove a universal MLIR lowering or exporter theorem,
or correctness of the candidate ordering algorithm as an inventory transform.

## Bounds and availability

Bound facts identify exact index/container positions. Result binding shifts
both positions. `IdentitySummaries` follows returned-input aliases and select
arms with the same known identity; two unknown origins never prove equality.
Math preconditions must be discharged at each call. An indices domain supplies
the bound for its selected vector in the `S / I / A / C` interface. Mutable state
is not assumed invariant across iterations; equal lengths do not identify
vector contents. Local regions begin without Math bound premises.

`Availability` is a separate formed-tree analysis. Math summaries retain one
dependency footprint per result and individual requirements for every
intermediate computation. Named calls substitute both collections through their
actual arguments. A forwarded output can ignore an absent unused input;
constants have empty dependencies. An unused mixed-owner calculation still
fails admission. `select(c,x,x)` still requires `c`. Independent requirements
are checked individually, so calculations at distinct participants need not
share a single owner. Zero-result calls do not discard requirements.

The first multi-role profile refuses Math folds and checked reads, including
transitively through named calls. Singleton roots keep the existing finite
profile; owned Local finite/control work remains available in multi-role roots.
This restriction bounds the partial Math fragment; it is not a proof that eager
component interpretation equals native demand-driven projection.

Each root checks every requirement, owned operand, nonempty restriction subset
and declared output scope. Service values originate only at singly owned root
input ports. Their exact contract is checked at draw, and they cannot be
selected, restricted, exchanged, returned, passed to helpers or used in
statements. Handle-alias restrictions belong to the executable request boundary;
service independence or uniform sampling does not follow from handle identity.

`UnitPayload.available` records `checkUnitAvailability ... = .ok ()`. This is
computational admission evidence, **not a general availability-soundness or
presence theorem**. In particular, denotation alone never licenses admission.
The rejected unused-intermediate controls are model counterexamples, not newly
admitted native programs.

## Shared mathematical and component meaning

`assignment F G` maps Boolean/index/field/vector/group/service sorts to
`Bool`, `Nat`, `F`, `List F`, `G`, and `Nat`. Admission permits exactly the
BLS12-381 scalar and G1 nominal tags and the corresponding random-service
contract. The evaluator uses explicit `CommRing F`, `AddCommGroup G`,
`Module F G` and decidable equality laws. Group scaling is scalar action with
group operand first in the source. No arbitrary group is silently equated to
its scalar field.

`Evaluation` implements scalar, group, Boolean and finite/control operations
once. The generic `HelperTable Value interface` checks exact signatures;
closures capture their already interpreted prefix. `ComponentTables` builds
closed and optional closures from the same body. Math calls pass optional tuples
directly to their named optional closure. Other operations delegate to the
existing evaluator after operand sequencing. Nested callbacks retain their
nonoptional meaning through `Region.component`.

All-present adequacy preserves the complete process, including stops, nested
callbacks and zero/multiple results. Generic frame laws require both closed and
component agreement because callbacks use closed meanings. Prefix linking and
full-table equations exclude missing/mismatched lookup fallback for checked
references; they do not exclude legitimate reads or stops in a callee.

Folds use `Finite.execute`: domain admission precedes iteration, predicate
precedes step, false preserves state, and stopping bypasses the suffix. Checked
reads refuse invalid indices. Counted loops retain state/capture packing and
conditional completion. The logical semantics has no depth fuel. Existing
finite theorem families use the same explicit `F,G` assignment and evaluator.
`SiteObservations` abstracts only internal marks; arithmetic is pure and shared.
There is no separate scalar arithmetic or unsupported-sort fallback.
The independent model retains its existing vector/index select controls, which
are not currently native mathematical export paths.

## Helper inlining and selected transformations

`Evaluation.inline_invoke` replaces a helper invocation by
`Region.bind (body.rename arguments.get) next` under an explicit equation
between lookup and body denotation for every actual argument tuple. It applies
to the shared scalar/group evaluator, any effect interface and site observations.
Binding retains ordered helper results above the caller environment. Equality
concerns the complete `PIR.Proc`: a stopping body bypasses the suffix, and a
returning body runs that same suffix, including its stops. Empty result lists
are supported. The premise is a process equation, not a totality assumption.
The closed `Structured.inline_invoke` wrapper and `Payload.inline_body_view`
reuse this law, exact declaration membership, linking and table-frame laws.

`SchnorrResponse.original_eq_candidate` and
`SumcheckClaim.original_eq_candidate` prove equality of exact exported original
and prepared candidate models for two authored scalar Entries. Checked body
contracts connect the imported subjects to their arithmetic over an arbitrary
commutative ring; an admitted subtraction mutation has a concrete counterexample.
These are selected model equations with retained source evidence, not correctness
of a native optimizer for every input. The scalar clients do not by themselves
establish an interactive protocol theorem.

## Actual Interactive Schnorr subject

`ZkcExamples.Structured.SchnorrInteractive` kernel-admits the retained whole-unit
constructor data. Its arbitrary `F,G` equations expose each participant's actual
requests and independent reply continuations. The verifier equation is the
existing Common Schnorr experiment through an explicit effect embedding; a proved
left inverse gives its `VerifierContract`, completeness and special soundness.
The optional `StructuredSchnorr` security consumer applies the existing VCVio
honest-view theorem to that contract. No honest-delivery premise supplies the
source equality.

`SchnorrVariants` kernel-admits the retained Helpers, Reordered and EarlyChallenge
units. Full-table equations expose the Helpers form's named response and
verification closures. Helpers and Reordered satisfy the same verifier contract;
the reordered equation uses group commutativity. EarlyChallenge instead queries
before receiving the commitment. Its exact process equation proves that it
cannot satisfy that contract, independently of any scripted test replies.

The separate dormant formula remains a named Math closure, with closed and
all-present component equations for arbitrary values. The exact relation record
is retained without inferring an association to that formula. These equations do
not certify native BLS arithmetic, provider randomness, runtime execution, the
exporter, authored relation binding, or Fiat–Shamir security.

## Participant meaning and observations

`Program.participant` interprets the selected root for a chosen roster index.
Input scopes mask supplied values before evaluation; output scopes filter
returned values after all work. Shared scopes do not equate participant copies.
`Participant.exchange` sends and retains the sender's value, receives an
independent typed reply at the receiver, and produces absence elsewhere.
`Participant.query` uses the actual service handle operand. `Participant.guard`
checks its optional condition only at its owner.

`Participant.owned` sequences every input at the owner, invokes the **closed**
Local closure and preserves stopping even for zero results. Missing owned inputs
stop `incomplete`. Nonowners skip the call. Optional Local helper closures are
not used for protocol dispatch.

`Op.mark` and `ProtocolOp.mark` retain internal site observations before protocol/Local
instructions and explicit Local stops. Math bodies do not insert marks; their
source operations have no nonempty stop sites in the admitted profile. `Program.observed` exposes these to the
scripted observer. `forgetSites` erases only those observations to obtain the
ordinary participant process; `PIR.Stop` itself does not carry a site. Provider
requests, replies and stops remain ordered. Internal marks consume no scripted
reply and are absent from the external request/reply trace.

`ClosedProgram` is an explicit checked closed projection of an admitted root.
It carries `subject.closedPayload = .ok payload`, retains the same subject, and
keeps its projected root separate from helper closures. Arbitrary `Program`s
have no closed `denote`. Existing finite clients use `checkClosed` and the
closed profile's process laws, with the same `F,G` interpretation.
`ClosedProgram.participant_eq_denote` proves the relation after site erasure,
with exact port transports and complete singleton scopes certified by the
closed-profile check itself.
`Program.participant_direct` derives the plain interpreter from the observed
one through generic operation, Region and table-fold interpretation laws.

`CommonAdapter` embeds the existing Common effect fragment and proves that
projection after embedding preserves the entire process. Projection of extra
index/vector messages refuses explicitly. Concrete contract use must establish
that its actual process lies in the supported fragment; the adapter supplies no
relation binding or security assumption.

## Executable bounds and comparison

```text
structured-source check SNAPSHOT.json
structured-source run SNAPSHOT.json INPUTS.json
structured-source open SNAPSHOT.json REQUEST.json
```

Closed runs retain the existing typed input/output arrays. Open requests and
results follow the native schema: optional ordered inputs, selected role,
scripted replies, full request/reply/stop records, stop site and consumed reply
index. Missing replies stop `incomplete`; mismatches stop `refused` without
consuming the mismatching reply; valid scripted stops consume their reply.
Unused script suffixes remain unconsumed.
An oversized received vector is an observer capacity error; a malformed reply
shape or element type remains an unconsumed semantic refusal.

The CLI chooses `F = G = ZMod scalarModulus`, an explicit additive test group.
This is not native BLS G1 semantics. Typed arbitrary-group equations protect
distinctions that commutative scalar test arithmetic cannot detect.

Source bytes are capped at 16 MiB, request bytes at 1 MiB; strings at 512 UTF-8
bytes; domains, relations and definitions at 128 each; signatures at 512;
source instructions/references at 4096; nesting/helper depth at 64. Stored
internal marks add no source instructions. Availability allows 100000 stored
traversal nodes, with separate 1000000 dependency and participant-replay budgets
across the whole unit. SSA footprints use indexed persistent arrays; helper
argument tuples retain their bounded list lookup costs. Summary substitution,
requirement expansion and footprint unions are charged incrementally before
construction. Reusing a checked Local summary does not charge hypothetical
dynamic call expansion. These are representation-aware admission policies,
not exact allocation or runtime complexity bounds; persistent array copies and
native bit-vector analysis need not have identical costs. Source-size bounds
alone do not bound transitive requirement expansion.

Executable work bounds are separate from fuel-free denotation. The Lean observer
and native SSA evaluator count different work, so their exact exhaustion
thresholds are not equated. Comparisons of outcomes, traces, sites and consumed
replies use sufficient capacities; capacity refusals are tested separately.

Native parsing/formation, C++ export, JSON parsing and constructor rendering
remain reviewed executable boundaries. Exact logical equations and bounded
differential comparisons establish different claims. Neither proves native
transformations, production BLS/RNG behavior, runtime execution, authored
relation/formula association, or Fiat–Shamir security.

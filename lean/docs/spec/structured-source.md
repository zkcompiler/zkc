# Structured native import

The [native export contract](../../../docs/spec/formats/structured-source.md)
owns `zkc.structured-source/0`. This page owns independent Lean admission and
logical meaning. Source/native correspondence is a separate boundary.

## Checked subject

`Structured.Snapshot` retains source identity, selected entry, all domains,
relations, bindings and definitions, exact function kinds, per-protocol rosters and port
scopes, visibility, origins, preconditions, sites and ordered operands/results.
There is one current strict wire schema. The reader rejects unknown tags, extra
fields, objects and noncanonical numeric tokens, including in unused bodies.
Canonical decimals use the shared bounded ASCII-digit fold, which reduces in
the Lean kernel. Parsing JSON and matching an export digest to MLIR remain
executable boundaries.

Bindings are separate noncallable metadata in the exact eight-slot envelope
`[format, original, digest, entry, domains, relations, bindings, definitions]`.
Each row is `["binding", name, contract, arguments, implementation]`. All rows,
including unused rows, are checked. Names match ASCII
`[A-Za-z_][A-Za-z0-9_.-]*`, occupy at most 256 bytes and share the domain,
relation and definition namespace. At most 128 binding rows are retained in
encounter order. The implementation string must be empty. There is no missing
field default or compatibility reader. Binding names cannot be called or
selected as roots, domains or callbacks.

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

## Checked primitives and index values

`Primitive` owns a closed vocabulary and ordered ports; `PrimitiveEvaluation`
owns its meaning over the existing `PIR.Outcome`. One `Op.exec` case delegates
through the shared `Evaluation` used by closed bodies, components and participant
helpers. There is no new carrier, process executor or whole-protocol intrinsic.
Its helper inventory is empty; general framing, effect interpretation, linking,
all-present adequacy, inlining and closed projection retain their claims.

An exec descriptor is `["exec", exact-native-operation, binding-name, parameters]`.
Admission independently resolves the exact operation/contract pair below,
nominal arguments, full ordered ports and parameters. Exec is Local-only,
region-free and requires a nonempty unique source site. Index constant takes
one canonical u64 decimal string; every other primitive takes no parameters.
No leading zero except `"0"`, sign, whitespace, non-ASCII digit, field reduction
or wrapping is accepted. Values through `18446744073709551615` are admitted.

Here `I` is index, `B` Boolean, `F` the exact nominal `bls12-381.fr` scalar,
and `V` its ordered vector. Every native operation has literal prefix
`algebra.exec.`; the suffixes in the table are exhaustive. Index contracts have
no domain arguments; vector and field contracts have exactly `["bls12-381.fr"]`.

| Native suffix | Binding contract | Inputs | Outputs |
|---|---|---|---|
| `index_constant` | `index.constant` | none | I |
| `index_equal` | `index.equal` | I, I | B |
| `index_less` | `index.less` | I, I | B |
| `index_add` | `index.add` | I, I | I |
| `index_mul` | `index.mul` | I, I | I |
| `index_sub` | `index.sub` | I, I | I |
| `index_div` | `index.div` | I, I | I |
| `index_mod` | `index.mod` | I, I | I |
| `vector_empty` | `vector.empty` | none | V |
| `vector_length` | `vector.length` | V | I |
| `vector_sum` | `vector.sum` | V | F |
| `vector_split` | `vector.split` | V | V, V |
| `vector_append` | `vector.append` | V, F | V |
| `vector_equal` | `vector.equal` | V, V | B |
| `field_equal` | `field.equal` | F, F | B |

Index values are `Nat` with explicit `value < 2^64` conditions. Exec checks
both index operands, including comparisons. Add/multiply overflow, subtraction
underflow, and division/remainder by zero stop `refused`. No result is reduced
modulo the scalar characteristic. Pure `index.constant` and `index.equal`
represent native `data.index` and `data.index_equal`, require Math/Protocol
ownership and empty sites, and preserve optional component dependencies. Their
constants are range-checked on admission. They cannot authorize Local exec.
At the logical carrier level pure equality is total on `Nat`; relating arbitrary
inputs to native u64 values additionally requires their representation bounds.
Exec equality checks those bounds itself and can refuse.

Vectors denote logical lists. Empty returns `[]`; sum folds field addition from
zero; append returns the entire original list followed by one scalar; equality
returns false for unequal lengths. Split requires positive even length and
returns the contiguous low half followed by the high half, with neither padding
nor truncation. It does not require a power-of-two length. All result positions
and source marks remain ordered. The component exec case sequences every
operand and stops `incomplete` on absence; reached exec cannot be skipped because
its results are unused. An exec stop bypasses every later continuation.

`vector.length` stops `exhausted` if logical length is not representable in u64.
The same explicit representation check in `DomainSpec.denote` now also stops
`exhausted`; its successful finite laws retain their range premises. This is a
logical representation boundary. List sum/append/split equations do not assert
host allocation success or equate native runtime and observer work capacities.
Callers needing subsequent lengths or index arithmetic must state those bounds.
The exact Fr/G1 nominal profile remains fixed; a configurable profile is deferred
until a real second-domain consumer requires it. Multi-role partial Math remains
restricted as above. Protocol application and protocol repetition remain
unsupported, including in dormant source closure.

## Retained realization and map declarations

The eight-slot envelope retains two additional definition variants, in original
encounter order:

```text
["realize", name, inputs, outputs, helper]
["map", name, inputs, outputs, helper, rowwise]
```

`RealizationDeclaration` and `MapDeclaration` retain exactly these fields.
Preparation names obey ASCII `[A-Za-z_][A-Za-z0-9_.-]*` with a 128-byte limit;
Math helper references use the existing nonempty 512-byte string bound.
`rowwise` contains JSON Booleans, has the input arity and contains at least one
true. A number or string is not a wire Boolean. Both variants count toward the
shared 128-definition limit and each charges one derived operation against the
4096-instruction limit. Unused declarations, metadata, operations and transitive
calls remain subject to admission, closure depth and cycle checks.

Reference permission depends on the original retained variant, before deriving
a semantic Local helper. A Math `call` targets a private defined Math function.
Local `apply` may target an ordinary Local function, finite declaration,
realization or map. Protocol `local.call` targets an ordinary Local function
only. Finite callbacks remain private ordinary functions of the required kind;
derived preparation helpers do not gain callback permission. A preparation's
helper must be an exact private Math reference. Selected entries remain
protocol functions.

Realization requires the declaration's complete input and output ABIs to match
those of its helper, including vector projections and zero or multiple results.
Its transitive Math fragment is
region-free: admitted Fr arithmetic/equality, G1 operations/equality, pure index
constant/equality, Boolean operations, supported selection, Math calls and
positional returns. No finite operation, bounded read, exec, Local control or
helper precondition is admitted in that closure. A semantic totality theorem
must prove immediate return for the actual checked closure; neither this
operation list nor a native effect annotation is itself such a proof.

Formation validates the shared typed operations. The checked raw preparation
profile and selected helper closure are the single operation/type authority;
ordinary declaration ordering and protocol availability enforce cycles and depth.
Declaration ordering precedes preparation-profile selection, so an ordering-depth
failure takes precedence when a unit also has a preparation-profile violation.
A separate traversal of retained Math declarations checks only that the entire
closure has no preconditions, since those original premises are not stored in
`CheckedDefinition`. It supplies no competing operation profile or depth rule.
Successful whole-unit admission entails `PreparationRootsSelected`; the
`Imported` inversion lemmas recover the exact selected root signature of every
retained realization/map. Totality consumers can use that evidence together
with actual checked-definition membership and its exact raw derivation, without
supplying a semantic callee-totality assumption or recomputing root membership.


Map's root helper has only Fr scalar inputs and exactly one Fr scalar output.
An input becomes an Fr vector exactly when its mask entry is true, and the map
has one Fr vector result. Every transitive operation, including dead instructions
and zero-result calls, must be an Fr constant, add, subtract, multiply, exact
Math call or return. Nested Math helpers may return zero or multiple Fr scalars;
the one-result condition applies only to the map root. Equality, selection,
index/group operations and other fields are excluded even when unused.

Both preparations use the existing typed `Source.Region`, `PIR.Proc` and Math
helper table. A realization derives one `Op.invoke` with positional operands,
followed by positional returns. A map derives one typed `Op.map` and return of
its sole result. `MapSpec` retains the helper name, field and ordered mask; its
computed helper signature enforces the scalar root ABI. Checked formation and
raw derivation equations connect each successful `checkDefinition` call to its
retained declaration. Concrete full-unit clients additionally prove exact raw
body equalities for their own checked payload; the per-definition equations
alone do not assert a generic payload/declaration association. The
original declaration acquires no invented body, site, origin or visibility
field.

For complete ordered map arguments, the first row length is checked for
representability below `2^64`. Each later row is then checked for representability
and equality with the first length, in source argument order. An
unrepresentable reached length stops `exhausted`; a representable unequal length
stops `refused` before later shape checks. Only after all rows pass does the map
invoke its checked helper at indices `0, …, n-1`, supplying every scalar operand
in its original position, whether selected from a row or broadcast. Unused rows
still participate in shape validation. Equal empty rows return an empty vector
without invoking the helper. Process bind preserves every reached helper effect
and stop prefix; no zip truncation or liveness-based operand removal is implied.

At the model level, direct optional `Op.map` sequences all operands and stops
`incomplete` if any is absent. Admitted source maps occur in derived Local bodies,
so their source-visible absence boundary is the owned Local call; direct optional
map laws also cover raw typed regions used by generic semantics and tests.
Existing Local helper component invocation retains its own strict wrapper
behavior, and owned protocol invocation requires all inputs before
work; nonowners skip it. Math projection remains optional per result and may
ignore absent unused inputs. These are separate boundaries.

Generic map formula laws require an equation for actual
`invoke table spec.helper` on every reached complete scalar tuple. Concrete
clients discharge that premise using their complete checked helper tables and
exact body views. Helper spelling never supplies a mathematical equation.
Helper inventory, framing, full-table linking, effect interpretation and
all-present component laws use the same node and carrier.

Logical lists and u64 representability are separate from observer vector/work
capacity. Collecting pure row lengths does not perform a representability
prescan: the stopping decision follows the ordered shape prefix above. Native
generated `control.require` uses its own rejection spelling; matching it to
logical `refused` requires an explicit bounded adapter. Internal generated sites
are not claimed equal to retained source sites.

The executable Bounds transfer intersects all retained row-length intervals and
charges every length extraction before helper work. On a possible nonempty
return, it analyzes the actual helper once on the complete scalar atom tuple
and reserves that helper's logical work for each possible row, including dead
nested calls. The resulting vector is bounded by the common successful length;
aggregate tuple work does not consume a different per-vector capacity. Empty
rows avoid helper work only after all shapes pass. Existing analysis, execution
and vector limits are unchanged. These are conservative executable transfers,
not a general bounds-soundness proof. The workload meter counts logical tuple
selections; it does not count the depth of concrete positional list indexing as
CPU steps. No wall-time, allocator-cost or native-capacity theorem is asserted.


## Actual retained preparation subjects

The complete original `map-callers.zkc` captures are retained as `MapFirstData`,
`MapPrefixData`, `MapCombinationData`, `MapConstantData` and
`RealizationValuesData`. Each selected subject includes its whole actual helper
table. First, Prefix and RealizeValues have the singleton role `P`; their checked
closed projection is explicit. Combination and ConstantRows retain roles `P,V`
and use the participant interpretation, including the owner and nonowner cases.

Exact `Views` modules connect typed bodies to retained raw trees. All five
subjects write out their complete checked payloads so downstream dependent types
need not rerun admission. Their `kernel_admission`/`imported` equations still
check equality with the original whole-snapshot checker, including declaration
order, linking, availability and preparation closures. This is a proof of the
checked result, not an assumed result cache. Other body consumers can use named
membership and helper-signature equalities through the explicit-ABI body-view
lemmas. All value equations use the existing interpreter and actual helper table.

| Subject | Source contract | Assumptions and boundaries |
| --- | --- | --- |
| `MapFirst` | Table validation, positive-dimension guard, contiguous split, interpolation map, dimension subtraction and ordered vector/dimension/width result | Logical input lengths and indices satisfy the stated u64 representation premises; invalid shapes and zero dimension reject |
| `MapPrefix` | Ordered finite composition of First, empty-point identity after table validation, overlong-point rejection and ordered append | Same initial representation premises; point length admission precedes iteration, and its exhaustion is retained |
| `MapCombination` | Full owner result `zipWith (fun a b => s*a-t*b+3)`, reached source marks, exact shape stops and nonowner skip | Every row, including unused rows, is representable and has the same length for a successful result; every owned input is present |
| `MapConstant` | Exactly one constant `7` per row, including zero rows, full shape stops and strict owned presence | Unused row shapes and the unused scalar remain required; the nonowner skips the Local call |
| `RealizationValues` | Actual vector projection through the retained realization and unchanged Local values wrapper, preceded by table validation in the full source | The projection/realization itself needs no vector-size or index premise; source validation and optional/owned boundaries remain explicit |

First's shape theorem preserves arbitrary flattened column widths. For one
column, its result decodes to `Multilinear.fixFirst` on the leading Boolean
coordinate. For one column, Prefix's result decodes to `fixPrefix` in the supplied point order,
using `ListRestriction`'s independent contiguous-half and ordered-fold laws.
These statements establish most-significant-bit-first table restriction in the
independent model. They do not establish native lowering correctness or a full
Sumcheck protocol theorem. Source-site observations, finite bridge comparison,
resource preflight and security theorems remain separate evidence.

## Actual library primitive subjects

`PrimitiveShapeData`, `PrimitiveTableData` and `PrimitiveHalvesData` retain fresh
complete original-stage exports of ordinary wrappers around unchanged
`multilinear::has_shape`, `table` and `halves`. The selected closure includes all
retained bindings and helper definitions. Each `Views` module kernel-admits its
whole snapshot and proves the exact raw equality of every typed body it uses.
The independently authored `PrimitiveSequenceData` retains an arithmetic/vector
caller, and `PrimitivePureIndexData` retains a two-role pure-index caller.
Generated constructor data explicitly records original digests; digest agreement
and renderer regeneration are executable source-identity checks, not theorems
about the exporter.

`PrimitiveRows` proves the checked doubling loop using
`Finite.fold_range_state`: after iteration i the state is exactly `2^i`, and
every reached multiplication is within u64. `PrimitiveLibrary` states body
equations under explicit comparison/rows helper premises. Each consumer in
`PrimitiveLibraryConsumers` discharges those premises from its own complete
checked table, using definition membership and exact body equality. A descriptive
helper name alone never supplies a law. `PrimitiveExpansions` contains proved
normal forms of these same bodies, keeping primitive evaluation opaque during
SSA/environment simplification; it adds no interpreter.

For representable vector length, dimension and columns, the complete Shape
wrapper returns exactly
`0 < columns ∧ dimension < 64 ∧ length % columns = 0 ∧ length / columns = 2^dimension`.
Table returns the original three values in order precisely when that predicate
holds, otherwise rejecting. The complete table-then-halves wrapper checks shape
first, then positive dimension, then positive even split length. Its two results
are `take (length / 2)` followed by `drop (length / 2)`.
`PrimitiveContracts` packages successful body contracts: each half has dimension
one smaller and unchanged columns, and concatenating the ordered halves
reconstructs the original vector. The standalone halves helper checks dimension
and split validity; it does not itself check columns or table shape.

`PrimitiveSourceStops` exposes complete original Shape short circuits: zero
columns avoids dimension/length requirements; a representable dimension at least
64 avoids length requirements; an unrepresentable length exhausts only after the
first two guards pass. `PrimitiveSequence.process_equation` covers every logical
input, including checked length/addition, division/remainder and all eight
ordered outputs. Its observed zero-divisor equation, under `length + 1 < 2^64`, retains the
wrapper site and all five reached helper sites for arbitrary vectors, followed
by refusal, excluding the suffix.
`PrimitivePureIndex` proves owner, other-role and missing-input equations on the
actual admitted open subject. The library and complete Sequence value equations use silent site observations;
the separate observed Sequence theorem proves the stated site order. PureIndex
uses the participant denotation that erases marks. No observed Shape/Table/Halves
site equation is asserted here. Typed body views retain the original marks, and
generic interpretation/closed-projection laws remain available.

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
honest-view theorem, with its handwritten honest strategy, to that contract.
No honest-delivery premise supplies the source equality.

`ZkcExamples.Structured.SchnorrHonestProver` additionally obtains both messages
from the actual Interactive prover's ordered send observations. Its
`replyHandler` uses the existing `PIR.Proc.run`, supplies fixed nonce/challenge
replies, acknowledges the two sends, checks domains/sites/peers/service handle,
and logs each actual action. `extract` accepts only a successful `none` result
with exactly the query/send/receive/send shape. It reads the two send payloads;
it does not check or construct the response formula. Stopped, reordered and
extended traces yield no messages. The algebraic `messages_eq` is proved from
the imported `prover_equation`, not assumed in the message definition.
The handler is deterministic for its fixed inputs: any sampling happens outside
the run, and its nonce reply does not inspect the challenge parameter.

`strategyOf` selects the commitment observed with reference challenge zero and
the response observed for each supplied challenge. It requires successful
extraction for every challenge and unwraps those observations without fallback
values. The original `strategy` and the admitted response mutation's
`responseStrategy` use this same constructor. The constructor itself asserts
neither causal timing nor agreement with every run's commitment.
This retrospective extraction
is justified for this source by `execution_eq`, `prefix_independent` and
`commitment_independent`: the commitment precedes the independent challenge
reply, the prefix through the receive request is identical for all replies, and
every fixed challenge completes under the selected successful profile.
`strategy_supplied` identifies both fields with the actual run for every
challenge. There is no generic causal adapter for arbitrary processes here.

`accepts` delivers this strategy to the actual checked verifier through
`Common.transcriptHandler`. Prover/verifier input copies are independent
arguments. Its premises are `proverBase = verifierBase` and
`verifierKey = secret • verifierBase`. The prover key is unconstrained because
the source does not inspect it. These premises express no enforcement mechanism.
`nonce_stopped` and `challenge_stopped` preserve the
exact reached prefixes for every stop reason at those two reply points.
`extract_stopped` proves the decoder returns `none` for every stopped run; there
is no decoder for messages in a prefix. Send acknowledgements succeed and all
owned inputs are supplied in this profile. Send failures and missing owned
inputs are outside these specialized prefix theorems. The existing verifier
delivery handler selects replies by type; matching source sites are certified
by the process equations and extraction, not by a joint routing model.
No arbitrary provider law or joint scheduler is assumed or proved.

The optional `StructuredSchnorrHonestView.sourceView` consists of the observed
commitment/response, fixed challenge and actual verifier outcome under honest
delivery. `sourceView_eq_honestView` transfers it to the existing VCVio view;
`source_honest_verifier_zero_knowledge` samples a uniform nonce with the
challenge fixed outside that sampling, and equates every public-view event to
the existing uniform-response simulator. The simulator takes the public key
without a witness. The private query trace is not part of this public view;
neither the service tag nor handle identity establishes native randomness.

`SchnorrHonestProverControls` retains concrete wrong-verifier-key,
mismatched-base and bad-delivery counterexamples, as well as an accepting
unused-prover-key mismatch. Its changed
response arithmetic and changed response site are separately kernel-admitted
constructor variants with synthetic source markers, not fresh native exports
or subjects identified by the original digest. Changed arithmetic changes the
extracted response, and delivery of those changed source sends to the unchanged
checked verifier is rejected; the changed site refuses extraction. Decoder
controls also reject reversed and extended traces.

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
bytes; domains, relations, bindings and definitions at 128 each; signatures at 512;
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

Before interpretation, `ZkcTools.StructuredSource.Bounds` propagates per-value
index intervals, vector-length intervals and optional presence through the
checked source. This includes generated constants, arithmetic, append, helper
bodies, loops and folds; an input maximum alone is insufficient. Typed received
values use conservative bounds from all matching reply envelopes, including
unused suffixes. A reversed array stores the abstract SSA context while ordered
argument/result tuples retain their list ABI. The preflight never interprets a
helper by its name and does not replace the typed evaluator.

Separate analysis and expanded logical-work meters each allow 1000000 units;
generated vectors are capped at 4096 elements. Work includes nodes, selected
operands, tuples, allocated ranges and vector traversal/serialization. It is
not an exact host instruction, allocation or wall-time bound. Analysis charges
its own expansion and context operations. A known branch or select condition
chooses its reachable alternative after strict/optional presence handling;
unknown conditions join both alternatives. Loop joins and typed unused replies
can still overapproximate the executed path, so a cheap logical run may fail
preflight. Such diagnostics are tool-capacity refusals, distinct from the
process's semantic stops. Transfer soundness and
resource correspondence remain proof obligations; finite controls do not prove
that every input satisfying a source theorem is admitted by this observer.
Analysis exhaustion reports `structured-bounds-analysis-limit`; unsupported or
mismatched abstract shapes report `structured-bounds-unknown`. Work and generated
value caps retain separate closed/open diagnostics. Helpers are resolved in a
bounded per-preflight table with full signature validation, preserving their
checked bodies and ordinary linking.

Native parsing/formation, C++ export, JSON parsing and constructor rendering
remain reviewed executable boundaries. Exact logical equations and bounded
differential comparisons establish different claims. Neither proves native
transformations, production BLS/RNG behavior, runtime execution, authored
relation/formula association, or Fiat–Shamir security.

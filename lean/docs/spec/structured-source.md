# Structured native import

The [native export contract](../../../docs/spec/formats/structured-source.md)
owns `zkc.structured-source/0`. This page owns its independent Lean admission and
logical meaning. It complements the scalar importer; neither silently changes
the other's vocabulary or scope.

## Checked subject

`Zkc.Source.Structured.Snapshot` retains source identity, selected entry and
participant, every domain and definition, visibility, origins, preconditions,
sites, operand positions and ordered results. `Format` reads exact tagged arrays
and rejects unknown tags, extra fields, JSON objects, noncanonical numeric tokens
and unsupported vocabulary, including in dormant bodies.
Canonical decimal constants use a bounded ASCII-digit fold shared with the
scalar importer. This computation reduces in the Lean kernel, so admission of
constructor snapshots containing constants can be proved without native
evaluation. JSON parsing and export correspondence remain separate boundaries.
Logical-origin binding values remain opaque retained metadata. Their membership
in the native identity language is checked by the native verifier; Lean checks
the pair structure, lengths, nonemptiness and key uniqueness.

`check` independently resolves types, helper kinds and signatures, exact bound
provenance, capture forwarding and acyclic dependencies. Each function body is
lowered to the shared `RawRegion` and formed by `RawRegion.elaborate`. A finite
declaration lowers to an owned fold using its exact declaration ABI. Each checked
body is stored once; calls retain named references instead of expanding syntax.
Dependency lists and instruction counts are derived from the formed operation
tree, including every callback and suffix. `CheckedDefinition.helpers_eq_body`
ties the helper inventory to the erasure of that same typed body. There is no
separately maintained dependency log.
Math-return summaries still order their syntactic call subgraph before admission;
the formed inventory checks the complete helper graph afterward.

Ordering produces a candidate. `linkPayload` independently checks that every
declaration name is fresh and every helper signature occurs in its strict
prefix. `Payload.linked` carries this proposition; `DeclarationsLinked.nodup`
derives name uniqueness. The check uses complete signatures and includes dormant
callbacks and stopped suffixes. It does not assume the ordering algorithm is
correct. Missing, forward, mismatched or duplicate links are refused.

`Imported snapshot` uses the common `Verification.Imported` carrier. Its check
witness ties the resulting program to that exact snapshot.
`CheckedDefinition.exactBody` proves that erasure recovers the lowered raw body;
`CheckedDefinition.body_eq_of_raw` recovers the typed body from exact raw equality;
`Imported.exactSubject` retains the complete source descriptor. These are
formation and subject-binding facts. The linking invariant does not prove that
ordering preserves the input declaration inventory, or that lowering faithfully
preserves source metadata and operations. Those are separate correspondence
obligations. A successful computational bounds check
does not itself constitute a general theorem that every admitted Math function
is total.

## Static bounds

A bound records an exact index/container pair. Result binding shifts both
positions. Conservative result-to-input summaries follow direct returns,
reordered or repeated outputs, shared Math calls and select arms with the same
known canonical identity. Two unknown origins never establish identity.
Each Math helper is summarized once after its callees, without expanding calls.
Admission normalizes operand identities through these summaries; unknown results
receive fresh identities. The summary algorithm is a computational check;
its general semantic preservation theorem remains a separate obligation.
Local control regions start without facts because Local definitions
cannot declare bound premises in this profile.
Math preconditions are local assumptions, instantiated and discharged at every
call. An indices domain supplies the bound for its selected vector in the
step's `S / I / A / C` interface, including another invariant formal supplied
with the same proven value identity, including helper-return aliases. Mutable state is not assumed invariant across
iterations. Matching types or equal lengths do not identify vector contents.

Math cannot contain an authored stop or invoke Local code. Local code may stop, including during
a zero-result call. The profile admits only immutable Boolean, index, scalar
and vector values. It makes no affine ownership claim.
Operation ownership is checked explicitly for each body kind, following the
native format's ownership table. The independent model supports vector and
index selection, although the current native mathematical verifier does not
yet admit those selection types.

## Owned meaning

`Meaning` assigns the nominal field explicitly to a commutative ring `F`,
indices to natural numbers and vectors to lists. The command-line runner uses
the actual BLS12-381 scalar modulus:

```text
52435875175126190479447740508185965837690552500527637822603658699938581184513
```

The meaning is a closed `PIR.Proc`, preserving returned ordered values and all
stop reasons. Named helpers resolve through an acyclic table of already
interpreted checked bodies; semantics has no arbitrary recursion fuel. Region
callbacks are invoked with closed arguments. The owned operations do not
inspect callback process constructors.

The defensive helper-resolution fallback and failed checked reads both stop
with `refused`, as does an authored `refused` stop.
`Payload.invoke_declaration` resolves any declaration in a checked table to its
body interpreted against its strict prefix. `Payload.declaration_helpers` gives
exact prefix membership for all its calls. `Payload.reference_resolves` supplies
an exact-signature lookup in the captured prefix. `Payload.invoke_body_view`
exposes a named helper against the complete table using an exact body equation;
proof clients need not unfold prefix construction or depend on declaration
indices. These linking laws do not rule out
failed reads or authored stops inside a resolved body.
Successful admission supplies a proved linking invariant, but does not prove
native formation, general read safety or Math totality. `check_ok_inversion` states only successful
checking and exact subject retention.

Folds use the shared ordered `Finite.execute`: domain admission precedes
iteration, the predicate precedes each selected step, false preserves current
state, and a stop bypasses the suffix. `boundedAt` is a checked read; an invalid
index refuses rather than returning an arbitrary default. Counted loops retain
their state/capture split and conditional completion flag.
An unconditional stop cannot replace a condition terminator; it belongs to the
ordinary loop form. Stops in nested branches remain valid.
`denoteLoop_reference` transfers a callback equation under a reachable-state
invariant to the ordered loop. Empty ordinary and conditional loops return the
initial state without invoking their callback.

## Optional component meaning

`Structured.HelperTable Value interface` owns generic exact-signature lookup.
The existing `FunctionMeaning`, `DenotedDefinition` and `Meanings` are closed
scalar specializations, so finite clients keep their original theorem statements.
`ComponentTables` builds two instances of this table from each stored typed body:
one closed closure and one optional closure, both capturing the preceding tables.
It stores no second body and expands no call syntax. `componentTables_closed`
identifies its closed projection with the original `Payload.meanings`.

`componentOperation` passes optional operands directly into the named component
closure at `Op.invoke`. Thus `first(x,y)` can return present `x` when `y` is
absent, including through another named helper. A constant needs no input, and
different returned components can have different availability. Every other
operation uses `strictComponent` and the existing closed operation implementation;
arithmetic cases are shared. Primitive select still needs its condition even
when both arms agree. Branch, loop and fold execution retains closed callbacks.
Absent strict operands skip the operation; in particular an absent guard has no
effect, while a present false guard retains its `reject` stop.

`ComponentTables.adequate_extend` and `adequate_fold` relate invocation in the
two tables on present input tuples. `Payload.component_present` equates the
optional execution with the original closed process followed by marking its
results present, including stops and zero-result computations. Table adequacy
does not require successful linking; the exact resolution and framing laws do.
`Payload.component_reference_resolves` proves prefix resolution for every stored
reference, including dormant callbacks. `component_invoke_declaration` gives the
captured-prefix equation; `component_invoke_body`, `component_body_view` and
`component_entry` give full-table equations. `region_component_table_congr`
requires agreement on both closed and component helper invocations because
callbacks and strict operations use the closed table.

This interpretation is an auxiliary denotation, not participant dispatch or
availability formation. The current `Op.invoke` has lost the source distinction
between Math and Local calls. Applying its optional rule to every invocation
does not implement Local ownership. A future Local boundary must sequence all
arguments at its owner, invoke the closed closure and preserve stops; nonowners
must not execute it. The private adapter test demonstrates this distinction
without claiming that the admitted operation language records it.

Result dependency summaries and separate requirements for every intermediate
remain unimplemented. `unused_intermediate_returns` in `Tests.StructuredComponents`
is a model counterexample to inferring formation from an available output, not
an admitted multi-role native program. No native format/profile, group vocabulary,
open protocol import, or eager-versus-demand-driven Math correspondence is added.
Future group operations can reuse the generic table and optional interpreter,
but require an explicit value assignment and one closed operation implementation.
No whole-import or native correspondence follows from all-present adequacy.

## Compositional contracts

`Structured.region_denote_table_congr` proves that agreeing on the exact helper inventory
preserves the complete region process. It covers nested callbacks, branches,
loops and fold predicates; unrelated bindings cannot affect the computation.
The inventory is derived from the same typed body used by the meaning. The law
does not require helpers to return normally.

`Region.Contract` states immediate return under an explicit input premise and
relates ordered outputs to the original environment. Contracts compose through
lexical binding, can strengthen premises and weaken conclusions, and transport
through exact process equality. For a checked read, the premise concerns the
exact vector and index. Representability, shape and range conditions remain
visible; an operation annotation is not a proof of unconditional totality.
These predicates fit the existing `Verification.Certificate` interface.

## Tools and practical bounds

```text
structured-source check SNAPSHOT.json
structured-source run SNAPSHOT.json INPUTS.json
```

Inputs are an ordered array of typed values:

```text
["bool", value]
["index", unsigned-number]
["field", "bls12-381.fr", canonical-decimal-string]
["vector", "bls12-381.fr", [canonical-decimal-strings...]]
```

A run returns `["returned", typed-values]` or `["stopped", reason]`.
Import, input and evaluation-capacity refusals have a nonzero tool exit; they
are distinct from successfully reporting a semantic stop.

The file reader bounds complete snapshot bytes to 1 MiB, including whitespace.
Admission bounds strings to 512 UTF-8 bytes, domains and
definitions to 128 each, signatures to 512, instructions and references to
4096, and nesting and helper depth to 64. Terminators and domain constructors do
not count as instructions; each finite declaration contributes one fold.
The helper inventory has at most two references per stored instruction, so it
needs no additional edge budget.
Input instruction preflight bounds work before summarization. The formed-body
count separately checks the resulting IR, so future lowering cannot silently
exceed that limit by introducing operations.
Shared call trees are not expanded during admission. The separate CLI work
estimate can refuse an admitted helper DAG whose execution would be too large.
The CLI has additional input and evaluation limits so a valid mathematical
program need not be executed with unbounded host resources. These limits do
not become fuel parameters in semantic theorems.

## Verification scope

The first clients concern the actual total-state and unit-state finite native
fixtures. Their complete model equations distinguish ordered multiple results
and stopping zero-result folds. Schnorr and the multilinear Sumcheck library are the subsequent
whole-protocol targets described in the
[design](../design/structured-native-import.md); the current single-participant
profile does not import their group/service communication.

Native parsing/formation, C++ export, JSON parsing and transparent constructor
rendering remain reviewed executable boundaries. The byte digest identifies
a subject and cannot replace correspondence. Model equations and bounded
native comparisons establish different claims. Frontend and optimizer
correctness, participant projection, native cleanup/capacity, production
arithmetic/sampling and cryptographic security require separate connections.

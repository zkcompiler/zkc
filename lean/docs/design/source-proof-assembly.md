# Assembling source proofs from mathematical premises

The execution model remains the admitted typed `Region`, its `PIR.Process`,
and the selected handler. The outstanding authoring problem is construction of
proofs about that model. A library of sound local rules is necessary, but does
not by itself remove an author's traversal of a new source body.

`FriCommitReply.installed` exposed this gap: its old proof selected marks,
restrictions, comparisons, guards, assembly and oracle operations. It now uses
the common `derive_oracle_returns` constructor. Its remaining premises describe
the length helper, provider associations and the mathematical output relation.
The actual Check admission prefix now uses the same constructor, retaining its
original mathematical and provider premises and projected loop operands. These
two migrations close their traversal gaps; the complete FRI endpoint and general
authoring acceptance remain separate requirements.

## Boundaries of an author's contribution

| Obligation | Owner and intended reuse |
|---|---|
| A handle denotes a particular polynomial or word | A representation or provider law. Source installation supplies the actual returned handle; equal types do not establish association. |
| Successive words satisfy the FRI folding relation | The FRI mathematical library. It is independent of SSA slots, marks and continuation records. |
| A saved reference survives permitted store changes | A common provider or realization law, under explicit extension and non-shadowing premises. |
| The next component's input relation follows from the previous output relation | A mathematical connection theorem stated against the two interfaces. Call installation supplies the actual operands and captures. |
| A loop preserves a new algebraic invariant | The component library or companion supplies initialization, step and exit mathematics. The common layer supplies iteration order, typed routing and stop propagation. |
| A source mark, result tuple or unchanged caller frame is routed correctly | Common proof construction, derived from the admitted body and proved operation laws. |
| A call preserves a resource or store outside its footprint | Common composition consumes the callee's preservation law. Neither a type nor the absence of a visible write is sufficient evidence about a handler. |
| A security reduction preserves access, correlations and charges | A property-specific library theorem over the selected experiment; it cannot be inferred from a return-value equation. |

Some obligations are mixed. A virtual oracle's captures can be routed and kept
alive structurally, while the fact that those captures denote the intended
folded polynomial remains mathematics. The author supplies that latter law
once; the application constructor must not ask the author to restate it with
generated positions at each call.

## Common judgments and assembly

Use the existing execution and security judgments for their respective jobs.

1. Local execution specifications relate a precondition to actual returned
   values, state and ordered observations, with a separate stopped
   postcondition. They permit a guard to establish a proposition about a
   successful continuation, rather than requiring a fixed reply and a manual
   early case split for every instruction.
2. Typed region rules bind these specifications at the actual ordered operands,
   compose continuations, and expose mathematical implications. Reuse checks
   the callee and captured dependencies as well as its input/output types.
3. Source/realization simulation relates both executions and their accessible
   state. It handles compiler-generated control that is absent from the source.
   A unary return specification is not a substitute for this relation.
4. Honest completeness and security transport consume the completed execution
   connections. Their termination, probability, attacker and cost premises
   remain explicit.

`MonadicWeakestPrecondition` adapts `Process.runM` and Lean's bind-faithful
`Ensures` to `Std.WP`; it adds no evaluator. Its assertions include state and
event history on both returns and stops. `RegionReturnSpecification` connects
the existing `ReturnsSatisfying` judgment to that interface and provides typed
region rules. Handler selection is local, not a global instance.

The current standard `vcgen` tests compose a guarded component with a second
read and preserve exact state changes and event order. An abstract-handler test
also reuses an existing fixed-reply law. These are useful tests of the common
interface, **not** evidence of complete source-authoring automation.

A bounded comparison against Lean 4.36.0-rc1 isolates a relevant limitation of
4.35.0. A reduced typed mark/restriction/return region, using zkc's actual
`Region`, `Values`, `Process` and locally selected monadic WP, fails to apply
its generic restriction specification on 4.35 and succeeds on 4.36-rc1. The
mark-only case succeeds on both. Upstream [Lean PR15555](https://github.com/leanprover/lean4/pull/15555)
changes specification-rule construction to reuse the goal's WP instance; its
own regression also reproduces that version difference. This establishes the
patch's relevance, not isolated causal attribution for every FRI failure.

On the pinned toolchain, the actual FRI mark region passes, and a fixed-reply
adapter gets its terminal reply through the restriction. The next obstacle is
installation of a helper law at symbolic arguments: a concrete input equation
does not match the unknown result of a preceding operation merely because an
equality will later relate them. Canonical operation heads and specification
preconditions must expose that association. The actual Sumcheck terminal's
complete decision equation composes with `vcgen`, retaining all size guards,
stopped reasons, state and ordered observations. This reuses an existing source
equation; it does not automate that equation's original derivation.

Therefore `vcgen` remains the preferred execution-specification engine, but the
full FRI suffix has not yet passed through it. The repository toolchain remains
unchanged. An isolated backport attempt failed in tactic/plugin loading and is
not validation of either a proof or a semantic refusal. The existing typed
constructor remains the working implementation until the same client statement
and premises pass through the consolidated path. Do not grow a parallel
protocol-specific visitor to work around specification installation.

The implementation must preserve a stable typed source boundary when selecting
rules. Unfolding the entire installed table to find a mark is not the desired
proof-construction interface. Prefer standard proof tooling where it composes
the rules reliably; otherwise isolate the necessary typed rule selection in
one common, kernel-checked proof producer. Neither option permits a new
protocol-specific source visitor.

`OracleReturnConstruction.derive_oracle_returns` selects operations from the
actual typed region and composes their return specifications. Checked operations
introduce their successful condition in the continuation; the common rule
handles the refused branch. Marks, operand selection, result environments and
preservation composition are constructed once in the common layer. The author
provides semantic facts, for example:

```lean
derive_oracle_returns [helperLaw, publicationLaw]
-- Prove the mathematical consequence of the learned conditions and outputs.
```

The complete `FriBindingExecution.installed` component also uses this constructor.
Its separate process presentation and `derive_receiver_returns` traversal are
removed. The reusable input/component laws now live with `ReceiverForwarding`.
`ProtocolAlgebra.invokeReturns` installs a body return specification at the
linked declaration and derives its boundary masks. The binder retains its
explicit participant-placement facts and named forwarding plan; it supplies no
source walk, per-operation frame proof or output tuple reconstruction. This is
complete adoption for the binding component, not for all FRI phases.

`OperationFacts` filters supplied facts by judgment, typed source operation and
request identity before attempting semantic unification. It then uses ordinary
Lean theorem application and bounded premise search. These keys only select a
candidate: the complete law, arguments, captured meaning and expected reply must
still type-check. Malformed fact terms and resource failures remain errors.
Quantified helper facts are installed by exposing the ordered `present` tuple
before matching their parameters. This avoids dependent-cast reduction blocking
on unknown arguments; the original, unexpanded law is then checked again.
Mathematical payloads remain opaque, and every unsolved law premise must still
be discharged. The FRI virtual body now uses this path for its pair-index,
power and fold equations. Its existing statement and mathematical premises are
unchanged; the manual two-query traversal is removed.
The constructor reduces an explicit index constant directly; it does not try to
execute an arbitrary installed mathematical helper while looking for a return
rule. Existing operation laws and fixed-reply equations have adapters into the
same return construction.

The common return projection follows typed references through explicit result
prefixes and leaves an unknown caller frame opaque. It reconstructs the actual
ordered output tuple by kernel-checked conversion. The FRI author no longer
repeats that tuple or its generated positions in the proof.

The constructor currently covers straight-line regions, active local calls,
checked guards and oracle operations with supplied provider laws. It requires
an actual return or stop at the end; unsupported operations fail construction.
The returned proposition concerns successful records and invariant preservation
on all records. It does not prove termination or probability mass, and does not
replace the relational controller proof below.

`Tests.OracleReturnConstruction` adds components with different guards and return
layouts, and a new helper client whose mathematical equation is supplied
independently of its source site. None imports FRI or Sumcheck or adds a source
visitor. A semantic theorem excludes exchanging two same-typed output ports.
A foreign-helper control retains absent operands through an index comparison
and an inactive guard. A linked-call control checks the actual output mask and
rejects exposing a foreign same-typed result. These tests demonstrate new structural assembly; the helper equation is an
explicit premise, not a newly proved mathematical result. The actual FRI
consumers supply their already proved helper and provider laws. A projected-return
control also rejects an unrelated same-typed helper law during construction, then
succeeds with the correct law. This is an installation control, distinct from the
semantic result-swap control.

`Tests.OracleBodyConstruction` covers a different virtual component with two
distinct handles, arbitrary query sites and a captured parameter. Its sole
helper equation is quantified over the two replies. Common construction supplies
the query order, capture routing and result layout; it needs no reply-variable
names or source visitor. A semantic theorem rejects exchanging the two handles,
and fact-installation controls retain an additional mathematical premise.

## Upstream reuse and one author interface

The author interface should extend the existing named helper presentations and
source-addressed companions. A component contributes its mathematical law,
representation and invariants. Common installation fixes the body, role,
captures and actual arguments before selecting that law. Exact equations,
return specifications, simulations and probabilistic claims retain separate
types; common source decomposition and installation do not identify them.
The existing `NormalForm.ActionForm` and `Region.Derivation` already provide a
checked source decomposition, including callbacks. They are the starting point
for shared structural work, not an invitation to add another interpreter.

The pinned PolyFun (`a5edfe2dd24d9d76f9a13cc1f131b220617ad534`) provides
operation specifications, `wpFold`, `WPMonad`, and transport through monad
homomorphisms. Its syntactic fold and semantic handler WP are related by an
inequality; equality additionally needs exact operation laws and an exact-WP
interpretation. These are useful optional adapters, but importing PolyFun into the Std-only execution layer would not
remove the need to relate its model to `Process.runM`. Such a correspondence
must preserve short-circuit stops, the reached state, ordered observations and
outer-monad missing mass. No losslessness conclusion follows from the current
`Ensures` adapter.

The pinned ArkLib (`1e0241333c18d8b22cb68f9522da5f9fb88f9a06`) provides oracle
execution and soundness composition in `Interaction/Oracle/Composition.lean`
and `CompositionSoundness.lean`. Its exported interfaces retain a public
statement, closed oracle and private continuation from the same reached run;
composition restricts what a selector may observe. These are candidates for
security composition after the actual source-to-interface correspondence is
proved. They neither construct a source traversal nor justify replacing the
published word or hidden continuation with a fresh one. The current FRI
mathematical theorem reuse is narrower than that full composition adapter.

Within this package, consolidate operation-specification installation and
adopt the shared construction on both actual clients before retiring replaced
manual paths. Keep relational controller simulation and probability transport
as distinct consumers. A repository-wide toolchain upgrade, a PolyFun core
dependency and a general ArkLib exported-interface adapter require their own
dependency and correspondence evidence; none is a prerequisite inferred just
from similar API names.

## Generated query controller

The controller needs one common relational invariant, rather than a collection
of FRI-specific interpretations of its physical blocks. It relates:

- the pending original query and its continuation to the current physical phase;
- logical anchors and captured contexts to immutable physical records;
- each saved frame to its outer continuation, parent instance and position;
- ordered, typed prior child answers and the just-returned answer;
- the live caller frame, source-relative identity and outstanding resource budget.

`OracleProcessLocation` exposes the existing open source computation at its
immutable installation. Fresh newer entries preserve that computation before
choosing a provider. Base requests retain arbitrary outcomes, reached provider
state and event order; failed admission still records and charges its logical
query. Virtual requests run their original checked body and captures against
the installation's older registry. `VirtualStorage.Stored.source_process`
recovers that registry from the reached storage relation and source reachability.
The actual two-query installation test consumes this equation after a later
real construction. An additional same-anchor replacement control changes the
open computation despite preserving its answer type. These are source-side
equations for the controller proof, not a completed target simulation.

The common proof must cover entry, child dispatch, save, return, resume, final
answer, refusal and exhaustion. Each branch needs its reached-operand and
capacity premises. A theorem for one physical fragment does not establish
reachability of that fragment or the whole controller invariant.

`QuerySourceContinuation` uses the existing `PIR.Reaches` judgment to relate
ordered saved answers to the remaining original body. Each returned child
extends a kind-indexed answer tuple and advances that body's actual
continuation; its physical index is justified by `QueryContinuation.AnswersRead`.
The initial cursor is the source itself, and append-only arena extension
preserves the association. An empty prefix cannot skip a request. A one-answer
prefix determines the first request, its stored reply and its continuation.
The checked-source controls reject a redirected same-typed handle and a reply
fabricated from a stopped source. Repeated requests remain separate positions.
This is a source-side invariant, not another virtual evaluator or a proof that
the selected provider actually returned the saved replies. Whole-controller
simulation must establish those returns, static continuation selection and
the captured source instance when saving and restoring each physical frame.

`QuerySourceExecution.Produced` strengthens that cursor with a derivation of
each actual child execution. The common rules derive both the typed saved
cursor and reachability in `OracleProcess.present`; they retain the provider
poststate, interaction phase and ordered events. A stopped child closes the
source path without adding an answer. `OracleProcessContinuation` proves the
outcome-preserving source cut and sequencing equations against that same
presentation, including stopped prefixes. There is no additional evaluator.

The stronger relation is necessary even when an open residual computation is
known. The checked-source counterexample in `Tests.QuerySourceExecution` ignores
its first answer: a cursor containing 99 and the eventual execution computation
both pass independently although the actual child returns 10. The `Produced`
derivation rejects their combination because it requires the very same reply
for the child execution and saved cell. This is an infrastructure obligation,
not a new mathematical premise for that component's author.

`QuerySavedSource` connects a saved frame to its immutable installed parent,
original capture tuple and source cursor. The frame's parent instance and
position determine that body's arguments. Common storage laws derive capture
and body uniqueness, and preserve the suspension across fresh registry and
arena growth. Actual load/unpack restores these same coordinates; the stronger
`load_produced` rule also consumes the child's actual execution evidence. The
fixture uses a real checked source installation and rejects swapped parent
coordinates and substituted same-typed captured handles. Static continuation
dispatch, reached controller phases and nested-frame composition still belong
to the whole-controller proof; these local relations do not establish them.

`TestsArkLib.FriSourceContinuation.installed` consumes the same common cursor
rules on the installed FRI virtual declaration. It reuses `VirtualReads.twoReads`
and its existing helper/mathematical installation, then appends the two actual
kind-indexed arena cells. It adds no source traversal, generated coordinate or
mathematical assumption. This demonstrates the source-side reuse of the rule;
it does not assert execution of the generated return arm or the whole root.
Its `produced` companion now uses the same common progress constructors with
the actual child executions, carrying their poststates, phases and logs through
that installed mathematical connection. The mathematical/helper installation
is unchanged and remains part of the author-effort account.

`RecordAppend` now proves the exact length/pack/append fragment, including the
old length as the new slot and preservation of the caller's prefix.
`QueryContinuation` proves frame encoding uniqueness, save/load, preservation
under arena extension, and ordered heterogeneous answer recovery. Their
mutation controls reject parent-coordinate and same-typed answer swaps.
The selected static continuation still determines the parent constructor and
answer kinds; the record alone does not justify that selection.

`QueryContinuationProjection` composes the actual saved-slot load and complete
nominal unpack. The shared `RecordProjection.allFields` rule derives the ordered
tuple from the declared product, including fields with identical types. The
frame's outer continuation, parent instance/position and prior answer indices
therefore come from its immutable saved record. Recognition checks the entire
fragment, actual SSA slot and field order; it does not infer source ownership
from a generated name. The surrounding invariant still selects the correct
static continuation and associates its frame arena with that source suspension.

`AnswerReads` connects ordered heterogeneous arena reads to actual constructed
instructions. Its operand readback determines a unique answer tuple, remains
valid under caller-frame extension, and agrees with the existing whole-tuple
encoding used by mathematical calls. A missing first answer refuses before the
suffix runs. The rule specializes to all four two-answer read blocks in the
retained FRI participant. The controller must still establish the reached
readback from its saved continuation and actual child execution.

`QueryAnswerReads` now composes kind-indexed saved-answer lookup with the
physical readback. Its `ArenaOperands` premise associates each actual arena and
index operand with the selected kind and saved slot before forgetting kinds in
the returned value tuple. This prevents conflating distinct arenas merely
because their answer types coincide. It preserves arbitrary caller suffixes;
a semantic control rejects a type-correct arena swap. Reaching those operands
and selecting the continuation remain controller obligations.

`QueryResumption` composes checked requirements with answer insertion for the
entire resumption block. Phase and kind checks precede all five request
coordinates; only then does the checked arena length precede append. Successful
resumption determines the same saved request and parent continuation coordinates.
The proof includes refusal, exhaustion, and every caller-frame checkpoint. It
applies to all four actual resumption blocks in the retained FRI participant,
including the reflexive coordinate comparisons left by inlining. Those still
check machine-index bounds. The returned answer slot is the arena's old length.

`RequiredIndices` owns the ordered requirement proof; `ConnectionClosedSimulation`
composes known closed returns and stops without obligations at unreachable
returned values. Neither introduces another evaluator or a source-authoring
visitor. The resumption rule still requires the surrounding controller to
associate the reached operands with its pending source query. Ordinary request
coordinates are not unforgeable or single-use capabilities.

`QueryResumptionOutput` derives the entire returned controller tuple from the
actual SSA references: the five saved coordinates, checked kind, Return phase,
old arena length as answer index, updated answer arena and other retained stores.
All four emitted FRI return layouts have been checked against this projection.

`RecordProjection` and `RecordLookupProjection` derive ordered typed field
selection from the immutable record actually returned by lookup. Nominal identity,
record reference, result sorts and selection order are checked together. The
same rule permits repeated fields and arbitrary caller placements; equal result
types do not identify two field selections. The number of projected SSA results
follows from the checked local types.

`QueryReadResponse` composes checked table access with the complete resumption
and output projection. Its table query position is derived from the saved request
coordinates, and the answer operand must be the actual newly read field value.
`ConnectionClosedSimulation.continueClosed` supplies composition across both
returns and stops of that closed computation. An invalid read refuses before
any later resumption check or arena exhaustion.

`BaseQueryResponse` composes lookup, projection and read/resumption into one
complete clear-base arm. It checks contiguous SSA placement and derives the
intermediate frame length. The four actual FRI arms specialize this same law.
`ClearStorage.Stored.response_simulation` now composes that arm with the
published-word relation. The immutable record supplies its rows and cells;
ordered nominal field selection supplies their actual SSA operands. The pending
coordinates supply the lookup constructor, instance and query position. No
separate equation for projected cells or intermediate header preservation is
required. Stored and requested shape annotations may differ when both admit
the word's length. Out-of-range refusal precedes resumption and allocation.
The four actual FRI arms pass the geometry and complete-body checks, conditional
on the source publication layout; those checks do not identify a publication by
its physical layout alone. The surrounding controller still establishes the
reached record association, header, arena and retained-store readback.

`ConnectionLocalRange` composes callbacks through the existing constructed
conditional range. Its callback judgment relates the complete typed yield,
including the continuation flag, to the next source state. Shared composition
handles caller checkpoints, finite iteration, early exit and final projection.
A false continuation skips later callbacks; it is distinct from a stopped
execution. Region formation still precedes a zero-trip interval. All eight
retained FRI ranges pass formation and specialize this rule, with the callback
invariant still explicit. A finite loop bound does not prove that the controller
has reached a request or completion: its state invariant and decreasing work
measure must separately justify the final phase requirement.

`ConnectionLocalRangeProgress` derives finite-range exit from a preserved
invariant and a decreasing natural rank on continuing returns. The strict
iteration bound includes the extra iteration that observes completion. A stop
remains a stop, so this theorem does not establish honest termination.

The range's final physical condition now composes with that proof through
`completedSimulation` and `Simulation.refineReturns`. Exit meaning is a separate
checked obligation: an early false yield at Return is compatible with decreasing
work but does not establish Request or Completed. `QueryWork.advance_completed`
and `evaluation_completed` consume the actual phase/flag correspondence and
derive those respective postconditions. The actual-body certificate retains
its source, target, output layout and all frame checkpoints when strengthened.
These rules close loop composition; branch reachability and source expansion
still have to instantiate their common invariant.

`QueryPhaseYield` derives the continuation flag from the actual final comparison
and full returned tuple. Recognition checks that the comparison reads that
tuple's phase field and yields the Boolean it produced; it rejects a same-typed
kind-field substitution, reversed comparison or different Boolean operand.
The reached tuple supplies the phase value through common SSA readback, so the
callback need not assume an independent equation for the flag. Advance and
evaluation retain their distinct thresholds, two and three. This rule connects
the iteration's end; the preceding dispatch still establishes the source state
and work transition.

`QueryWork` supplies the common rank and allocation arithmetic for depth-first
query expansion. It is an erased work relation, carrying no values, positions,
provider or outcome. It counts repeated child occurrences separately and
distinguishes a zero-query virtual node from a base-provider leaf. One successful
complete expansion uses twice its node count in administrative transitions,
one reply per base leaf, one answer per node and one saved frame per tree edge.
The same accounting bounds every partial prefix and derives room for its next
allocation. The controller must connect these steps to the actual source body
and physical branches and derive the expansion's size from source admission.
An abstract work bound alone does not discharge that connection.

The next composition step must establish this invariant from the actual
generated controller and retain it across every branch. The companion supplies
the virtual oracle's mathematical meaning and any new mathematical invariant;
it must not supply the dispatch traversal. Generated delivery separately proves
that the physical publication implements the original source publication.
Generated names do not satisfy the ordinary source-occurrence check.

## Disposition of the revised closing review

The review at `62bb4ed39` was checked against the later implementation, rather
than treated as a new package plan. Shared typed construction, distinct exact,
return and relational judgments, and checked mathematical-law installation were
already present. The base-arm provider connection and common progress/allocation
laws above advance the controller obligations identified in that review. The
instantiated whole-controller relation and the original endpoints remain gates.

The saved-parent installation, outcome-preserving continuation laws and
`Produced` progress derivation repair concrete parts of that infrastructure.
In particular, the unused-answer counterexample rules out treating two
independent final-result/cursor proofs as evidence of a child's production.
The actual FRI body reuses the same progress constructors and existing
mathematical installation. These repairs do not move the generated invariant
into its companion or substitute the fragment checks for the complete roots.

`OracleMathEnvironment.invokePresent` and `invokeReturned` install the existing
`ReferenceLaw` at its actual helper body and arguments. FRI's `powerRequires`,
`pairCall`, `powerCall` and `foldCall` include dependency association, typed input
and output assembly, and genuine mathematical premises. Count that work in the
authoring account; the short `bodyReads` traversal is not its total cost.
`Tests.FriBindingSites.bothSites` already checks component placement reuse at
two actual calls. It does not, on its own, discharge the separate new
mathematical-connection gate. Reuse existing installation for that gate where it
suffices. Broad module moves, optional discovery/search and a toolchain change
remain later decisions supported by evidence after this package lands.

## Acceptance and cost accounting

Keep the original Sumcheck and FRI endpoints. FRI still needs universal paired
honest completeness, complete source/realization correspondence, and compiled
accepting/far transport with actual access and retry accounting. The existing
interactive theorem does not close those obligations.

Authoring acceptance additionally requires:

1. Reuse the same mathematical theorem at a second valid actual call, with
   different arguments or captures, and reject a broken same-typed association.
2. Add a structurally different component through the same operation rules and
   constructor, without writing a new traversal or protocol-specific generator.
3. Install a new mathematical connection between two interfaces at multiple
   source calls without rewriting that theorem in source-layout terms.
4. Preserve early rejection, nested continuations, shared state and work already
   performed. A timeout or missing execution result is not semantic refusal.

For each experiment, report handwritten mathematics, representation laws,
invariants/security assumptions, configuration, structural glue and any
protocol-specific generator code separately. Distinguish common-library
investment, first-component cost and second-use cost. Record incremental
checking time with source/toolchain/dependency pins and the final affected
integration check. Generated-line reductions alone do not measure author cost.

The Sumcheck/GKR round-representation example tests reuse of mathematical
security reasoning across encodings. The second Sumcheck call tests installation
and frames. Neither substitutes for the new-component experiment or establishes
a complete GKR endpoint.

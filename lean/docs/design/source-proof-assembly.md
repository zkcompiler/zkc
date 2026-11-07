# Assembling source proofs from mathematical premises

The execution model remains the admitted typed `Region`, its `PIR.Process`,
and the selected handler. The outstanding authoring problem is construction of
proofs about that model. A library of sound local rules is necessary, but does
not by itself remove an author's traversal of a new source body.

`FriCommitReply.installed` is a concrete counterexample to claiming that this
work is finished. Its operation laws are reusable, but its proof still selects
marks, restrictions, comparisons, guards, assembly and oracle operations. The
complete FRI endpoint and the elimination of this author-owned traversal are
separate acceptance requirements.

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
interface, **not** evidence of complete source-authoring automation. The
isolated `FriCommitReply` migration still fails specification matching on
dependent source operations. The production proof has not been replaced.

The implementation must preserve a stable typed source boundary when selecting
rules. Unfolding the entire installed table to find a mark is not the desired
proof-construction interface. Prefer standard proof tooling where it composes
the rules reliably; otherwise isolate the necessary typed rule selection in
one common, kernel-checked proof producer. Neither option permits a new
protocol-specific source visitor. The concrete tactic interface remains under
evaluation until both actual clients and a new component pass.

## Generated query controller

The controller needs one common relational invariant, rather than a collection
of FRI-specific interpretations of its physical blocks. It relates:

- the pending original query and its continuation to the current physical phase;
- logical anchors and captured contexts to immutable physical records;
- each saved frame to its outer continuation, parent instance and position;
- ordered, typed prior child answers and the just-returned answer;
- the live caller frame, source-relative identity and outstanding resource budget.

The common proof must cover entry, child dispatch, save, return, resume, final
answer, refusal and exhaustion. Each branch needs its reached-operand and
capacity premises. A theorem for one physical fragment does not establish
reachability of that fragment or the whole controller invariant.

`RecordAppend` now proves the exact length/pack/append fragment, including the
old length as the new slot and preservation of the caller's prefix.
`QueryContinuation` proves frame encoding uniqueness, save/load, preservation
under arena extension, and ordered heterogeneous answer recovery. Their
mutation controls reject parent-coordinate and same-typed answer swaps.
The selected static continuation still determines the parent constructor and
answer kinds; the record alone does not justify that selection.

The next composition step must establish this invariant from the actual
generated controller and retain it across every branch. The companion supplies
the virtual oracle's mathematical meaning and any new mathematical invariant;
it must not supply the dispatch traversal. Generated delivery separately proves
that the physical publication implements the original source publication.
Generated names do not satisfy the ordinary source-occurrence check.

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

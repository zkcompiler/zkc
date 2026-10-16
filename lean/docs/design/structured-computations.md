# Structured computations

## Decision and ownership

Use `Source.Region` as the canonical Lean carrier for local structured compiler
programs. Native MLIR remains the production representation. `Source.Dialect`
supplies binding signatures; `RegionMeaning` supplies the operation contracts;
`PIR.Proc` supplies ordered interactions and stopping. No external SSA framework
is a production dependency of this foundation.

This follows an implemented comparison of an owned carrier and LeanMLIR on the
same native transformation examples. Both could express the required programs
and prove the same open-process equations. The selected foundation reuses zkc's
existing contexts and process semantics. The remaining hard obligations concern
operation contracts, admission, projection and correspondence. The choice should
be revisited if generic verified rewriting becomes a major requirement or owned
binding infrastructure grows into a substantial framework.

## Binding and region interfaces

A dialect declares, for each operation:

- ordered operand types;
- ordered result types;
- ordered region signatures, each with input and output types.

A region has an input context and an output list. Its constructors are return,
stop, operation binding and shared sequential binding. Binding prepends results
in declaration order: result zero becomes reference zero, and the old context
starts after the entire result prefix. Returning no values is valid. A zero-result
operation still executes, can interact, and can fail.

Operation callbacks are closed over their declared inputs. A control descriptor passes
captured values as ordinary operation operands and explicitly supplies them when
invoking a callback. Renaming the enclosing context changes those operands and
the suffix; it leaves the closed body unchanged. This is an explicit-capture
normal form. Current zkc native regions are isolated with explicit captures.
Their adapter must check the actual capture maps, generated control inputs,
yield forwarding and helper identities. A future profile with implicit captures
would additionally need checked closure conversion.

For example, the scalar reference adapter uses these signatures:

| Descriptor | Operands | Regions | Results |
|---|---|---|---|
| Scalar operation | Declared scalar operands | None | One declared result |
| Branch | Condition followed by captures `C` | Two regions `C → [R]` | `[R]` |
| Repeat | Accumulator followed by captures `C` | One region `A :: C → [A]` | `[A]` |

A finite fold can use an accumulator tuple, dynamic domain values and a body with
explicit item and capture inputs. These are operation contracts over the same
carrier. They need no new protocol-specific structural constructor.

The scalar reference adapter captures the whole caller context to keep its
correspondence simple. Repeated control bindings can therefore have quadratic
operand counts despite linear structural node counts. Native import should
preserve the native capture interface and validate its order and types, rather
than copy the entire SSA environment. Any closure conversion needs its own
checked map. Dropping a declared capture is a separate transformation with
availability, ownership and execution obligations; unused does not imply
erasable. The generic carrier already supports smaller interfaces.

`Region.bind body next` composes a separately authored lexical subcomputation
without distributing `next` through its returning leaves. It shares the caller
context with `body`; it is distinct from an operation's closed callback interface.
Operation binding already retains the common suffix of a branch or fold once.
Keeping lexical binding avoids flattening separately authored computations during
composition, at the cost of one extra structural case in generic proofs. The
canonical evaluator and formation checker never expand continuations into
returning leaves. The unused expanding scalar composition helper has been removed.

## Semantics and proof reuse

`RegionMeaning.operation` receives evaluated operands and effectful semantic
callbacks. Its result is `Proc interface (Values Value results)`. A callback
accepts exactly its declared input tuple and returns its declared result tuple.
An operation controls which callbacks execute and how often. The structural
carrier makes no assumption that every body runs exactly once.

`Region.bind_congr`, `Region.operation_congr` and `Regions.cons_congr` lift
pointwise open-process equality through shared suffixes and nested regions.
`Region.denote_rename` connects typed capture renaming to environments.
`Region.exactRefinement` reuses the existing exact implementation contract. Execution
laws preserve actual successor state and ordered events when a body stops and
prevent the suffix from running. They quantify over external replies.

Effect translation needs an additional law. `RegionMeaning.Translation` specifies
a target operation and proves that it commutes with pointwise translation of all
callback processes. `Region.denote_translate` then lifts that law to every formed
program. A higher-order implementation can inspect callback process shape, so
this compatibility does not follow from the callback type. The scalar/control
adapter supplies a proved instance through `Interpretation.regionTranslation`.

Totality means the process equals an immediate `Proc.done`, without interactions
or a stop. `Region.Total` is a sufficient structural predicate over the same
carrier, backed by per-operation semantic contracts and total callbacks.
`Region.returns_of_total` proves the resulting property. Its uniform operation
premise is deliberately strong. A checked operation, such as dot with unequal
lengths, generally needs a theorem restricted to admitted inputs. `Region.letOp_return` substitutes a proved immediate operation result in any
suffix. `Region.bind_empty_return` permits removal of a zero-result subcomputation only
with an immediate-return proof at its input. A native memory effect annotation
does not establish this property. A native instruction budget or resource policy
can still distinguish executions that the unbounded mathematical meaning equates;
such a policy needs its own correspondence or observation relation.

## Ordered finite admission

`Source.Finite` supplies semantic helpers, not another program syntax or an SSA
domain value. Its existential `Domain` lives in `Type 1`; operation meanings
construct it from small typed operands and interpret it before returning values.
A future importer should select concrete domain descriptors rather than store
this universal semantic tree in a `RegionMeaning.Value`. A `Domain` retains checks
and otherwise unused admission. Strict zip admits both factors
before checking lengths. Product admits both factors even when the first list is
empty. The first failed admission determines the stop. An empty admitted loop
returns its seed; an empty rejected domain still stops.

`Finite.execute` invokes effectful callbacks in order. Its replacement laws retain
admission in front of a pure fold equation. `Finite.interpret_fold` and
`Finite.interpret_execute` preserve ordered execution under operation translation. The invariant-based law can restrict
callback totality to admitted elements and reachable states. A mathematical fold
equation alone does not justify deleting an admission or reordering failures.

## Reference profiles and existing consumers

`Source.Program` is retained as the single-result structured reference profile.
`Program.toRegion` lowers every reference term to the canonical carrier with
explicit captures. `Program.denote_toRegion` proves equality of the complete open
process with its scalar result wrapped as a singleton tuple. The maintained
AlgebraicRounds and complete Sumcheck verifier references expose canonical
`structuredProgram` forms and named denotation bridges.

`Mathematical.Block` remains the independent role-family reference model. Its
projection now directly creates canonical regions and preserves component
values, availability, locality, empty event lists and monadic execution. Optional
components remain explicit; absent values receive no invented default. Projection
partly resolves locality while constructing a term. Its equation pairs a projection
for a role with that role's input environment. The mathematical meaning itself
is role-independent: the projected restrictions already record the selection.

`Common.Program` remains the bounded global/participant reference and scalar
native-import consumer. `Common.Program.toRegion` lowers all six constructors to
the canonical carrier. Calculations become mathematical/restriction nodes and
lexical bindings; no whole calculation is hidden in an opaque operation.
`Common.Program.denote_toRegion` preserves its full process for every role and
input. `Native.Imported.toRegion` also retains the import carrier's final output
role restriction after execution, so an unavailable output does not skip actions
or stops. Deterministic and monadic execution equations follow from this bridge.
Fresh receive continuations, sender-side aliases, service ownership and existing
security contracts are preserved. The participant operation type and dialect
retain the selected role as a nominal parameter. A projection for one role
cannot use another role's meaning accidentally. This keeps the projected
representation and all operation meanings tied to one participant without adding
a wrapper around the generic carrier. It does not authenticate an external role
assignment; the importer still owns that admission.

These reference profiles carry different obligations and do not become a second
compiler SSA representation. They remain reference authoring/admission interfaces,
with proved conversions rather than an assumed correspondence. New structured
admission and transformation validation should use `Region`. Wider native import
is a separate package.

## Formation and trust boundary

`RegionDecoding` represents raw operation result annotations, callback signatures,
bind intermediates and reference indices. Formation checks exact types and
arities throughout the syntax, including callbacks a runtime operation may skip.
Universal `elaborate_erase` theorems cover every typed region and callback list.
The converse laws require successful formation to preserve all raw structure and
annotations exactly. Shared operand lookup lives in `ContextDecoding`. The unused
scalar raw grammar and its JSON codec have been removed; the bounded native
`Common` schema remains separate.
This checks Lean structural formation. Operation descriptors and their selected
meanings still need resolution at the external boundary.

The native scalar export schema and its existing readers stay in their current
bounded profile. This package supplies no general MLIR decoder, structured native
import correspondence, runtime/provider theorem or cryptographic reduction.

## Stress cases and follow-up work

The maintained examples cover two distinct complete effectful endpoint shapes:
a seeded finite factor-opening verifier and a guarded challenge-response
verifier. They use actual independent receive continuations, sends, zero-result
checks, multiple results and captured callbacks. Their open-process equations
include rejected prefixes. The arithmetic interpretation is illustrative; these
examples do not establish production protocol security. The standalone core
client also consumes generic contextual replacement and the imported-program
bridge through a real Lake path dependency.

| Next use | Foundation supplied here | Remaining obligation |
|---|---|---|
| Original-stage native import | Typed result/region signatures, explicit captures, strict formation | Native correspondence of preparation, projection and lowering; resource limits at the external boundary |
| Actual transformation validation | Contextual equality, shared binding, operation contracts, ordered finite admission | Relate actual source/candidate artifacts and prove each native transformation under its preconditions |
| Complete verifier consumers | Full open-process semantics and bridges for maintained verifier references | Protocol families beyond the maintained Schnorr and Sumcheck consumers |

Role projection and constructions remain separate obligations. Fiat–Shamir
changes interactions and needs stated interpretation/coupling/reduction laws;
plain process equality is not a general security theorem for constructions.

## Design constraints for the next packages

A prepared native importer must resolve each descriptor to an owned signature
and meaning, retain exact source/helper identity, and check result order and all
closed captures before producing a region. The current example fold uses
state, two items and captures. A native adapter must explicitly map the
[finite helper ABI](../../../docs/spec/ir/finite.md#helper-and-operand-abi), including
its index and domain arguments, and the distinct counted-control region ABI.
Matching informal names is insufficient. In particular, native n-ary zip admits
all children before comparing lengths. Nesting binary semantic zips can report an
earlier length mismatch instead of a later child admission failure; a negative
control retains that distinction. Binary zip uses `.refused` for a mismatch in
this model. An importer must account for the native diagnostic policy explicitly.
The structural decoder alone authenticates neither an artifact nor a resolver.

Import at the boundary whose correctness is being studied. Native preparation
already performs finite algorithm selection even when scalar simplification is
disabled. A prepared snapshot can support proofs about subsequent execution and
projection, but cannot validate an earlier selection without its retained source
and actual candidate. Native Local control already uses isolated bodies and
explicit captures; the adapter must check its specific argument/yield maps,
including unchanged loop captures and affine state roots, before normalizing them.

A transformation theorem should state its admitted inputs and chosen observation.
Exact process equality is reusable for transformations that preserve all actions;
it is intentionally too strong for changing a transcript or resource protocol.
It is also independent of static source contracts. Statement annotations have
no runtime effect, and an unused rejected mathematical definition can have the
same dynamic process as an admitted source without that definition. Transformation
validation must bind both actual artifacts, check the relevant static contracts,
and then establish the selected dynamic equation. `Region.Equivalent` establishes
only the last of those obligations.
Native frame entry/cleanup, affine services and instruction capacity can require
an execution relation over actual state and observations. Those policies must not
be silently erased by translating an abstract callback. Likewise, changing an
admission requires a proof about its stop behavior, even for unused values.
In particular, appending cleanup with `Proc.bind` skips it on a stop. Catching
syntactic halts still does not catch a stop produced by a handler. Native cleanup
and its failure precedence therefore belong to the execution adapter, rather
than an assumed meaning of lexical binding.

A complete imported verifier consumer can compose the canonical process equation
with an existing contract. It still needs actual relation, arithmetic, sampling,
provider and adversary assumptions. The preserved reference security results are
not a security theorem for every future operation vocabulary or native runtime.

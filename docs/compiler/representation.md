# Compiler representation

This chapter explains representation choices and the bounded examples that
discriminate them. The [protocol pipeline](protocol-pipeline.md) owns the current
end-to-end architecture. The direct table and logical query examples below
exercise individual obligations; they are not the full native protocol route.

The [table and storage contract](table-storage/README.md) and the
[formal handoff](../../formal/design/implementation-handoff.md) are the starting
requirements. [Component instantiation](components.md) selects static dependency
specialization and shared definitions, [logical calls](calls.md) complete
returned and stopped behavior and a possible successor representation, [selective lowering](lowering.md) local expansion,
original-source admission and evidence invalidation, and the
[target design](targets.md) with the
[admission responsibilities](calls.md#6-integrated-admission-responsibilities)
the production boundaries.

## 1. Architecture and semantic connections

```text
protocol contract + original statement + selected interaction construction
              | admission of supplied participant algorithms
              v
typed protocol algorithms with logical objects and explicit local inputs
              | local/algorithmic transformations with stated relations
              v
selected kernels, storage and ordered execution plan
              | value/state/codec correspondence
              v
owned native execution
```

Construction selection is an additional axis: Fresh and a particular framed
interpretation can use the same arithmetic child. Protocol admission relates
an algorithm to a contract; it is not merely an earlier-to-later IR conversion.
The common interactive carrier supports participant generation for its admitted
grammar. Supplied participants enter through their own admission boundary. This
does not provide a total projector for arbitrary choreographies; unsupported
choices and communication structures require additional rules.

`PIR.Proc` supplies common execution meaning. It does not prescribe a mutable
compiler graph. A domain operation may have a structured expansion with a proved
interpretation, while remaining an operation until a pass needs that expansion.
Introducing a new interpreted primitive and expanding an existing operation into
visible code are separate extension mechanisms.

| Representation | Information retained | Work made possible | Condition for removal or lowering |
|---|---|---|---|
| Protocol contract and construction | Statement, roles, message/check/challenge sites, construction instance and property premises | Interaction admission, original-statement binding, construction-specific checking | Explicit admitted endpoint and applicable construction relation; retain its artifact binding |
| Participant algorithm | Role-local inputs, ordered captures, public loops/branches, complete call outcomes | Specialization, local substitution, legal placement and composition | Actual source export and value/control interpretation |
| Logical objects | Original tables, ordered prefixes/axes, product occurrences, degree and structured queries | Restriction fusion, shared preparation, query transport, algebraic algorithm selection | Selected implementation of the same object/query; preserve all pending terminal obligations |
| Arithmetic child | Resolved field/module laws and ordered operands | Ring rewrites, local CSE, structured linear kernels | Mathematical-to-machine representation and range/encoding obligations |
| Execution plan | Kernel selection, materialization, storage, provider calls, guards and exits | Capacity planning and execution or later code generation | Complete native value/state/observation correspondence |

Several rows can coexist in a module. There is no fixed requirement for one
dialect per row. The implemented families include PIR, Algebra, Polynomial,
PCS, Oracle, Relation, Claim and Plan; define libraries around operation contracts
and their consumers. A protocol
library composes those operations and contracts rather than changing generic
binding, control or analysis for each protocol.

## 2. Concrete representation choices

Use typed operations and explicit operands for semantic dependencies. Properties
or attributes hold resolved immutable descriptors, not mutable execution state.

| Fact | Selected home | Why |
|---|---|---|
| Field, scalar-action field, digest suite | Resolved domain descriptor referenced by types/operations | A modulus alone cannot describe extension fields, basis or group scalar actions |
| Public specialized original dimension | Table/view type parameter in the first profile | The original rank remains stable through a prefix-growing loop |
| Actual ordered challenge prefix | Logical view value | Fixing a coordinate changes the value, not the loop accumulator type |
| Original table and ordered factors | Explicit SSA operands and source binding | Labels, equal shapes and optimizer metadata cannot establish provenance |
| Product degree/multiplicity | Interpreted expression structure plus checked/derived facts | A product of extensions differs from an extension of pointwise products |
| Ready/prepared/current facts | Analysis result tied to interpreted transfers and source positions | Runtime writes and failed outcomes can invalidate a fact without changing its type |
| Protocol/construction requirement | Retained resolved contract and source-relative evidence | A freely editable attribute or operation name does not prove admission |
| Physical buffer/session/generation | Plan value and runtime ownership | Native handles do not replace the logical object's meaning |

The initial native profile uses public specialization and the adopted F2/F7
table contract. The type/domain resolver must admit independent additional
profiles without a global modulus or a Sumcheck-specific switch in generic
control. The F4 query experiment tests a third descriptor; it does not implement
a binary-tower runtime. Canonical F4 representation codes are basis coordinates,
not natural-number casts into characteristic two.

Protocol containers and algorithm regions retain useful structure. A region
captures values explicitly and yields ordered results. It may group a round or
terminal calculation, but a label such as `round` is not a phase certificate.
An isolated straight-line region is one possible grouping. The registered
local-control operations and protocol loops have their own formation and
execution rules; a grouping label is not a new semantic constructor.

Keep logical stopping distinct from formation. For example, a well-typed table
evaluation with the wrong residual/point arity is a computation that refuses.
Its source cannot silently become an unconditionally pure operation or a
compile-time input error. The initial native implementation needs explicit
returned/stopped control and a path-sensitive flow verifier. Straight-line
single-use checking in the experiment does not establish that CFG invariant.

## 3. Protocol walkthroughs

### Sumcheck

The main representation must retain the original polynomial expression and
statement while prover rounds send messages and the verifier checks and draws.
The original expression may include repeated table factors. A residual scalar
and point carry an outstanding terminal obligation until its actual consumer.
Private prover tables do not become verifier inputs through compilation.

The finite logical example is a closed one-variable shared-table trace: evaluate the original table at zero and one, send endpoints, check their
sum, draw, interpolate the message, evaluate the original at the delivered point
and compare. Its input policy deliberately makes the table available to this
joint trace. The registered MLIR example retains that structure and original
table operand. An affine child lowers to `a + r*(b-a)` while the protocol,
construction and ordered calls remain.

The wider degree-two/multivariate argument requires actual prover and verifier
programs, a challenger and their terminal join. The maintained
`Sumcheck.Source`, `TableSource`, `Endpoints.Composition` and `Security` provide
its mathematical basis. The [interactive execution route](interactive-execution.md) supplies native
protocol consumers separately. This logical example neither establishes that
entire route nor proves Fresh or Fiat–Shamir security from a construction label.

### Execution-plan trace

For that same direct one-variable source, the initial physical plan binds an
immutable original table, holds a logical view as `(original handle, prefix)`,
and dispatches these contracted operations in order:

```text
entry(original, claim, provider):
  view := original with empty prefix
  a := invoke evaluate(view, [0]); on stop, finish with that outcome
  b := invoke evaluate(view, [1]); on stop, finish with that outcome
  invoke send(a, b); on stop, finish with that outcome
  if a + b != claim: finish rejected
  r := invoke draw(provider); on stop, finish with that outcome
  updated := invoke affine(a, b, r)
  actual := invoke evaluate(view, [r]); on stop, finish with that outcome
  finish returned(actual == updated)
```

This example is scheduling notation, not the syntax of the implemented `plan`
dialect or a frozen codec.
The Lean direct-plan instance supplies its logical reference. Public
input admission and native reservation occur before entry. Every completed stop
keeps the actual state/event prefix, and the final comparison returns a Boolean
without silently introducing another rejection. The provider's residual tape
belongs to the same session. The view's storage remains alive until its last use.

The first direct artifact retains the original operation descriptors and uses
their contracted kernels. The experiment's expanded affine child changes those
operations: it cannot be serialized as a direct-v1 candidate and accepted merely
because its algebra is correct. That actual changed candidate needs an admitted
expansion/rewrite rule and consumer, or a separately bound generated-kernel
realization with its own correspondence. Until that join exists, the direct path
uses the unexpanded operation. This keeps selective-lowering feasibility separate
from source-relative artifact acceptance.

### Ordered Merkle work

The Merkle example contains two logical opening occurrences at the same
position, ordered parent compression and explicit consistency checks. The local
calculation may share equal pure compression work. Both logical openings and
their checks must remain: the second supplied opening can contradict the first.

An actual cryptographic suite and opening decoder remain separate contracts.
The example uses the `ordered-pair` mathematical digest suite, matching the
contrasting table client. It makes no binding or collision-resistance claim.
Replacing the two wire openings with a multiproof is a separate representation
transformation with an adversarial decoding/consistency relation.

### Binius-style original-root query

The linear-query example uses a root, a field-valued claim and a query
descriptor. The verifier region has no witness table. A zero-filled right shift
induces a query pullback on the original root: for a two-cell table, `(w0,w1)`
becomes `(w1,0)`.

The identity is a specialization of `dot(w,Mv) = dot(M^T w,v)` from the checked
expressiveness experiment. Root and query remain explicit opening operands.
The example pressures the carrier for a general linear form; it is not a full
Binius verifier, PCS implementation or claim-batching security proof. Dense
weights are a finite reference. Production queries may retain sparse, tensor,
factored or composed structure if their original-object interpretation is fixed.

## 4. Alternatives and their discriminating cases

| Choice | Decision | Evidence needed before the dependent production API |
|---|---|---|
| One opaque call for a complete protocol | Keep only for external integration; it cannot establish the compiler's own optimization claim | Compiler-authored protocol bodies expose rounds, queries and terminal uses |
| Immediate lowering to field operations | Use within selected children after logical consumers | A protocol/view/query survives local arithmetic conversion |
| A separate dialect for every protocol | Prefer shared domain operations and supplied protocol libraries | Two distinct clients use the same operations or semantic interfaces |
| Put all facts in dependent types | Use stable sorts plus operands and checked analyses; add useful local type refinements later | Prefix-growing loops retain a type; misuse is still rejected or refuses at its specified boundary |
| Custom storage everywhere versus upstream tensor/buffer lowering | Keep logical handles initially; compare appropriate physical kernels at materialization | Original-value/alias relation, failure behavior and measured copy/allocation costs |
| Whole compiler in Rust versus split analyses | Keep one C++/MLIR engine and whole-job Rust execution boundary | Runtime consumes a finished plan without reproducing compiler decisions |

The first production interfaces are semantic export, resolved domains and
signatures, complete operation outcomes/effects, and exact source binding.
Demand/preparation interfaces enter with their first two real consumers.
Kernel, codec and provider APIs are separate from the beginning; a substituted
test adapter must work through the same runtime dispatcher.

Admit the original source and its complete declaration/dependency environment
before optimizing, including dormant bodies. Final legality alone cannot
establish this: canonicalization may already have erased an unsupported body.
Source admission and checking the actual final plan are separate boundaries.

For each material decision, record the competing choices, the discriminating
case, the result and the affected API. Investigate uncertainty at that boundary.
A counterexample can reopen a semantic law; a poor layout can reopen the storage
choice without reopening unrelated proofs. Keep the direct valid implementation
as a fallback when an optimization's premises or benefit cannot be established.

## 5. Native evidence

Native correspondence uses differential testing against executable Lean as
the default evidence. A shared schema does not prove decoder equivalence.
Compare complete outcomes, selected observations, live values and residual
states, with independent input generation, failure controls and replay. Optional
native proofs strengthen individual adapters later.

The [delivered direct table slice](table-execution.md) implements canonical
numeric parsing (`-0` versus negative nonzero values), all declared captures
including dormant bodies, two domains, prefix-growing loops, failed writes,
stopped suffixes, stale and foreign handles, substituted field kernels and
providers, and ownership after start failure. Two immutable storage layouts run
through that same adapter and complete Lean comparisons. This closes storage
substitution at the finite profile, not physical plan selection, materialization,
public specialization or general endpoint admission.

The [compact region](regions.md) implements one shared suffix across actual
MLIR, source-relative checking and native execution, which closes the repeated
branch tree growth case. It does not close general CFG structure, generic region
analyses, physical control lowering or optimization admission.

## 6. Theory at the relevant boundary

Intrinsic typing and substitution govern explicit captures. Algebraic effects
and complete execution relations govern calls and stops. Abstract interpretation
and outcome-sensitive frame laws govern preparation facts. Data refinement and
ownership govern views, aliases and buffers. Linear-map duality and degree-aware
polynomial meaning govern query transport. Translation validation binds the
actual transformed object; differential testing supplies bounded native evidence.

MLIR mechanisms are implementation aids for those obligations:
[ODS](https://mlir.llvm.org/docs/DefiningDialects/Operations/) generates typed
signatures and structural verifiers;
[effects and speculation](https://mlir.llvm.org/docs/Rationale/SideEffectsAndSpeculation/)
control generic motion/deletion;
[dialect conversion](https://mlir.llvm.org/docs/DialectConversion/) permits mixed
representations and checks declared legality. None establishes protocol
admission or cryptographic lawfulness by itself. Check APIs against the actual
pinned installation, not only current upstream documentation.

Before physical lowering, compare the applicable
[bufferization](https://mlir.llvm.org/docs/Bufferization/) interfaces against
zkc's alias and failure contract. A compiled sketch that keeps opaque handles
does not settle that engineering question. Correlation-aware reuse, general
linear-query compilation, changed multiproofs, stronger FS security and complete
zkVM relation-to-PCS composition remain concrete research questions.

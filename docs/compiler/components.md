# Component definitions, instances and connections

Reusable algorithm definitions stay separate from their selected semantic
environments and runtime invocations. Code is specialized by its actual static
dependencies; runtime values and state are passed explicitly. Component outputs
are preserved until their connected consumers have used them. These choices
refine the [representation design](representation.md) and add no new semantic
layer.

Sharing one specialization for equal static dependencies prevents repeated
call sites from cloning the entire dependency graph. This is a code-size
property; it does not by itself imply faster execution.

## 1. Four different objects

| Object | Meaning and carrier | What it does not establish |
|---|---|---|
| Contract | Resolved relation/operation definition, domain parameters, boundary types and required properties; immutable descriptors referenced from IR | A contract declaration does not provide an algorithm or discharge its hypotheses |
| Algorithm definition | Reusable, inspectable typed body with explicit parameters, logical operations, structured control and ordered calls | A body name does not select one construction for all its callers |
| Selected instance | Definition plus actual immutable construction, domain, contract and target bindings; retained in the compilation environment and entry/call references | Equal generated code does not identify source statements, evidence or runtime sessions |
| Invocation | Actual input/capture operands, runtime resources, returned or stopped outcome and exposed outputs | A successful call does not automatically prove its residual relation |

Use MLIR symbols for reusable definitions and immutable environment references;
use SSA values for invocation data. The initial closed compilation admits an
acyclic static call graph and explicitly bounded repetition. Dynamic closures,
recursive calls and loading unknown definitions at runtime require additional
profiles. An acyclic call graph is not a restriction to acyclic protocols: a
bounded round loop belongs inside a definition.

The native route uses `func.func` for local algorithms, `pir.protocol` for common
interaction and `pir.participant` after projection. Their respective local,
protocol and participant calls retain the boundaries described by the
[protocol pipeline](protocol-pipeline.md). The
[logical-call discussion](calls.md) compares a possible explicit-successor CFG
representation; it is not an additional installed call dialect.

An entry wrapper can associate a reusable body with a resolved environment.
Immutable captures still enter through explicit ordered arguments unless
specialization deliberately embeds their values. They are not free SSA captures
from a module-level symbol declaration. Role-local inputs and original statement
data remain separate from provider selection.

## 2. Binding and code sharing

Consider one supplied round body with an abstract challenge operation. Two
callers select different implementations of that operation:

```text
definition round(state, message, original_subject, inputs)
  logical challenge operation + arithmetic child + returned/stopped outcome

instance interactive_round = round under interactive_environment
instance framed_round      = round under framed_environment

call interactive_round(actual_state, message, original_subject, inputs)
call framed_round(other_state, other_message, other_subject, other_inputs)
```

This is dependency notation, not frozen MLIR assembly. A complete environment
can bind several operations and types. A construction may expand one abstract
operation into an inspectable body; a concrete provider may implement a remaining
primitive. Those are separate bindings even if a small illustrative model represents
both by one callback slot.

For a closed compilation, choose demand-driven specialization of definitions
that depend on the selected static environment. Reuse one generated body for
equal specialization keys. Keep helpers independent of that environment shared.
Do not inline the whole component graph merely to resolve a construction.
Specialization resolves dependencies; selective inlining remains a separate
profitability decision.

The production key needs the referenced definition/version, operand/result
domains, relevant construction/operation/codec contracts, any embedded constants
and selected target profile. A sound dependency analysis may omit irrelevant
entries. Unknown dependencies prevent that reduction. For a single-slot, uniform-type model in one immutable module, a key of
`(resolved definition, resolved provider)` can suffice. It is not sufficient for
the general dependency set above. An operation pointer
is not a persistent artifact identity, and a spelling such as `fresh` is not a
complete semantic key.

Share code without combining runtime invocations. Residual provider/transcript
state, immutable input handles, session identity and preparation storage remain
actual arguments/resources under their contracts. Reusing compiled code does
not reuse a sample or authorize a preparation-cache hit. Code equivalence also
does not allow deduplicating source-bound evidence for distinct statements.

Evidence quantified over runtime inputs can be reused for distinct statements
within that domain. This requires no per-statement recompilation: the actual
ordered operands and invocation binding select the instance. By contrast,
embedded constants and assumptions specialized to one original must remain in
the evidence subject. Code dependencies, evidence dependencies and physical
ownership are separate keys even when they share a resolver implementation.

| Alternative | Assessment |
|---|---|
| Mutate a shared definition to select its provider | Reject: other callers can acquire the wrong construction |
| Clone at every call occurrence | Valid bounded baseline when binding is correct, but needlessly expands shared dependency graphs |
| Specialize by resolved static dependencies | Selected for the first closed profile; retains static calls and shares equal instances |
| Pass a runtime dictionary of operations | Useful future option for runtime-selected services; requires a supported calling convention, admitted dictionary and effects/contracts. No performance comparison is implied |
| Compile every protocol as an opaque external call | Useful as an optional backend boundary; insufficient as the sole optimization carrier |

## 3. Connections retain actual boundaries

Algorithm composition and logical relation composition are different operations.
A call graph connects computations. The
[component relation](../spec/properties/relations.md#component-connections)
additionally constrains the actual boundary values exposed by those computations.
Represent a connection through explicit operands and the selected predicate or
verification consumer; no universal claim-graph dialect is required by this law.

For example, a component may expose `(key, commitment)` and another expose
`(key, message)`. Their connection compares the actual keys while retaining each
component's other statement arguments. They need not use the same tuple layout.
Two independently inhabited relation instances do not establish a shared key.
Likewise, a Sumcheck reduction's scalar and point remain pending inputs to an
opening/terminal consumer. Dropping those outputs because the producing function
returned successfully would change the proposition being checked.

The [representation laws](../spec/properties/relations.md#changing-boundary-representations)
allow different layouts with explicit coverage and connector compatibility.
They do not choose a native encoder. A contextual check-elimination pass must
record which surviving component establishes its premise. Both sides cannot
remove the same check by relying on the other's old body. Executable stopping
and observations require their own preservation relation in addition to the
connected proposition.

The native contract/call design must represent these obligations without
treating arbitrary attributes as proofs. A retained source selects the actual
library meanings; an independent checker resolves the supported definitions.
Static type agreement, symbol resolution and call graph formation are necessary
structural checks; they are not source-relative semantic validation.

## 4. What remains visible during lowering

| Boundary | Retain | Permitted local work |
|---|---|---|
| Reusable definition to selected instance | Body identity, explicit inputs/captures, selected environment, output relation and caller requirements | Substitute bindings; share equal code; expand an independent pure helper |
| Logical operation to selected body/kernel | Original object, ordered factors/coordinates, actual provider state and observations | Use a proved/checked expansion; lower only the selected arithmetic child |
| Connected algorithm to physical plan | Exposed residuals, role ownership, state dependencies, complete stop and resource behavior | Select storage/kernels and schedules under their contracts |
| Common source to native or acceptance target | Original statement, actual output, admitted input mapping and every remaining consumer | Target-specific representation with coverage/adequacy evidence |

Construction selection and arithmetic lowering are different axes. The
[interpretation laws](../spec/core/interpretations.md#sequencing-and-changing-construction-order)
justify sequencing through the actual residual state. They do not authorize
resetting a transcript or exchanging constructions. A helper expansion can
commute with binding when it is independent of that binding and preserves the
required observations. General effectful expansion needs the operation-level
law; independent helper expansion cannot establish it.

Generic CSE may optimize supported pure arithmetic. Provider attempts remain
ordered calls, including failed attempts. Equal argument tuples are not evidence
that an effectful call can be reused. Once inlining moves a body, its operand
mapping, role context, scoped contracts and observations must move correctly;
source locations alone are not a retained semantic binding.

## 5. Theory and reference clients

| Required reasoning | Existing basis | Use here and remaining bridge |
|---|---|---|
| Substitution and interpretation | [Core interpretation](../../formal/Zkc/Semantics/Interpretation.lean), execution fusion and binding laws | Explain specialization and separate expansion; actual native substitution/export adequacy is still required |
| Connected relations and contextual replacement | [RelationComposition](../../formal/Zkc/Semantics/RelationComposition.lean), [contrasting connections](../../formal/Examples/ComponentConnections.lean) | Retain open boundaries, representation coverage and a non-circular premise producer; native claim checking has a separate bounded scope; no universal composition theorem |
| Input coverage and observable behavior | [Refinement](../spec/verification/refinement.md), input binding and retained-consumer contracts | Include actual inputs, results, post-state and selected events in validation; equal return values are insufficient |
| Preparation and dependency analysis | [Preparation](../../formal/Zkc/Semantics/Preparation.lean), sound observation summaries | Separate static code dependency, immutable value reuse and stateful calls; code specialization alone does not establish runtime reuse |
| Local information and supplied endpoints | [Interaction](../spec/language/interaction.md), supplied endpoint correspondence | Keep caller-visible captures explicit; ordinary functions do not establish communication realizability |

These references constrain the design; they are not a proof of the native compiler.
The production connection still follows the adopted Lean–MLIR/Rust differential
testing policy, with stronger proofs where useful.

The following maintained clients supply contrasting semantic obligations:

- [Sumcheck connection](../../formal/Zkc/Protocols/Sumcheck/Connection.lean)
  and [framed interpretation](../../formal/Zkc/Protocols/Sumcheck/Framed.lean):
  preserve the original polynomial, scalar/point outputs and actual challenge
  construction. A fresh-tape acceptance instance cannot certify a framed target.
- [Opening reduction](../../formal/Examples/OpeningReduction/README.md): retain
  ordered factor obligations and their actual consumer. Sharing table storage
  cannot replace a virtual product by its Boolean value table.
- [Correlated service](../../formal/Zkc/Protocols/CorrelatedSetup/Source.lean)
  and [commitment sessions](../../formal/Zkc/Protocols/CommitmentSessions/Source.lean):
  share appropriate pure work while preserving each external response and
  session transition. Distinct runtime sessions may use the same generated code.
- [Non-machine connections](../../formal/Examples/ComponentConnections.lean):
  connect differing proof/signature boundaries through the actual common key.
  No machine trace, global clock or single transcript is required by the carrier.

These are semantic clients and design obligations. Native coverage is stated
separately in [status](../status.md).

## 6. MLIR mechanisms and engineering scope

Use the upstream [symbol table](https://mlir.llvm.org/docs/SymbolsAndSymbolTables/)
APIs for lookup, insertion and symbol-use rewriting. Resolve actual definitions
before sharing. Nested symbol tables
need explicit scope handling; they do not implicitly search enclosing tables.
Definition renaming must update references, while stable semantic identity stays
independent of generated symbol spelling.

Use [operation interfaces](https://mlir.llvm.org/docs/Interfaces/) for callable
bodies, calls, controlled inlining and effects. Protocol-specific semantic
contracts remain additional obligations. [Dialect conversion](https://mlir.llvm.org/docs/DialectConversion/)
provides selective legality and type conversion; legality alone is not a theorem
that the selected protocol observation is preserved.

Run environment resolution and instance creation at their owning symbol table.
Keep local analyses on bodies under immutable resolved environments. MLIR's
[pass infrastructure](https://mlir.llvm.org/docs/PassManagement/) supplies scoped
passes and analysis invalidation; a caller-sensitive analysis still needs its
actual environment among its dependencies. All of this stays in C++/MLIR.
Rust receives completed artifacts and execution contracts, not round trips for
individual call-graph queries or rewrites.

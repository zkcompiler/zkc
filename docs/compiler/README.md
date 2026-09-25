# Compiler structure and correctness

The [refinement specification](../spec/verification/refinement.md) owns execution
models, correctness and checked transformations. [Analysis](../spec/verification/analysis.md) and
[evidence judgments](../spec/verification/judgments.md) own applicability,
conditional evidence and caller requirements.
[Module contracts](../spec/profiles/compiler/factor-preparation.md) own fact/availability transfer and
preparation laws. This guide connects those meanings to compiler choices, and
the pages below own the parts of the compiler.

Start with the [protocol pipeline](protocol-pipeline.md). It connects retained
source, construction, participant algorithms and physical execution. The
[language guide](../language/README.md) owns authoring; the
[runtime guide](../runtime/README.md) owns execution and backend use.

## Implementation reference

| Boundary | Pages |
|---|---|
| Source analysis and elaboration | [Frontend](frontend.md), [elaboration rules](elaboration.md), [common source model](source-model.md) |
| Static and semantic selection | [Specialization](specialization.md), [independent generic validation](library-design/validation.md), [components](components.md) |
| Shared compiler contracts | [Operation contracts](operation-contracts.md), [protocol library extension](protocol-libraries.md), [closed reference libraries](libraries.md) |
| Interaction and local computation | [Logical calls](calls.md), [local composition](local-composition.md), [local control](local-control.md), [compact regions](regions.md) |
| Construction and generation | [Interactive carrier](carrier-consolidation.md), [participant execution boundary](interactive-execution.md), [artifact construction](artifact-execution.md) and [format](artifact-format.md) |
| Relation and claim consumers | [Relation ingress](relation-ingress.md), [claim composition](claim-composition.md), [targets](targets.md) |
| Transformation and admission | [Selective lowering](lowering.md), [phase admission](phase-admission.md), [implementation design](design.md), [representation decisions](representation.md) |

## Finite reference implementations

The [finite source/direct-plan format](source-plan.md),
[table execution](table-execution.md) and [table/storage contract](table-storage/README.md)
have independently useful checkers and proof consumers. Their
[operations](table-storage/source.md), [storage](table-storage/storage.md) and
[protocol traces](table-storage/protocols.md) describe this bounded route. It is
not the mandatory lowering path for the interactive native carrier.

## 1. Structured PIR and lowering

A useful optimization carrier retains typed values, structured branches and
public loops, explicit region inputs/results, logical domain operations and
contracted effects. Natural indices and field elements must remain distinct;
ordered captures, factor occurrences and challenge prefixes need their source
meaning until justified erasure. [Program clauses](../spec/language/programs.md) and
[domain values](../spec/domains/values.md) and
[polynomial meaning](../spec/domains/polynomials.md) define these obligations.

The reference direct plan supplies a proved small evaluator. It is not a
mandatory second IR for every compiler. Structured SSA, shared regions and
native calls are possible implementation choices under the same semantic
judgment. The [implemented pipeline](protocol-pipeline.md) selects concrete carriers;
Lean layouts do not mandate their mutable representation.

## 2. Three transformation classes

[TR-01](../spec/verification/refinement.md#preservation-subjects)
distinguishes local execution refinement, representation refinement and
protocol/property transport. A pass may require more than one. Faster pairing
arithmetic and KZG aggregation with changed challenge order have different
proof obligations even if one compiler proposes both.

[TR-03](../spec/verification/refinement.md#checking-the-actual-candidate) requires
checking the actual source and candidate. Before source distinctions disappear,
[TR-06](../spec/verification/refinement.md#effects-and-admission-timing)
requires retained meaning, checked establishment, lawful erasure or refusal.

## 3. The selected passes

The [factor rule](../../formal/Zkc/Compiler/FactorOptimization.lean) infers
reuse from facts produced by actual source calls, invalidates them by the
actual outcome and preserves readiness guards. Its reference rewrite keeps
loops direct and may duplicate differing continuations. A shared representation
and sound joins can improve that implementation without changing the judgment.

The [preparation join](../../formal/Zkc/Polynomial/Bilinear/Compilation.lean)
combines current facts, installation and immutable cache validity for one
caller, including actual readiness refusal. The
[communication client](../../formal/Zkc/Protocols/CorrelatedSetup/Communication.lean)
and [session client](../../formal/Zkc/Protocols/CommitmentSessions/Source.lean)
exercise the same separation of meaning, state and observation in nontrivial
communication flows. These do not imply universal protocol compilation.

## 4. Analysis, checking and selection

[TR-07](../spec/verification/analysis.md#meaning-and-transfer)
allows conservative analyses and heuristic proposal algorithms. The selected
candidate still needs source-relative evidence. The maintained checker is a
model-specific rule interface; a finite certificate format and native resolver
are further concrete profiles.

[Conditional judgments](../guides/security-properties.md#judgments-premises-and-use) preserve actual premises.
Structural MLIR verification establishes its implemented structural invariants.
[Phase admission](phase-admission.md) adds a distinct checked obligation.
Neither alone establishes domain rewrites or native backend correctness.

## 5. Costs and engineering value

[MOD-10](../spec/profiles/compiler/factor-preparation.md#immutable-preparation-and-prices) states
the exact preparation accounting. The two-use control has direct work eight,
memoized work four and overhead three under its declared prices. That is a
mathematical example, not a native measurement.

The engineering goal is reusable discovery, applicability checking and
composition across source changes. An equally capable manually supplied
library is a valid baseline and consumer. Runtime, verification/compile time,
memory and emitted bytes need distinct measurements; current equality laws
do not show generated code always outperforms such a library.

## 6. Theory and implementation entry

[Implementation maintenance](../development/extensions.md) describes the installed
pass factories, shared pipeline builders and native extension points.

A transformation is accepted by
[checking its candidate](../rationale/candidate-checking.md), not by proving the
optimizer. The [architecture](../architecture.md) and [roadmap](../roadmap.md)
connect these laws to the implementation. The mathematical pass library is evidence for those selected laws,
not a completed native protocol compiler.

[Compiled relations](../language/relations.md) connect imported relation data to
ordinary authored algorithms; [relation ingress](relation-ingress.md) owns the
compiler-side admission and lowering contracts.

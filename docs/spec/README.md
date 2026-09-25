# Selected-model specification

This specification defines the finite atomic model selected by
[docs](../README.md): its mathematical objects, admitted programs,
complete executions, checking judgments, property claims and realization
requirements, with explicit outer iteration over finite bodies. It does not prescribe an IR hierarchy or a physical runtime.
Start with [conventions](conventions.md) for notation, execution scope and
conformance claims.

## Adopted scope

The seven parts below own the selected definitions. A common chapter defines
parameters and laws; a profile fixes a particular vocabulary, algorithm,
representation or experiment. A profile's restrictions apply within that
profile rather than to the whole language.

### 1. Core semantics

| Chapter | Definition scope |
|---|---|
| [Execution](core/execution.md) | Signatures, bodies, complete outcomes, sequencing, bounds and retained histories |
| [Iteration](core/iteration.md) | Pending prefixes, termination, deployment caps and publication |
| [Observations](core/observations.md) | Event projections, equal-result relations and justified observers |
| [Operation interpretations](core/interpretations.md) | Expansion, composition, execution fusion and admission transport |
| [Contracts](core/contracts.md) | Complete-result satisfaction, sequencing and immutable cache validity |

### 2. Language and admission

| Chapter | Definition scope |
|---|---|
| [Typed programs](language/programs.md) | Ordered heterogeneous contexts, control, denotation and structural bounds |
| [Inputs and captures](language/inputs.md) | Capture lifetime and source selection; concrete input binding is defined by the source profiles |
| [Interaction and endpoints](language/interaction.md) | Public subjects, all-reply conformance, return phases and semantic admission |

### 3. Domain objects

| Chapter | Definition scope |
|---|---|
| [Values and domains](domains/values.md) | Interpreted sorts, actual shapes, conversions and adequacy |
| [Vectors and linear combinations](domains/vectors.md) | Ordered shapes, scalar/group contractions, linear maps and representation obligations |
| [Tables and polynomials](domains/polynomials.md) | Ordered cells, extension, factor occurrences, residuals and contraction |
| [Constraint relations](domains/constraints.md) | Sparse rank-one views, public/ONE binding, finite AIR windows, read locality and degree |
| [Authenticated tables](domains/oracles.md) | Vector commitments, private opening custody, exact queries and source ordering policies |

### 4. Transformations and checking

| Chapter | Definition scope |
|---|---|
| [Refinement](verification/refinement.md) | Actual execution models, initial domains, transformation rules and candidate binding |
| [Analysis](verification/analysis.md) | Sound sufficient facts, transfer, conservative merging and applicability |
| [Evidence and use](verification/judgments.md) | Conditional claims, discharge, logical results, failure boundaries and cost |

### 5. Experiments and properties

| Chapter | Definition scope |
|---|---|
| [Probability](properties/probability.md) | Normalized execution, joint initialization, reached masses and complete updates |
| [Experiments](properties/experiments.md) | Actual operands, strategies, property quantifiers and transport |
| [Relations and terminals](properties/relations.md) | Statement validity, heterogeneous component connections, contextual replacement, bound reductions and actual terminal consumption |
| [Disclosure](properties/disclosure.md) | Allowed worlds, joint release, couplings and permitted observations |

### 6. Realization and artifacts

| Chapter | Definition scope |
|---|---|
| [Representations](realization/representations.md) | Values in actual post-states, complete-result relations, acceptance/output adequacy and native obligations |
| [External construction transitions](realization/external-constructions.md) | Explicit Monero hash-chain and OpenVM duplex data states, call boundaries and primitive trust |
| [Codecs](realization/codecs.md) | Accepted input languages, decoding laws, receive effects and capacities |
| [Artifacts](realization/artifacts.md) | Consumer-retained subjects, specialization dependencies, interpretation closure, identity and custody |

### 7. Selected profiles

The [profile inventory](profiles/README.md) defines profile parameters and
locates contrasting reference clients at their actual scope.

The inventory is the complete list. Its groups are source formation and input
binding; compiler plans and local control; concrete realization; providers;
Sumcheck components; and stateful services. Each entry states the scope of the
selected definition rather than implying support across all implementations.

## Reading routes

Read conventions and complete execution first, then follow the relevant route:

| Reader | Route |
|---|---|
| Frontend author | Language and inputs → interaction admission → domain objects → selected source profile |
| Compiler/checker author | Programs and contracts → representations → refinement, analysis and judgments → selected rule/profile |
| Protocol author | Interaction and actual inputs → domains → probability, experiments and relations → protocol and terminal profile |
| Runtime/codec author | Execution and contracts → representations, codecs and artifacts → concrete format and custody |

These routes are dependencies for understanding claims, not compiler passes.
For example, an exact plan transformation still needs source adequacy, and a
protocol bound still needs its actual experiment and terminal observer.

## Reading and conformance rules

Definitions and rules are normative within their stated parameters and
premises. Examples are informative. [Conformance](conventions.md#conformance-claims)
identifies the actual frontend, checker, experiment or realization and its
covered domain; it does not combine all assurance questions into one Boolean.

Architecture explains responsibilities, design documents select realizations,
and decisions explain choices. [Status](../status.md) and
[assurance](../assurance.md) report achieved evidence. Those documents use this
specification's definitions. Each definition has one current home, reached through the chapter or profile
index. Correspondence maps and in-page Formal references identify selected
definitions, theorems and remaining obligations.

## Relationship with Formal and public documentation

Root [Formal](../../formal/README.md) supplies mathematical definitions and
kernel-checked propositions. The six correspondence maps identify actual
[core](correspondence/core.md),
[program](correspondence/programs.md),
[domain](correspondence/domains.md),
[transformation](correspondence/transformations.md),
[property](correspondence/properties.md) and
[realization](correspondence/realization.md) declarations,
hypotheses and limits. A parameterized obligation is not automatically a
mechanized theorem or an implementation guarantee.

A disagreement is adjudicated against the intended subject, its mathematics and
actual evidence. Neither an implementation's convenience nor a theorem about
a different object decides the intended semantics. The
[writing rules](writing.md) give the editorial rules. The
[profile grouping rationale](../rationale/profile-grouping.md)
explains the grouped profile structure. The optimized artifact and bounded
rewrite are engineering obligations until their exact profiles and proofs are
implemented; they are not additional definitions adopted by this index.

This specification and its Formal correspondence do not establish native
protocol support; the [status page](../status.md) states what is implemented.

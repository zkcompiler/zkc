# Binding, identities and artifact lifecycle

The [binding specification](../../../docs/spec/realization/artifacts.md) owns identity and artifact
contracts. This guide explains their use with
[endpoint admission](../spec/language/interaction.md#endpoint-admission),
[inputs](../spec/language/inputs.md) and [realization](../../../docs/spec/realization/representations.md).
Each purpose of identity has [its own relation](../../../docs/rationale/identity-purposes.md).

## 1. The common admission boundary

[INT-05](../spec/language/interaction.md#endpoint-admission)
and [BIND-01](../../../docs/spec/realization/artifacts.md#consumer-selected-subject) join the
same source, binding, actor and body. A pure expression frontend and a supplied
local-code frontend can instantiate this interface without sharing a DSL.
The [program correspondence](../correspondence/programs.md) states
their exact formation and locality premises.

`Frontend.inputs` remains a supplied predicate; its name does not establish
that all decisions depend only on an actor's permitted view. Concrete local
input and execution laws provide that connection for declared views/private
memory. Global phase legality and local information access are different checks.

## 2. Interpretation closure

[BIND-02](../../../docs/spec/realization/artifacts.md#interpretation-closure) includes actual
algebra and operation/module meaning. The same `mul(3,3)` returns 4 in the field
of order 5 and 2 in the field of order 7. Source spelling or ABI identity alone
cannot select that meaning. Lean parameters and imports fix the mathematical
instance; a native resolver must bind its installed implementation accordingly.
The consumer supplies the reference source independently of the candidate.

## 3. Four different uses of identity

[BIND-03](../../../docs/spec/realization/artifacts.md#identity-purposes) distinguishes
source/capture, runtime reference, preparation and probability identities, plus
the separate authority of a live continuation entry. An immutable capture fixes
values for its declared lifetime. A mutable reference resolves in a world and
follows actual transitions; equal cache keys or public receipts supply no right
to bypass those transitions. No single hash or ownership type establishes all
of these laws.

## 4. Open, admitted and sealed

[BIND-05–09](../../../docs/spec/realization/artifacts.md#lifecycle-and-release) distinguish
lifecycle state, exact selected subject, requirements and format scope. The
independent direct-plan model admits only its own rule and complete-execution
claim, with no introduced requirements. Its tagged-array codec is a model-specific
exchange profile. Current native packages use the
[exact identity contract](../../../docs/runtime/artifact-identity.md), with authentication
and execution through the shared Host. Model proofs do not validate that byte
boundary.

Sealing identifies a fixed subject and evidence/trust references. It does not
make private captures, generated code, digests or diagnostics safe to release.
Their joint publication belongs to the selected observer's disclosure policy.

## 5. Mutation and reuse rules

[BIND-04](../../../docs/spec/realization/artifacts.md#premise-preserving-reuse) permits reuse when an
actual frame, dependency or equivalence law preserves the required premises.
Changed captures, fields, guards, failure summaries and terminal targets cannot
inherit evidence by copying a status flag. Unrelated definitions and lawful
mutable transitions can preserve unaffected conclusions.

The [correspondence map](../correspondence/realization.md) lists
actual proof support and controls. Same-typed swaps, stale values, wrong source
occurrences, failed consumption and artifact substitution exercise different
parts of binding; no one successful control certifies the whole resolver.

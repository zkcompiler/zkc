# Assurance

Definitions, kernel-checked propositions, source-relative compiler checks,
native tests and declared trust establish different claims. Each claim must name
its actual subject, assumptions and evidence.

## Formal propositions

The independent [formal specification](../formal/docs/spec/README.md) defines the
models. [Formal support](../formal/docs/support.md) owns the theorem inventory,
premises and limits; [correspondence maps](../formal/docs/README.md#definitions-and-proofs)
link selected clauses to exact declarations. Some profiles give their formal
references in-page. A generic record states obligations; constructing such a
record does not verify an arbitrary native implementation.

The library's declaration audit permits only `propext`, `Classical.choice` and
`Quot.sound` in the transitive dependencies of reached library, tool and example
declarations. External dependencies may contain unfinished proofs, but reached
declarations may not depend on them. This audit does not prove kernel correctness
or statement adequacy.

`native_decide` adds native-evaluation trust and is excluded from the proof
library, its tools and its examples by structural controls. Conformance cases
under `formal/Tests/` use it only in `example` declarations: those cases check
compiled evaluation on named inputs and are not audited library theorems.
Declaration counts therefore do not measure those tests or model maturity.

## Contract boundaries

| Claim | Owning definition | Additional native obligation |
|---|---|---|
| Preserve observations and disclosure | [Observations](../formal/docs/spec/core/observations.md), [disclosure](../formal/docs/spec/properties/disclosure.md) | Implement the selected projection over actual releases, diagnostics and identifiers |
| Authorize a retained continuation | [Accepted continuations](../formal/docs/spec/profiles/services/accepted-continuations.md) | Actual identity, custody and publication adapter; the model's atomic single export is not distributed persistence |
| Bind interpretation to the supplied subject | [Artifacts](spec/realization/artifacts.md), [representations](spec/realization/representations.md) | Resolver, loader, parser and backend correspondence |
| Use a conditional checked result | [Judgments](spec/verification/judgments.md), [refinement](spec/verification/refinement.md) | Native checker correspondence and actual premise discharge |
| Establish source adequacy | [Relation encoding](spec/relations.md#source-encoding-adequacy), [source translation](spec/language/translation.md) | Preserve the intended source, captures and actual target; import/type validity alone is insufficient |
| Establish protocol acceptance | [Relations and terminals](spec/relations.md) | Actual terminal consumption plus the argument-specific security experiment |

## Native checks and trust

| Boundary | Current evidence and remaining trust |
|---|---|
| Source and MLIR lowering | Bounded [adjacent and emitted-artifact comparisons](compiler/verification.md); no native Lean refinement theorem |
| Artifact admission | Native parsers, structural checks, exact byte pins and interface binding; no universal decoder theorem |
| Runner and backend | Installed operation contracts and [native execution tests](../tests/native.md); runtime and primitive correctness remain implementation assumptions |
| Cryptographic providers | Scheme-specific assumptions and actual sampling/encoding contracts; product-tape mathematics does not prove native RNG or hash security |
| Whole protocol properties | Only exact established propositions under their hypotheses; no blanket soundness, extraction or zero-knowledge guarantee |

Source-relative checking and supplied-artifact admission are separate. A digest
authenticates authorized bytes without proving their derivation from source.
Two interpreters agreeing on one exported program cannot detect a shared
source-to-program mistake. References compute expectations from original inputs
and a separately implemented contract at the boundary being tested.

## Verification and reproducibility

The [formal package guide](../formal/README.md#build-and-validate) describes builds,
axiom audits and fresh reproduction. A reproducer or workflow definition is not
evidence that it succeeded on the current revision. Build records identify
source, dependency locks, toolchain and completed scope; pinned Lean/Std and its
kernel remain trusted.

[Tests](../tests/README.md) select native and formal checks. Finite controls can
discriminate errors and document bounded behavior without proving all inputs.
Timeouts and unsupported cases are not agreement. Measurements follow the
[documentation policy](development/documentation.md); no benchmark campaign is
currently maintained.

## Native correspondence

The native source semantics, exported artifact and Runner need an explicit
connection before independent Lean results apply to them.

A realization claim MUST identify the actual implementation and build, its
relation, input domain, observer and trusted boundaries. It MUST distinguish
kernel proof replay, trusted executable checking, independent differential
evidence and declared assumptions. A mathematical simulation establishes its
mathematical adapters; a claim about native parsing, FFI or allocation supplies
the corresponding connection to those actual operations.

Differential controls used for a realization claim MUST exercise the actual
retained source and candidate data and compare complete related results,
including negative cases. Passing those controls does not establish a universal
native theorem or a protocol-security bound.

Each comparison fixes:

- the source subset and actual executable bytes;
- actual inputs, initial states and provider behavior;
- returned/stopped outcomes, residual-state relation and ordered observations;
- capacity premises or related budgets when exhaustion is in scope;
- parser, primitive, runtime and build/loader assumptions that remain trusted.

Successful outputs alone are insufficient when failed prefixes or state are
observable. A sufficient-capacity relation cannot be reported as equality under
arbitrary unchanged instruction caps. Erasing charge events does not erase a
different stop or residual state.

A connection may establish one scoped boundary at a time. Cryptographic
security additionally fixes the actual
statement, adversary, oracle/sampling model, encoding and property transport.
Transcript construction correctness is not a Fiat–Shamir security reduction.

[Formal connection components](../formal/docs/native-connection.md) identify
existing laws; the [roadmap](roadmap.md) sequences further work.

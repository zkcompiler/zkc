# Native IR foundation

The foundation retains the information needed to compile mathematical protocols
through one shared execution model. Exact contracts live in the native
[profiles](../spec/profiles/README.md); [status](../status.md) and
[validation](foundation-validation.md) record support and evidence.

## General mechanisms

| Mechanism | Owning contract |
|---|---|
| Total mathematics and role availability | [Mathematical protocols](../spec/profiles/compiler/mathematical-protocols.md) |
| Structured data and bounded protocol iteration | [Structured iteration](../spec/profiles/compiler/structured-iteration.md) |
| Ordered local algorithms and failure | [Local control](../spec/profiles/compiler/local-control.md) |
| Runtime-count containers | [Nested data](../spec/profiles/compiler/nested-data.md) |
| Formal polynomial realization | [Polynomial recipes](../spec/profiles/compiler/polynomial-recipes.md) |
| Static protocol applications | [Composition](../spec/profiles/compiler/protocol-composition.md) |
| Service aliases and persistent provider state | [Native services](../spec/profiles/compiler/native-services.md) |
| Independent producer/validator execution | [Native proofs](../spec/profiles/compiler/native-proofs.md) |
| Early completion and bounded search | [Entry completion](../spec/profiles/compiler/entry-completion.md) |

Protocol algorithms compose ordinary mathematics, explicit messages and installed
primitives. General kernels may implement bulk algebra, hashes, codecs or setup
operations; they do not hide a complete protocol interpreter. Programs retain
local function bodies and relation bindings for inspection and checking.

## Information retained for observation analyses

Analyses consume the actual source operands, role-local receives, draw
occurrences, resource origins, ordered guards/stops, outputs and later disclosure.
A dynamic loop occurrence includes its iteration coordinates. Metadata can locate
that occurrence but cannot replace its semantic dependency relation.

[Public-coin views](public-coin.md) are a bounded application of this information.
A later security analysis must still define its statement, observation,
initialization and adversarial experiment. Available dependency data alone proves
no sampling law, security reduction or leakage bound.

## Completion tests and limits

Validation follows actual source through emitted bytes and separate native
execution. Composed clients exercise changing shapes, nested calls/repetition,
structured proof messages, setup identity, retained state and failures. Negative
controls substitute receives, terminals, resource roots and same-shaped relation
data. Code size, compile work, value capacity and execution limits are distinct.

These tests establish bounded implementation behavior. Native Lean correspondence,
cryptographic security and broader library development remain separate. Old
Frontend, table and application consumers are retired; the foundation carries no
requirement to reproduce their old formats or port their protocol libraries.

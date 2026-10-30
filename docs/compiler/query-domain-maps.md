# Query-domain maps and the shared catalog

Binary FRI needs a map from a selected source position to its two natural-order
coset positions. The current library computes it with checked `index.div`,
`index.mod` and `index.add`. Those operations may stop; their presence in the
installed catalog does not admit them inside a total virtual-oracle query body.

The selected next boundary is a bounded domain-map family tied to an immutable
actual shape. Keep the general checked index operations unchanged. Implementing
this mathematical family is a joint IR/Lean unit, after the existing-family
probe, rather than a parser alias or a new runtime arithmetic engine.

## Evidence from the existing four faces

| Face | Existing owner | What is established |
| --- | --- | --- |
| Frontend | Ordinary library declarations and resolved operator bindings | The retained source profile resolves division, remainder and addition to exact checked contracts. Layout library primitive declarations still need their projection before library migration. |
| IR | Neutral contract declarations and admitted local calls | The actual compiled helper retains checked arithmetic and ordered guards; it is not a mathematical helper. |
| Execution | Independent native index installation | Eighty actual Host cases, with simplification on and off, cover even shapes, every position in small domains, u64 boundary values, and refusal without results for empty/odd/out-of-range inputs. |
| Lean | Existing `Structured.PrimitiveLaws` | Six compiled equations establish half positivity, low/high ranges, reconstruction, conditional native remainder/addition results and natural coset pairing. They reuse the existing primitive laws. |

The probe checks a library operation family, not a newly installed primitive.
Its Lean equations are about the independent model under explicit premises;
they are not a source-elaboration or native-kernel simulation. The runtime
cases use the retained source profile because the layout library primitive
adapter is not installed. No broader catalog migration follows merely from
matching names or successful examples.

## Shape-bound semantics

Let the actual immutable row count be `n`, with `0 < n < 2^64` and `n` even.
Let `h = n / 2`. The closed map family has the equations
`low(i) = i % h` and `high(i) = low(i) + h`. Both outputs are representable and
inside the source domain for every representable `i`. When `i < n`, one of the
two outputs equals `i`. The reached oracle query must still check `i < n`
before using a map; total arithmetic is not authority to query out of bounds.

Admission must bind the shape parameter to the same actual anchor used by the
query. A static maximum is only a resource bound and cannot stand in for `n`.
Source mutation, another anchor, a changed actual shape or a different capture
invalidates the association. Dynamic shape checks happen at the defined ordered
boundary; moving them into a pure helper would change refusal behavior.

For natural multiplicative coset order, with `g^h = -1`, the points at `low`
and `high` are opposites. This algebraic premise is separate from integer range
formation: an even array length does not establish a valid two-adic domain.
The total fold keeps explicit inverse-two and inverse-point values and needs
their laws separately. The [FRI paper, section 2.1](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ICALP.2018.14)
explains the domain reduction and paired-query consistency test; zkc's concrete
natural-order convention belongs to its library and formal model.

## Alternatives and decision

| Alternative | Assessment |
| --- | --- |
| Admit general checked arithmetic as Math | Rejected: zero division and overflow remain observable failures. |
| Add unrestricted dependent integer refinements | More general than this boundary needs; it would require a solver, export language and independent proof reconstruction before the first map. |
| Use only static bit masks | Insufficient for dynamic actual shapes and general even-domain tests; it also hides ordering assumptions. |
| Precompute a virtual table or create a constant anchor per query | Changes the virtual definition, identity, work and reached-query behavior. |
| Closed shape-bound map family, lowered to existing checked operations | Selected: narrow total equations, explicit shape premises, reuse of execution and Lean laws, extensible to separately declared map families. |

The family descriptor should name the frontend library declaration, logical
signature and shape dependency, existing execution recipe, and Lean definition
with its law identifiers. Consumers continue to validate independently. Reuse
the existing TableGen contract machinery; do not create another cross-language
schema framework or generate proof authority from a `total` flag.

Before installation, require a source/export representation for the exact shape
association, IR mathematical admission, independent actual-body checking, native
boundary cases and Lean reconstruction of the range premises. The frontend may
then resolve the ordinary library name through the catalog. No new language
keyword, general arithmetic-purity rule or runtime oracle object is required.

## Acceptance scope

The shared FRI/STARK acceptance test remains open until the complete layout
client, virtual definition, realization and formal admission consume the same
source/configuration. A successful map probe or a single fold layer does not
pass that test. Report frontend, IR, Lean and runtime results separately, using
the [contract register](../spec/contracts.md#shared-oracle-stack-acceptance-boundary).

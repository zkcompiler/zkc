# Shared operation contracts

The compiler operation catalog connects admitted source contract keys to typed
MLIR operations. It owns independently consumed structural facts. Mathematical
meanings remain with the [domain specifications](../spec/README.md), and a
physical binding still selects an implementation of a contract rather than
changing its meaning.

Polynomial interpretation conversions belong to `poly`: `point_to_vector`,
`point_from_vector`, `table_to_vector` and `table_from_vector`. The logical
catalog keys `vector.from_point`, `vector.to_point`, `vector.from_table` and
`vector.to_table` retain their declared meanings. This is a catalog-to-MLIR
mapping, like `field.add` to `algebra.sum`, with no alternative legacy operation
or fallback decoder. Coordinate order, dimension and Boolean-table shape are
polynomial-domain obligations, even when a backend shares the sequence storage.

`Contracts/Operations.h` attaches these facets to each registered `Kernel`:

| Facet | Contents | Consumers |
|---|---|---|
| Sampling | Provider kind, sample domain, provider input, sample/successor outputs, optional bound input | Oracle dependency analysis; construction resource and availability analysis |
| Derived counterpart | Registered transcript operation with matching sample and parameter ports, if construction supports it | Public-coin construction and emission |
| Observation | Provider input, payload input and provider successor | Exact transcript-chain absorption and historical dependency analysis |
| Public replay | An explicitly installed construction recipe | Availability analysis and participant mirroring |
| Acceptance guard | An operation whose completing execution requires its Boolean input | Execution view and oracle acceptance analysis |
| Conjunction | An output whose truth entails its Boolean inputs | Acceptance-sink closure |
| Diagonal map / linear contraction | Factor, coefficient, value and result roles under the domain's scalar-action law | Typed MLIR diagonal representation selection |
| Ordered coset / exact domain value | Shift, size, vector-result and fold roles; a small vocabulary of exact value equations | Conditional nominal-domain congruence and compatibility inspection |

These are compiler contracts for installed operations, not arbitrary source
assertions. An unknown key has no positive facts. A registered provider-consuming
operation without an analysis transfer contract remains unclassified. The
catalog test checks sampler/observation port shapes, counterpart consistency and
coverage of installed RNG/transcript operations. Nonce transitions have atomic
runtime custody contracts but no sampling transfer summary; dependency analysis
retains unknown coverage for them instead of classifying them as ordinary data.

Replay eligibility is narrower than mathematical determinism. Replaying an
operation adds an occurrence at another participant; common-subexpression
elimination removes one. Neither operation is licensed by the other's facet.
No facet implicitly grants MLIR purity, speculation, cryptographic security or
permission to discard a failure, frame, logical charge or transcript occurrence.

Algebraic map/contraction facts do not name a physical layout. MLIR's optional
`DiagonalProducerInterface` and `DiagonalContractionInterface` expose installed
representation choices after exact binding/type checks. Their absence does not
make an operation nonlinear; their presence is not a new algebraic proof. This
separates the mathematical contract from current Arkworks/Dalek applicability.

The current RNG type's nominal field parameter selects the installed sampling
capability. Entropy, bounded-index sampling and field algebra remain independent
contracts. A private vector sampler can have a known state successor without
having a public-challenge construction counterpart.

## Custody is independent of transport

`Contracts/TypeProperties.h` classifies admitted logical kinds as public-codec
values, private immutable custody, affine resources or unknown. A public-codec
classification describes representability, not permission to disclose a secret.

- Serialization requires a registered public codec kind and all ordinary
  domain, representation and ownership checks.
- Local duplication and discard have independent positive queries. They agree
  for the current installed immutable kinds, including keys and opening state.
- Provider/capability tokens have affine use and generation rules. Generic
  storage release does not discharge them.
- Unknown abstract kinds acquire no positive duplication, discard or transport
  permission. Absence of `affine` is not a proof of any of those permissions.

Construction can preserve a whole immutable local computation without making
its private inputs public or mirroring it to another participant. Operations
that transform selected provider state retain their construction-specific
interpretation. Physical local storage release uses discardability, not the
availability of a wire encoding; its [accounting contract](interactive-execution.md#ordinary-local-storage-lifetime)
continues to retain logical charges until frame exit.

## Representation and assurance boundaries

Source occurrence analysis and MLIR verification share catalog facts. Source
analysis does not require converting the protocol to physical kernels, and
MLIR transformations do not substitute for the source-relative checker.
Rust and Lean maintain independent interpretations. Their checks and
differential tests can detect disagreement with the compiler; sharing a schema
does not by itself prove conformance.

The Lean sampling transfer module proves monotonicity and separation of direct
reception from provider history. The locality module proves that fixing entry
values and provider replies fixes a direct-reception-free local expression,
including ordinary sampler arguments.
These facts support the [oracle analysis](../spec/domains/oracles.md), while
native extraction, codec injectivity, sampler laws and protocol-security
reductions remain separate obligations.

Construction uses `duplicable` to retain a producer-local immutable helper as a
whole call, including helpers returning private commitment state. Its generated
source therefore has the canonical whole-helper frame and charges; no equality
with the old per-operation generated frames is asserted. Artifacts are rebuilt
and checked against the actual generated source. Private custody gains neither
a public codec nor a cross-role replay rule through this choice.

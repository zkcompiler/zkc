# Selected profiles

A profile instantiates common definitions with a particular vocabulary,
representation, algorithm or experiment. Its scope is the resulting judgment
and its stated premises. A profile does not specialize the whole language to
its own field, degree bound, register count or artifact format.

## Profile parameters and dependencies

A selected profile fixes the operands relevant to its claim: domain objects,
source and input interpretation, interface and effects, admitted initial states,
result and observer, and any transformation or property relation. A portable
profile additionally fixes descriptor and value formats, resolution, capacities
and failure behavior. A probabilistic claim fixes the actual
[joint law](../properties/probability.md) and
[strategy information](../properties/experiments.md#strategy-information-and-statement-selection).
A protocol acceptance claim fixes the actual
[terminal consumer](../properties/relations.md#terminal-decisions-and-contracts).

These parameters use the common [language](../language/programs.md),
[execution](../core/execution.md) and [interpretation](../core/interpretations.md)
definitions. Missing operation laws, source binding or provider premises cannot
be inferred from a profile's name. An implementation states which selected
profiles it realizes and supplies the corresponding
[conformance claims](../conventions.md#conformance-claims).

## Definition inventory

The following links identify the definitions and selected scope of each profile.

| Group | Profile | Selected scope |
|---|---|---|
| Source | [Named inputs and role stores](source/named-inputs.md) | Exact ordered string-named binding, diagnostics, permitted views and local runs |
| Source | [Public dimensions](source/public-dimensions.md) | Scoped natural expressions, formation, actual public values and substitution |
| Source | [Invocation-selected families](source/families.md) | Public input selection, dependent protocol shapes, complete outcomes and bounded admission |
| Source | [Resolved authoring](source/authoring.md) | Source environments, naming, elaboration, identity and authored selection |
| Source | [Checked libraries](source/checked-libraries.md) | Interface requirements, components, prepared values and relation-bound preparation facts |
| Source | [Expressions and captures](source/expressions.md) | Positional reads, ring expressions, dependencies and immutable issuance |
| Source | [Resolved definitions](source/definitions.md) | Shared acyclic bodies, typed calls, complete stopping, capture/reference renaming and optional inlining |
| Source | [Generic static foundation](source/generic-definitions.md) | Checked equality/capability derivations and structured type substitution with complete execution preservation; native generic resolution is separate |
| Source | [Closed operation bindings](source/operation-bindings.md) | Native nominal types, explicit operation applications and per-value physical selection |
| Source | [Located calls and shared control](source/located-execution.md) | Role-local execution/admission, complete stop origins, peer-state frames and actual guard/count agreement |
| Source | [Resolved common protocols](source/common-protocols.md) | Role-owned ports, shared protocol bodies, selected bindings, independent reception and fixed public loops with complete stopping |
| Compiler | [Direct plans](compiler/direct-plan.md) | Evaluator, exact direct checking, version-1 grammar and separate phase sidecar |
| Compiler | [Scheduled participant lowering](compiler/scheduled-participants.md) | Role-local operands, distinct send/receive instructions, shared calls/loops and complete source-to-target execution equality |
| Compiler | [Finite phase certificates](compiler/finite-phases.md) | All-reply summaries, finite covers, structural checking and realized admission |
| Compiler | [Factor preparation](compiler/factor-preparation.md) | Live facts, guarded typed rule, frames, allocation and immutable preparation |
| Compiler | [Local algorithms](compiler/local-algorithms.md) | Shared acyclic local calls, bound entailment, expansion and complete stopping |
| Compiler | [Local control](compiler/local-control.md) | Typed local conditionals and bounded loops, resources and failure behavior |
| Compiler | [Local variants](compiler/local-variants.md) | Nominal variant construction, exhaustive matching and payload/resource bounds |
| Realization | [Instruction-list execution](realization/instruction-machine.md) | Embedded exits, list execution and justified resumption |
| Realization | [Scalar bytes](realization/scalar-bytes.md) | Selected width/modulus, prefix decoding and actual failed receive effects |
| Providers | [Product tapes](providers/product-tapes.md) | Persistent transitions, residual reconstruction and actual next-request consumer |
| Sumcheck | [Quadratic coefficients](sumcheck/quadratic.md) | Degree-two objects, ordered table compilation and coefficient encoding |
| Sumcheck | [Scalar rounds](sumcheck/scalar-rounds.md) | Logical interaction and supplied early-round adapter returning a residual scalar |
| Sumcheck | [Interactive verifier](sumcheck/interactive.md) | Complete source, supplied endpoints, actual terminal, soundness and checked evaluation |
| Sumcheck | [Typed framing](sumcheck/framing.md) | Fresh/framed interpretation, full statement root and complete query transitions |
| Sumcheck | [Local prover cuts](sumcheck/local-prover.md) | Finite local code, actual input admission and returned abort/commit cuts |
| Sumcheck | [One-round consumer](sumcheck/one-round-consumer.md) | Committed local cut, actual challenge, terminal against 2r and acceptance bound |
| Services | [Affine services](services/affine.md) | Response law, fixed controller, coupling, captured source and installation |
| Services | [Issued causal experiment](services/issued-causal.md) | Actual issued local source, normalized sampler and one-round acceptance bound |
| Services | [Commitment sessions](services/commitment-sessions.md) | Finite atomic scheduler, ordered trace and shared preparation |
| Services | [Accepted continuations](services/accepted-continuations.md) | Verifier/arm reports, installed policy, atomic ledger and exports |

Shared chapters supply common laws; the inventory links do not assert that all
profile operations have one probability law or one terminal meaning. In
particular, an early scalar-round return is distinct from full Sumcheck
acceptance. A completed partial-response service is distinct from proof
acceptance. An atomic commitment session is distinct from a service whose
interface exposes a partial response.

### Sumcheck components

The [quadratic coefficient object](sumcheck/quadratic.md) supplies the statement.
[Scalar rounds](sumcheck/scalar-rounds.md) define messages and logical phases;
the [interactive verifier](sumcheck/interactive.md) adds the actual terminal.
[Framing](sumcheck/framing.md) interprets calls using a retained statement root.
The separate [local prover](sumcheck/local-prover.md) returns cuts. The
[one-round consumer](sumcheck/one-round-consumer.md) uses a committed cut and an
actual challenge under the selected [product-tape laws](providers/product-tapes.md).
These components retain their distinct result types, providers and claims.

### Service components

The [affine service](services/affine.md) owns its fixed controller, joint response
law and captured-source issuer. The [causal experiment](services/issued-causal.md)
uses the issued local code with its actual sampler. The
[commitment-session machine](services/commitment-sessions.md) is a separate
finite client of shared preparation with its own scheduler and observer.

## Contrasting domain clients

*Note (informative).* The following clients illustrate distinct domain
interpretations; they do not select additional cryptographic interfaces.

A Sigma client can use separate scalar and group sorts, module operations and
an actual final group equation. Its source-to-reference law fixes the statement,
received message, challenge and response under the selected primitive meanings.
Swapping same-sort operands is a source change even when it remains well typed.
Honest algebraic completeness does not establish extraction or an adversarial
soundness experiment.

A Merkle client retains the actual commitment root, query index and ordered
path. An interpreted path operation can expand into ordered leaf and node
operations. Its source-to-reference law binds those exact operands and the
declared root comparison, including failures inside the expansion. A correct
fold under supplied primitives does not by itself establish hash binding or
FRI soundness.

The [domain correspondence](../correspondence/domains.md#root-domain-map)
identifies the reference sources and their theorem scope.

## Message-shape reference client

*Note (informative).* The natural-word message frontend illustrates public
shape formation and hostile payload admission. Its raw sequence has four
header words
(field, domain, instance and round identifiers), followed by all coefficient
words. Formation evaluates public round-count and width expressions; checking
requires matching identifiers, an in-range round, the exact width, positive
cardinality and each coefficient below that cardinality. Zero width is allowed.
Missing parameters and hidden-value expressions refuse formation, including in
an operand multiplied by zero. The accepted payload type contains every raw
value satisfying these shape conditions, independently of honest equations.

This frontend specifies no byte order or arithmetic interpretation derived
from those numeric identifiers. The scalar-byte reference consumer
reads three encoded scalar words and then constructs the four trusted header
words internally. Its byte stream therefore does not contain the natural-word
header. The [Sumcheck profile](sumcheck/scalar-rounds.md#messages-and-logical-rounds) uses
typed field triples and selects no interoperable wire format from this client.

The separate parameter-family client uses field/instance tags and a public
per-round degree to type coefficient vectors of length `degree+1`. All such
vectors remain legal adversarial
messages. These clients illustrate the common distinction between public
shape, actual domain interpretation and protocol equations; they add no
universal header or degree expression to the language. Their sources and
implemented boundaries are listed in the
[message-client correspondence](../correspondence/domains.md#message-shape-reference-clients).

## Cross-protocol correspondence

A connection between profiles names the actual source and target, maps their
inputs and domain objects, and states the complete-result or property relation
being claimed. It establishes the relevant preservation premises at every
boundary: source formation and binding, operation interpretation, analysis and
checking, representation, and actual terminal or observer use. Constructor
agreement for one interpreter does not establish that another frontend or
native backend realizes the same subject.

The [protocol guide](../../guides/protocols.md)
locates Sigma, Merkle, cubic opening reduction and full FRI, KZG and ZKBoo
applications at their actual scopes. A local cache theorem, an opening-reduction
lemma or finite native controls do not supply a missing whole-protocol join.
Bounded-machine research likewise does not enlarge the
[selected execution envelope](../conventions.md#execution-envelope).

## Evidence and interpretation scope

Raw parsing, actual capture binding, primitive realization and exposed native
interleaving require their selected correspondences. Ordered emissions inside
an atomic operation do not alone create callback points. Native behavior with
additional interleaving needs an interface and law that exposes that behavior.

*Note (informative).* The [domain correspondence](../correspondence/domains.md),
[assurance map](../../assurance.md) and [status](../../status.md) identify proof
dependencies and achieved support for these definitions.

The native [canonical local algorithm profile](compiler/local-algorithms.md)
selects a bounded acyclic stored-body subset, an MLIR expansion boundary, and
explicit accounting and occurrence transport. It does not assert equivalence to
a separately charged runtime call stack.

The [structured local-control profile](compiler/local-control.md) defines isolated
branch/loop formation, finite runtime bounds, affine carries and charged regions.
It does not extend protocol interaction with dynamic choice or unbounded loops.

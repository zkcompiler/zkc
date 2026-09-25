# Realization and native boundaries

The [representation specification](../spec/realization/representations.md),
[codec/receive specification](../spec/realization/codecs.md) and
[binding specification](../spec/realization/artifacts.md) own these contracts. This guide
connects them to the [runtime design](../runtime/design.md), the current
[direct-plan implementation](../runtime/reference-execution.md) and mathematical adapter examples.
Rationale records explain the [representation relation](../rationale/representation-relation.md)
and the [relations of identity](../rationale/identity-purposes.md);
[correspondence](../spec/correspondence/realization.md) states proof scope.

## 1. Data and complete-result relation

[REAL-01–02](../spec/realization/representations.md#related-complete-results)
use a state relation and a returned-value relation indexed by the actual final
states. This permits a logical value to correspond to an allocated buffer handle.
Sequencing relates the consumer of that handle in the resulting heap; composing
relations uses the same intermediate execution. The
[simulation controls](../../formal/Tests/Simulation.lean) reject stale contents,
rollback after failure and missing events.

[REAL-04–05](../spec/realization/codecs.md#codec-domains) distinguish honest
round trips, arbitrary-success faithfulness and complete receive behavior. In
the scalar byte profile a noncanonical full word consumes eight bytes while an
underrun consumes none. A pure decoder returning `none` cannot express that
difference; the [operational adapter](../../formal/Zkc/Protocols/ScalarBytecode/Execution.lean)
and typed read packet retain it. These are mathematical adapter proofs, with
actual native parser correspondence separately required.

## 2. The source-selected adapter

[REAL-03](../spec/realization/representations.md#source-selected-adapters) binds actual
arguments to the consumer's source/site, domains, ordered inputs and captures.
This is where same-typed input swaps, changed fields, omitted guards and stale
references must be caught. A proof term can disappear at runtime while its
proposition still has to hold at actual use. Compare complete results and
intermediate observations, including failures, under the chosen relation.

## 3. Provider and backend contracts

[REAL-06–07](../spec/realization/representations.md#algebra-and-provider-correspondence) separate
algebra, codec, provider and storage obligations. Rust traits organize the
implementation but do not prove their laws. Arkworks implements selected native
arithmetic/codecs; ArkLib supplies separately resolved mathematical definitions
and reduction consumers. Neither connection proves the other.

A replacement backend uses an actual relational law. Equal weak unary contracts
alone do not establish equivalence. Immutable preparation validity, live fact
survival and allocation ownership retain their different premises. The
[native correspondence design](../../formal/design/native-correspondence.md)
and [assurance policy](../assurance.md#6-implementation-correspondence-policy)
distinguish differential evidence, explicit trust and optional implementation
proofs.

## 4. Runtime and OIR

[REAL-08–11](../spec/realization/representations.md#capacity-and-progress) define the
resource, completion, embedded-exit and custody boundaries. A native plan can
choose buffers, ownership and schedules without being a unique canonical graph.
A changed representation supplies a relation, while exact comparison remains a
useful conservative checker for the direct profile.

The instruction-list profile returns its machine exit as data. Its append law
needs the proved absence of a primitive incomplete halt; it is not permission
to resume an outer PIR stop. Host interruptions likewise differ from modeled
complete results. A private continuation ledger has no implicit crash persistence,
distributed consistency or hostile-owner authentication.

## 5. First correspondence and regression set

[REAL-12](../spec/conventions.md#conformance-claims) owns the evidence
boundary. The maintained native plan and interactive routes have bounded differential
evidence; [status](../status.md) records their coverage. Broader preparation
reuse and enclosing-controller delivery remain on the roadmap.
Controls for each implemented interface must exercise its actual parser,
lowering and runtime: changed captures, wrong domain/world, same-typed swaps,
omitted guards, failed writes, exhausted tapes, remaining-byte differences,
stale aliases and wrong-target/replayed export where exposed. Legitimate mutable
transitions and unrelated module edits are positive reuse controls.

Data refinement, explicit contracts and source-relative validation connect
these interfaces. They permit implementation progress without claiming that a
mathematical model has already verified the native backend.

The opt-in [public-operand Ristretto MSM](../runtime/public-msm.md) illustrates a compatible
kernel substitution with an additional leakage premise, checked artifact-role
admission, and a separate backend caller-authority boundary.

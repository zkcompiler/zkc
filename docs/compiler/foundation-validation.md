# Native validation scope

Validation connects the actual source, adjacent compiler subjects, emitted
program and Host execution. The [foundation contract](ir-foundation.md) defines
the capability boundary; [status](../status.md) records support. The
[test guide](../../tests/README.md#selecting-checks) owns command selection.

## Source-to-artifact checks

Language controls check syntax, static types, permissions, Entry closure and
independent comparison of emitted IR with checked definitions. Native compiler
controls then check preparation, role projection, participant rewrites, demand
lowering, physical materialization and serialization. The
[preservation guide](preservation.md) states the recognized relation at each edge.

Export comparison reads the actual executable and compares it with physical SSA.
Bundle schedules and deployment maps are checked against retained source
interfaces and actions. Encoder/decoder round trips or reconstruction using only
the producer's routine do not supply these independent comparisons.

## Execution and failure coverage

| Capability family | Evidence route |
|---|---|
| Source and named application interface | Maintained Schnorr/Sumcheck projects, Language/Host controls and installed C++/Rust consumers |
| Scalar and structured mathematics | Generated native programs and independent arithmetic expectations |
| Role projection and control | Actual receive substitutions, nested repetition, local branches and completion controls |
| Resources and services | Exact-origin mutations, affine custody, alias state, work exhaustion and cleanup |
| Composition and relation binding | Original-input arithmetic references, same-shaped relation substitutions and actual terminal decisions |
| Proof framing and setup | Independent producer/validator processes, malformed frames, public-context changes and unauthorized material |
| Attempts | Retained provider state, failed prefixes, cumulative work and publication controls |

The detailed guides for [mathematical composition](mathematical-composition.md),
[structured proofs](structured-proofs.md), [attempts](native-attempts.md) and
[completion](entry-completion.md) record their bounded clients and limits.
Arithmetic examples do not imply complete argument libraries or external
prover/verifier compatibility.

## Independent references and trust

An independent reference computes expectations from original inputs and the
selected contract. It must not use the transformation under test as its oracle.
Two interpreters agreeing on an already wrong exported plan cannot detect the
source-to-plan error. Unsupported cases and timeouts are not agreement.

C++/Rust checks remain bounded native evidence. Lean source/direct-plan models
have their own interpretations and proofs. A connection to `zkc.program` needs an
explicit interpretation. Native semantics and differential/formal connections remain
separate work under [assurance](../assurance.md).

# Native validation scope

Validation connects the actual source, adjacent compiler subjects, emitted
program and Host execution. The [foundation contract](../docs/compiler/pipeline.md) defines
the capability boundary; [status](../docs/status.md) records support. The
[test guide](README.md#selecting-checks) owns command selection.

## Source-to-artifact checks

Language controls check syntax, static types, permissions, Entry closure and
independent comparison of emitted IR with checked definitions. Native compiler
controls then check preparation, role projection, participant rewrites, demand
lowering, physical materialization and serialization. The
[preservation guide](../docs/compiler/verification.md) states the recognized relation at each edge.

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
| Retained storage and work | Aliases against equal independent allocations, views retaining parents, multiwidth base/extension commitments and stated budgets at 65,536 rows and 64 openings |

Representative controls are linked below; their assertions define the exact
cases checked. Arithmetic examples do not imply complete argument libraries
or external prover/verifier compatibility.

| Boundary | Controls |
|---|---|
| Named source Entries | [Language Host](protocol/test_language_host.py), [CLI walkthroughs](protocol/test_developer_commands.py) |
| Mathematics and changing state | [Composition](../compiler/test/native_composition.py), [carried state](../compiler/test/native_composed_state.py), [nested data](../compiler/test/native_nested_data.py) |
| Relation identity and terminals | [Relation bindings](../compiler/test/native_relation_bindings.py) |
| Relation bundles | [C++ reference](../compiler/test/relation_bundle.cpp) and [Rust admission](../crates/zkc-runtime/src/relation_tests.rs), sharing one hand-authored fixture, its independently computed identity and its mutation outcomes |
| Proof messages and construction | [Structured proofs](../compiler/test/native_structured_proofs.py), [iteration](../compiler/test/native_iterated_proofs.py), [authored transcripts](../compiler/test/native_authored_transcripts.py) |
| UniformIndex sampling | [Source, formation and construction](../compiler/test/native_index_sampling.py), [independent transcript replay](../crates/zkc-test-drivers/src/native_index_sampling.rs), [spot-check client](protocol/test_index_sampling.py) |
| Retry and completion | [Attempt lifecycle](../compiler/test/native_attempts.py), [participant completion](../compiler/test/native_entry_completion.py) |
| Retained storage and logical work | [Proof-scale openings](protocol/test_retained_storage.py), [native ledgers](../crates/zkc-backends/tests/retained_storage.rs), [Runner ledgers](../crates/zkc-runtime/src/interactive/tests/storage.rs) |
| External relation export | [Clean export against finite AIR and ring providers](protocol/test_clean_air_conformance.py) |

## Independent references and trust

An independent reference computes expectations from original inputs and the
selected contract. It must not use the transformation under test as its oracle.
Two interpreters agreeing on an already wrong exported plan cannot detect the
source-to-plan error. Unsupported cases and timeouts are not agreement.

C++/Rust checks remain bounded native evidence. Lean source/direct-plan models
have their own interpretations and proofs. A connection to `zkc.program/0` needs an
explicit interpretation. Native semantics and differential/formal connections remain
separate work under [assurance](../docs/assurance.md).

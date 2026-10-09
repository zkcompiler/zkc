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
| Source inference and contracts | [Definition completion, annotations, static holes, service arguments and limits](../compiler/test/language_inference.cpp) |
| Mathematics and changing state | [Composition](../compiler/test/native_composition.py), [carried state](../compiler/test/native_composed_state.py), [nested data](../compiler/test/native_nested_data.py) |
| Relation identity and terminals | [Relation bindings](../compiler/test/native_relation_bindings.py) |
| Relation bundles | [C++ reference](../compiler/test/relation_bundle.cpp), [Rust reference](../crates/zkc-runtime/src/relation_tests.rs) and [cross-language controls](protocol/test_relation_bundle_conformance.py) compare identities, residuals, balances and refusal identifiers on imported AIRs and staged assignments over KoalaBear/Ext8. Resource controls bound declared data and expanded results before evaluation. The [polynomial view test](../compiler/test/relation_bundle_polynomial.cpp) checks the recurrence fixture's opening subjects, scoped quotient bounds and chunk count against an independent coefficient interpolation of its honest data, with edited-structure, inactive-scope, lifted-carrier, general-field and refusal controls. |
| Bundle polynomial view | [Static premises](../compiler/test/relation_table_view.cpp), [native view](../crates/zkc-backends/src/relation/polynomial_tests.rs) and the [source client](protocol/test_relation_table_polynomial.py) compare shapes, descriptors and scopes with hand derivations, dense residuals with combined matrices, and Ext8 points with an independent integer model. Batches equal their rows substituted one at a time and the dense residuals on the subgroup. Shared [chunk fixtures](../compiler/test/fixtures/relation/polynomial-chunks.json) relate the analysis's zero-chunk encoding to the runtime shape; resource controls cover empty and huge counts and the charge before preparation. |
| Proof messages and construction | [Structured proofs](../compiler/test/native_structured_proofs.py), [iteration](../compiler/test/native_iterated_proofs.py), [authored transcripts](../compiler/test/native_authored_transcripts.py) |
| UniformIndex sampling | [Source, formation and construction](../compiler/test/native_index_sampling.py), [independent transcript replay](../crates/zkc-test-drivers/src/native_index_sampling.rs), [spot-check client](protocol/test_index_sampling.py) |
| Retry and completion | [Attempt lifecycle](../compiler/test/native_attempts.py), [participant completion](../compiler/test/native_entry_completion.py) |
| Retained storage and logical work | [Proof-scale openings](protocol/test_retained_storage.py), [native ledgers](../crates/zkc-backends/tests/retained_storage.rs), [Runner ledgers](../crates/zkc-runtime/src/interactive/tests/storage.rs) |
| Pointwise maps | [Source controls and refusal locations](../compiler/test/language_map.cpp), [formula formation, Ring depth boundaries, realization schedule and correspondence mutations](../compiler/test/map_realization.cpp), [Host values, loops, shared helpers, shape refusals, height-independent work and measured helper inlining, scalar hoisting and dead scalar operations](protocol/test_native_map.py), [agreement with Ring providers and coset kernels on KoalaBear/Ext8, including off-domain interpolation](kernels/test_pointwise_polynomials.py) |
| AIR STARK and FRI | [FRI controls](protocol/test_fri.py) exercise independent polynomial words, dishonest folds and terminals, every query layer and transcript ordering. [AIR controls](protocol/test_air_stark.py) cover imported traces, separate proof Hosts, mutated claims/roots/late openings and excluded-set sampling; independent Ext8 interpolation checks quotient chunks, OOD claims and the DEEP word. [Scope and layout controls](protocol/test_air_polynomials.py) test native polynomial helpers against integer arithmetic. These are bounded execution checks, not a soundness reduction. |
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

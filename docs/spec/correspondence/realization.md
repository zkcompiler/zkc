# Realization and identity correspondence

This map covers [representations](../realization/representations.md),
[codec/receive boundaries](../realization/codecs.md) and [binding](../realization/artifacts.md). `D` denotes a definition, `T` a theorem under its
actual hypotheses, and `O` a policy or adapter obligation. A row containing
both does not mean that its policy has become a proved native theorem.

## Realization clauses

| Clause | Formal correspondence | Actual hypotheses and limits |
|---|---|---|
| [REAL-01](../realization/representations.md#related-complete-results), [outcome and state relations](../realization/representations.md#outcome-and-state-relations) | D: `PIR.Outcome.Relates`, `PIR.Execution.Relates`; T: `Tests.Simulation.allocated_result`, `Tests.Simulation.stale_heap_rejected` | Actual complete results, selected state/value/observer relation; value relation uses final states; O: actual native initial-state correspondence |
| [REAL-02](../realization/representations.md#sequencing-represented-values), [transitive composition](../realization/representations.md#transitive-composition), [observers](../realization/representations.md#observers) | T: `PIR.Execution.Relates.follow`, `PIR.Execution.Relates.trans`, `PIR.Execution.Relates.of_related`, `Tests.Simulation.allocated_then_loaded` | Related returned values and states for suffix; exact common intermediate execution/observer; no implicit arbitrary target context |
| [REAL-03](../realization/representations.md#source-selected-adapters) | D: `Zkc.Compiler.CheckedPlan`; T: `Zkc.Compiler.CheckedPlan.decoded_unique`, `Zkc.Source.bindInputs_exact` | Consumer source/candidate, actual ordered bound inputs, same interpretation; O: native FFI/order/domain resolution and erasure |
| [REAL-04](../realization/codecs.md#codec-domains), [round trip and faithful decoding](../realization/codecs.md#round-trip-and-faithful-decoding), [fixed width scalar example](../profiles/realization/scalar-bytes.md#fixed-width-scalar-codec) | D: `Zkc.Source.Format.Codec`; T: `Zkc.Realization.ByteEncoding.little_value`, `Zkc.Realization.ByteEncoding.be_reencode`, `Zkc.Protocols.ScalarBytecode.Codec.scalar_complete`, `Zkc.Protocols.ScalarBytecode.Codec.scalar_faithful`, `Zkc.Protocols.ScalarBytecode.Codec.words_faithful`, `Zkc.Realization.JsonArrays.checkJson_iff`, `Zkc.Protocols.BackendProfiles.representation_unique`, `Zkc.Polynomial.Quadratic.coefficients_injective` | Width bound for numeric inverse; fixed scalar modulus; arbitrary-success suffix law; sufficient JSON fuel and exact chosen request; coefficient dimension fixed; O: each actual native codec |
| [REAL-05](../realization/codecs.md#complete-receive-results), [input boundaries and capacity](../realization/codecs.md#input-boundaries-and-capacity) | D: `Zkc.Protocols.ScalarBytecode.Execution.effect`, `Zkc.Protocols.ScalarBytecode.Endpoint.ReadPacket`; T: `Zkc.Protocols.ScalarBytecode.Execution.read_value_agrees`, `Zkc.Protocols.ScalarBytecode.Execution.handler_simulation`, `Zkc.Protocols.ScalarBytecode.Execution.interpreted_run_simulation`, `Zkc.Protocols.ScalarBytecode.Endpoint.read_packet_step`, `Zkc.Protocols.ScalarBytecode.Endpoint.onRead_error_retains_state` | All bytes under selected pure hash, read bound and cursor/tail relation; pure decoder projection forgets failed consumption; O: actual receive/FFI execution |
| [REAL-06](../realization/representations.md#algebra-and-provider-correspondence) | T: `Zkc.Transformations.EncodingReuse.cache_encoding_preserves`, `Zkc.Transformations.EncodingReuse.encoder_saving`, `Zkc.Protocols.ScalarBytecode.Suppliers.cursor_represents`, `Zkc.Protocols.ScalarBytecode.Suppliers.counted_represents` | Same pure encoder/absorb/draw and local continuation; encoder invocation count only; selected supplier relation; O: algebra, native entropy and actual distribution laws |
| [REAL-07](../realization/representations.md#storage-and-ownership) | D: `Zkc.Modules.FactorState.World`, `Zkc.Modules.FreshAllocation.Registered`; T: `Zkc.Modules.Allocation.chosen_fresh`, `Zkc.Modules.FreshAllocation.kept_sound`, `Zkc.Modules.ImmutableCache.rebind` | Good actual pool and registered retained names; immutable provider agreement at occupied keys; O: native buffers, aliases, generations and quiescence |
| [REAL-08](../realization/representations.md#capacity-and-progress) | T: `Zkc.Compiler.CheckedPlan.calls_bounded`; O: actual native capacity/admission/progress policy | Uniform operation-call bound and actual checked plan; does not bound machine arithmetic, kernel time, byte sizes or all allocations |
| [REAL-09](../realization/representations.md#completion-and-atomicity) | T: `Tests.Simulation.failed_write`, `Tests.Simulation.rolled_back_failure_rejected`, `Tests.Simulation.missing_observation_rejected`, `Tests.Simulation.different_stop_rejected` | Mathematical complete-result countermodels; O: native completed/interrupted distinction and synchronous ownership recovery |
| [REAL-10](../profiles/realization/instruction-machine.md#embedded-machine-exits) | D: `Zkc.Realization.InstructionSequence.Exit`, `Zkc.Realization.InstructionSequence.source`, `Zkc.Realization.InstructionSequence.resume`; T: `Zkc.Realization.InstructionSequence.execution_exact`, `Zkc.Realization.InstructionSequence.run_append`, `Zkc.Realization.InstructionSequence.flatten_run_blocks`, `Zkc.Protocols.ScalarBytecode.Execution.no_incomplete_halt` | Explicit machine exit returned as data; concatenation needs no primitive incomplete halt; bytecode instance supplies that law; no outer stopped resumption |
| [REAL-11](../realization/representations.md#admission-and-custody) | D: `Zkc.Compiler.CheckedArtifact`; T: `Zkc.Compiler.CheckedPlan.decoded_unique`; O: retained immutable native artifact and invocation binding | Actual request/candidate; no generic native custody or parser theorem follows |
| [REAL-12](../conventions.md#conformance-claims) | T: `Zkc.Protocols.ScalarBytecode.Suppliers.cursor_run`, `Zkc.Protocols.ScalarBytecode.Suppliers.counted_run`; O: implementation/build/trust inventory and actual differential validation | Complete mathematical runs under same hash and supplier relation; counter instrumentation hidden by declared relation; no native universal claim |

## Binding and artifact clauses

| Clause | Formal correspondence | Actual hypotheses and limits |
|---|---|---|
| [BIND-01](../realization/artifacts.md#consumer-selected-subject) | D: `Zkc.Compiler.Request`, `Zkc.Compiler.CheckedArtifact`; T: `Zkc.Compiler.CheckedPlan.decoded_unique` | Retained source request independent of proposed target; same elaboration/type interpretation |
| [BIND-02](../realization/artifacts.md#interpretation-closure) | D: `Zkc.Compiler.DefinitionRef`, `Zkc.Compiler.CompilationContext`; O: actual interpretation closure and native installed resolver | Name/revision equality is metadata equality; direct checker quantifies over one actual shared meaning |
| [BIND-03](../realization/artifacts.md#identity-purposes) | D: `Zkc.Modules.Factor.Key`, `Zkc.Modules.FactorState.World`, `Zkc.Modules.ImmutableCache.Valid`; O: distinct live/probability/authority meanings | Key validity is relative to actual source/world/provider; no universal identity law |
| [BIND-04](../realization/artifacts.md#premise-preserving-reuse) | T: `Zkc.Modules.FactorState.means_frame`, `Zkc.Modules.FactorState.survivors_valid`, `Zkc.Modules.ImmutableCache.rebind`; O: native dependency tracking | Actual unchanged semantic referents; new provider agrees at occupied keys; no arbitrary digest-based rebinding |
| [BIND-05](../realization/artifacts.md#lifecycle-and-release) | O: artifact lifecycle, authentication and observer release policy | No generic sealing or cryptographic content-authentication theorem; security/release clauses supply additional experiment obligations |
| [BIND-06](../realization/artifacts.md#artifact-envelopes) | D: `Zkc.Compiler.Candidate`, `Zkc.Compiler.CheckError`, `Zkc.Compiler.metadataError`; O: future profile extensions | Current explicit semantic fields and fail-closed profile checks; optional metadata does not acquire a semantic role automatically |
| [BIND-07](../realization/artifacts.md#exact-retained-content) | D: `Zkc.Source.Format.parse`, `Zkc.Source.Format.decodeProgram`, `Zkc.Compiler.ArtifactFormat.request`, `Zkc.Compiler.ArtifactFormat.candidate`; T: `Zkc.Compiler.Plan.decode_erase` | Exact tagged-array shapes and selected codecs; finite depth/byte/number parsing policy; typed erase round trip; O: native parser correspondence and canonical byte identity |
| [BIND-08](../realization/artifacts.md#requirement-disposition) | D: `Zkc.Compiler.metadataError`, `PIR.Properties.Conditional`, `PIR.Properties.Check`; O: installed evidence/trust/guard disposition | Current artifact rule accepts no introduced requirements; a permitted requirement remains unsupported; executable checking assumptions are separate |
| [BIND-09](../profiles/compiler/direct-plan.md#format-parameters), [control grammar](../profiles/compiler/direct-plan.md#control-grammar), [envelope grammar](../profiles/compiler/direct-plan.md#envelope-grammar), [context validity and accepted metadata](../profiles/compiler/direct-plan.md#context-validity-and-accepted-metadata), [artifact checking and execution binding](../profiles/compiler/direct-plan.md#artifact-checking-and-execution-binding), [text parsing and limits](../profiles/compiler/direct-plan.md#text-parsing-and-limits) | D: `Zkc.Compiler.formatVersion`, `Zkc.Compiler.semanticsVersion`, `Zkc.Compiler.completeExecution`, `Zkc.Compiler.checkCandidate`; T: `Zkc.Compiler.lower_correct` | Direct lowering and identical actual interpretation; metadata strings, versions, declaration validity and actual source formation; no native resolver or new rule codec |

## Controls

[`Zkc.Realization.Family.run_relates`](../../../formal/Zkc/Realization/Family.lean)
joins actual related ingress and selected member executions through
`Execution.Relates.follow`. `Family.Admitted.selected_at` separately requires
actual residual-phase compatibility. `Tests.FamilyRepresentation` covers a stored
input representation, ingress effects and a phase mismatch despite valid inputs.
[`Zkc.Realization.Iteration`](../../../formal/Zkc/Realization/Iteration.lean)
provides represented continuation transport and deployment closure; its tests
relate a logical count to a different controller type carrying that count in its
actual handler state.

`Tests.Simulation` covers returned handles, composition, stale contents, failed
writes, omitted events and distinct stops. `Tests.SourcePlan` rejects changed
metadata/source/candidates and even permitted-but-unsupported requirements.
`Tests.InstructionSequence` refutes block resumption when a primitive halts
incomplete. `Tests.ScalarBytecode.OneRound` checks actual failed consumption,
source-occurrence sensitivity and ordered input changes;
`Tests.ScalarBytecode.BlockAdapter` distinguishes premature absorption despite
an equal failure verdict. Existing encoding controls exercise short and
noncanonical words.

## Profiles

The concrete [instruction machine](../profiles/realization/instruction-machine.md)
and [scalar-byte codec/receive](../profiles/realization/scalar-bytes.md) are
profiles outside the common law chapters. An external optimized envelope is
an implementation obligation, not an extension of the current direct decoder.

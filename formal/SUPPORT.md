# Formal capability support

This page records the supported statements, their concrete consumers and their
limits.

The library supplies finite module contraction and ordered folding laws, cubic
Sumcheck coefficients, range residual/parent identities and conditional integer
bounds. The [import table](README.md#use) identifies their reusable modules.
Logical reference execution now includes nominal vectors, polynomials and
Ristretto; group/PCS/transcript replies remain an explicit trusted boundary.
This expands neither the bounded physical-accounting proof nor whole-protocol
security claims.

The semantic adoption adds the component, acceptance, input-binding,
observation-summary and contextual preparation APIs below.

## Protocol families and controllers

Count-parametric common/participant/role syntax retains resolved `Nat` meaning.
Symbolic dimension instantiation preserves syntax size and commutes with both
projections, including stored definitions. Complete ingress retains failures and
role-knowledge obligations. Runtime-symbolic native common protocols are not
implemented; native carriers still contain resolved counts.

`Family.Admitted.selected_at` requires the selected member's initial phase to
match an interpretation of the actual ingress residual state; member admission
alone does not establish that match or ingress conformance.
`SelectsReady` and `Admitted.selected_ready` connect a proved domain-wide ingress
postcondition to admission at that actual phase. `run_proc` identifies finite
process ingress with ordinary sequencing. Maintained examples bind ingress seed
values into stored argument ports, resolve symbolic stored callees and execute
configuration-dependent input types. Role delivery remains a separate premise.
`Zkc.Realization.Family.run_relates` composes related actual ingress with
represented member execution, retaining ingress failures and observations.

The Std-only iteration API proves prefix composition, terminal stability,
per-body admission/bound transport and complete simulation. A Rust controller
implements resumable finite prefixes with explicit deployment closure. The
`iteration-reference` differential corpus covers pending, success, all five stop
reasons, split resumption with carried values, explicit closure, state and events.
These are tests, not a native refinement proof. Host resource
retirement is tested through real native frames and consuming failures; there is
no Lean proof of the Rust resource store. Finite probability laws preserve stopped
mass and bound retry tails under explicit reached-law assumptions. They prove no
concrete protocol's retry rate, eventual production or cryptographic security.

`evaluateM` reuses `Proc.runM` for actual finite prefixes, with resumption and
pure-handler embedding laws. Outer effects must still supply complete records
and the actual probability law; an outer exception is not an inner stop.

`Zkc.Realization.Iteration` extends transport to different continuation/result
types with state-dependent relations. `approximate_blocks` proves finite grouping
at a translated horizon; it does not preserve an unchanged deployment cap.
`within_approximate_of_invariant` needs a bound only on invariant-admitted
continuations, with all-reply preservation at each exit. Mutable native callback
captures remain the caller's responsibility across resumption. Maintained
countermodels cover phase-mismatched ingress and iteration re-entry, typed hostile
continuation replies, reset callbacks, persistent hidden coins and insufficient
observations for future transitions.

## Maintained APIs and actual consumers

The authored interactive implementation uses the
[source-role connection](design/role-execution.md), scoped source-cut and resource
laws, and the [committed Sumcheck connection](design/committed-sumcheck.md).
`Tools.Interactive` is a separate executable portable checker/source interpreter.
Its concrete artifact checks and native differential comparisons do not prove
raw-to-typed elaboration or native refinement. See the
[running compiler guide](../docs/compiler/interactive-execution.md) for the
actual source → MLIR → admitted Rust route and its boundaries.

The explicit-binding path independently checks original generic definitions,
requirements, partial configurations, literal normalization, local representation
conversions and common participant control. It returns source port/call maps used
by the actual Rust host. See [generic validation](../docs/compiler/library-design/validation.md).
This structural checker reifies straight-line source locals into typed regions
through ordered result bundles; admitted controlled locals instantiate finite
typed branches/iterations after reading runtime bounds (see [scope](design/local-control.md)).
Generic reference execution runs those computations under independent mathematical/RNG/nonce/transcript-state services
and explicit group/hash/PCS contracts, with interpreter-owned PCS custody. A
separate source-checked local physical interpreter compares payload budgets and
consuming failures. General resource-view correspondence, raw elaboration
adequacy and construction integration remain unfinished. None follows automatically from typed substitution or the bundle
adapter's execution theorem.

| Capability | Definitions and laws | Consumer and scope |
|---|---|---|
| Generic static requirements and type substitution | [Requirements](Zkc/Source/Requirements.lean), [TypeInstantiation](Zkc/Source/TypeInstantiation.lean), [controls](Tests/TypeInstantiation.lean) | Proof-producing finite derivation checking and actual structured type substitution preserve their stated meanings, including stopped executions. Native requirement certificates have independent Lean and Rust replay, including versioned pure-application congruence. Raw elaboration, implementation selection and native refinement have separate scope; see [profile](../docs/spec/profiles/source/generic-definitions.md) |
| Runtime-selected finite local control | [FiniteControl](Zkc/Source/FiniteControl.lean), [adapter scope](design/local-control.md) | Admitted runtime bounds, zero/inverted/count/index laws, existing Region.iterate denotation and a uniform semantic call bound. Executable adapters check both branches and actual candidates; raw adequacy and native refinement remain unproved |
| Ordered multi-result local operations | [ResultBundle](Zkc/Source/ResultBundle.lean), [source reifier](Tools/Interactive/TypedLocal.lean), [adapter controls](Tests/ResultBundle.lean), [reification controls](Tests/TypedLocal.lean) | Unit and heterogeneous results use the existing region carrier with pure projections. Invocation preserves complete operation execution, including stops and events. Straight-line generic preparation retains actual typed locals; controlled locals use runtime-selected finite instantiation. The raw reifier has executable controls, not an adequacy theorem; affinity is checked separately and bundles do not model physical allocation |
| Portable generic source correspondence | [formation](Tools/Interactive/GenericSource.lean), [configurations](Tools/Interactive/Configuration.lean), [shared local relation](Tools/Interactive/LocalValidation.lean), [whole-source checking](Tools/Interactive/GenericValidation.lean) | Independent bounded formation and source-owned specialization; exact local conversions and original control are checked against actual native output. Returned maps support shared code and original host ports. Executable structural checking, not a raw-to-typed or native refinement theorem |
| Generic reference execution | [shared control](Tools/Interactive/Control.lean), [source interpreter](Tools/Interactive/GenericReference.lean), [typed local execution](Tools/Interactive/ReferenceRuntime.lean), [resource services](Tools/Interactive/ReferenceResources.lean), [controls](Tests/GenericReference.lean), [native comparison](../crates/zkc-tools/tests/generic_reference.rs) | Original source executes independently of native participants. Field/polynomial math, RNG consumption, nonce stage transitions, transcript history/canonical origins/field reduction, full nominal types and exact external G1/hash/PCS requests are exercised. Native comparisons cover ordered messages and primitive logs, distinct role results, actual terminal cuts, polynomial domain errors, nested calls/loops and mixed representations. Logical operation locations are finer than native local-call stop sites. PCS custody retains immutable originals; evaluations and key/rank/receiving selection are independently checked. G1/PCS equations and hash bytes are conditional provider evidence; physical accounting is a separate row below |
| Participant lifecycle reference | [source suspension and schedule](Tools/Interactive/ReferenceControl.lean), [in-process controls](Tests/ReferenceLifecycle.lean), [cross-build controls](../tests/execution/test_participant_lifecycle.py) | Independent original-source traversal retains each role's iteration allowance and frame lifecycle. Completed roots keep returned units; stopped or cancelled roots retire units, including pre-body ingress failure. Reference-fixture postflight errors do not reopen completed roots. Native comparison is bounded; peer ingress event prefixes can differ on failure, and no general scheduler or resource-store refinement theorem is claimed |
| Checked physical local execution | [Interpreter](Tools/Interactive/PhysicalLocal.lean), [native comparisons](../crates/zkc-tools/tests/generic_reference/physical.rs) | Original-source checking precedes selected local execution. Mathematical contracts, representation crossings, retained-payload charges, output budgets and consuming failures are compared with the native runner. Explicit input capacity and successful exact-capacity allocation are premises. Single-root/local/return scope; view counts do not establish frame membership, and no native adequacy theorem is claimed |
| Physical values in compact regions | [RegionSimulation](Zkc/Realization/RegionSimulation.lean), [physical table client](Examples/TablePhysical/README.md) | Generic local-to-region execution refinement with final-state value relations and preservation of all old represented values. The two-field client checks actual lazy/materialized candidates, logical input coverage and both installed local phase policies through call instrumentation. Native allocation/progress, broader endpoint policies and releasing stores remain separate obligations |
| Checked logical operation folding | [RegionFolding](Zkc/Compiler/RegionFolding.lean), [table law](Examples/TableProtocol/Optimization.lean), [controls](Tests/TableOptimization.lean) | Generic alias traversal and source-relative folded-body comparison preserve complete procedures. Identical-endpoint interpolation composes with physical checking and original-source phase admission for every handler. Guarded reuse, effectful rewrites and native implementation proofs remain separate |
| Component connections and replacement | [RelationComposition](Zkc/Semantics/RelationComposition.lean) | [Non-machine component client](Examples/ComponentConnections.lean) uses different proof/signature boundaries and re-encodes a key; [controls](Tests/RelationComposition.lean) check incompatible witnesses, missing representation coverage and circular removal of checks. Contextual replacement preserves the connected relation, not complete native execution |
| Finite obligation closure | [Obligations](Zkc/Semantics/Obligations.lean) | Ordered multi-premise derivations cover independently supplied source requirements; rules compose through actual available facts and permit reuse. Soundness assumes terminal truth and each rule's law, with explicit bad events. [Controls](Tests/Obligations.lean) include whole-chain deletion, subject/context substitution, cycles and accepted but unsound rule syntax. Native differential evidence concerns finite closure; actual-body binding and cryptographic laws remain separate |
| Application arithmetic boundaries | [BoundedResidues](Zkc/Algebra/BoundedResidues.lean), [Pedersen](Zkc/Protocols/Pedersen.lean), [Schnorr](Zkc/Protocols/Schnorr.lean) | Total bounds recover integer balance and word-addition meaning from field equations. Actual shared openings give the excess identity; different challenges at one nonce give the two-response extraction equation. Controls exhibit modular-wrap and incompatible existential-opening counterexamples. These laws do not prove native ISA adequacy, nonce generation, joint extraction or either complete application's security |
| Acceptance and exposed outputs | [Acceptance](Zkc/Realization/Acceptance.lean) | [Decision and deferred-output clients](Examples/Acceptance.lean) preserve selected source outputs for every satisfying witness. [Opening reduction](Examples/OpeningReduction/Acceptance.lean) binds the actual source residual and complete three-claim bundle; satisfying forged reports cannot discharge the following opening obligations. Reduction soundness and cryptographic security remain separate |
| Direct Sumcheck acceptance realization | [Acceptance](Zkc/Protocols/Sumcheck/Acceptance.lean), [controls](Tests/SumcheckAcceptance.lean) | Actual staged source, original polynomial and ordered field tape bind a direct evaluator. `honest_complete` reuses source completeness at arbitrary arity over a commutative semiring; executable Z/5Z controls include non-Boolean challenges and wrong object/point/value. This is not a PCS or native implementation |
| Connected Sumcheck residual | [Connection](Zkc/Protocols/Sumcheck/Connection.lean), [controls](Tests/SumcheckConnection.lean) | The actual round process exposes the full ordered point and value, connected to direct evaluation of the original polynomial. Both use common acceptance realization; the closed connection equals complete source acceptance for every typed tape. Includes swapped-coordinate rejection and characteristic-two completeness |
| Contextual immutable preparation | [Preparation](Zkc/Semantics/Preparation.lean), [emission bridge](Zkc/Semantics/Preparation/Emission.lean) | One arbitrary external signature with dependent replies; valid private caches and equal external states preserve outcomes and ordered external events, including state changes on failure. The emission bridge retains reference accounting. [Controls](Tests/ContextualPreparation.lean) distinguish provider/caller/cost changes and cache observers |
| Prepared complete Sumcheck source | [Preparation](Zkc/Protocols/Sumcheck/Preparation.lean), [integration](Tests/SumcheckPreparation.lean) | Actual cached evaluation drives the next claim; all typed source bodies resolve to their original meanings under any selected construction. Fresh acceptance connects to the direct residual evaluator; framed runs preserve the initial statement, actual query attempts, stops and state. No native profitability or FS security claim |
| Advertised refinement inputs | [InputBinding](Zkc/Compiler/InputBinding.lean), [controls](Tests/InputBinding.lean) | An actual partial input map covers the advertised source domain and applies refinement to its selected target inputs; empty initial relations and extra accepted target inputs are distinct controls. Coverage is not native progress or full target-domain adequacy |
| Sound observation summaries | [Observation](Zkc/Compiler/Analysis/Observation.lean), [controls](Tests/ObservationAnalysis.lean) | Sound use, weakening and conjunction for the same actual observation; the controls instantiate these laws with existing factor merging. The sampling-locality model below also instantiates this interface. Unknown summaries remain sound after erasure but cannot recover exact values or justify missing checks; locality controls cover erased configuration and modular information loss |
| Structural sampling analysis | [Sampling](Zkc/Compiler/Analysis/Sampling.lean), [SamplingLocality](Zkc/Compiler/Analysis/SamplingLocality.lean) | Separate draw, direct-reception, provider-history and unknown sets; monotone transfer and adversarial reception boundaries. Expression evaluation factors through its input support, and absence of direct reception discharges a `SummarySound` locality obligation when entry values and provider replies are fixed; ordinary sampler arguments remain in its support. [Controls](Tests/SamplingAnalysis.lean) include a peer-controlled bound counterexample. This does not prove native extraction correct, sampler independence, exact transcript-byte absorption or a Fiat–Shamir theorem |
| Staged interpretation | [Interpretation](Zkc/Semantics/Interpretation.lean), [monadic fusion](Zkc/Semantics/MonadInterpretation.lean), [structured source](Zkc/Source/Interpretation.lean) | Identity, composition, binding and complete execution through public loops; `run_interpret_related` relates different states and observations under an explicit per-operation premise, including stopped post-states; the round constructions use these laws |
| Construction sequencing and rebasing | [Interpretation](Zkc/Semantics/Interpretation.lean), [Execution](Zkc/Semantics/Execution.lean), [controls](Tests/ConstructionSequencing.lean) | Separately constructed components retain residual state. Interchange needs an operation square; rebasing needs suffix equivalence. An actual framed Sumcheck client distinguishes resetting the transcript from lawful sequencing |
| Typed region sequencing | [Composition](Zkc/Source/Composition.lean), [clients](Tests/SourceComposition.lean) | Capture-safe source sequencing denotes semantic binding for every interpretation; branches, result aliases, bounded recurrence and suffix failure retain complete executions |
| Shared source definitions | [Definitions](Zkc/Source/Definitions.lean), [reference renaming](Zkc/Source/DefinitionRenaming.lean), [inlining](Zkc/Compiler/DefinitionInlining.lean), [controls](Tests/SourceDefinitions.lean) | Acyclic stored bodies and typed calls; capture-safe inlining preserves complete execution for arbitrary primitive interpretations/handlers. Call-boundary observations, symbol/instance resolution and participant projection remain separate |
| Defined Sumcheck source | [Definitions](Zkc/Protocols/Sumcheck/Definitions.lean), [controls](Tests/SumcheckDefinitions.lean) | Stored verifier source equals the existing staged run, including original polynomial, adaptive messages, round loop, terminal and stopped state/events; no new PCS or security theorem |
| Located source calls | [Execution](Zkc/Source/LocatedExecution.lean), [controls](Tests/LocatedCalls.lean) | Different state/event types per role; exact active state, peer-state frame, local-view factorization and complete stopped origin. Local-effect conformance is separate from raw execution; whole Sumcheck receive cannot hide in an admitted local block |
| Resolved common protocols | [Syntax](Zkc/Source/Protocol/Syntax.lean), [meaning](Zkc/Source/Protocol/Meaning.lean), [runtime](Zkc/Source/Protocol/Execution.lean), [controls](Tests/CommonProtocol.lean) | Role-owned argument/result ports, acyclic protocol calls, selected bindings, independent reception and fixed public loops; complete call/send/receive stop laws and exact child/direct execution equality. Global choice, role remapping, portable resolution and participant generation remain open |
| Scheduled participant lowering | [Projection](Zkc/Compiler/Participant/Projection.lean), [execution](Zkc/Compiler/Participant/Execution.lean), [controls](Tests/ParticipantProjection.lean) | All current common-source constructors and actual stored callees preserve complete execution through separate local/send/receive requests, role-local inputs and a typed packet schedule. It is one scheduled target, without independently deployable role modules, global choice or an asynchronous progress theorem |
| Independent source and target roles | [direct source meaning](Zkc/Source/Protocol/Role.lean), [target projection](Zkc/Compiler/Role/Projection.lean), [runner](Zkc/Compiler/Role/Runner.lean), [execution](Zkc/Compiler/Role/Execution.lean); [scope](design/role-execution.md) | All current common-source constructors and actual stored tables have separately defined role meanings with exact projection equality for arbitrary local/peer replies. Focused inputs contain no foreign values. Includes real local definitions, own stops, foreign-leaf incomplete, missing-ingress suspension and completed-strategy runner correspondence. [Projection](Tests/RoleProjection.lean), [independent heterogeneous target](Tests/RoleTarget.lean), [uninhabited foreign input](Tests/RoleIsolation.lean) controls. No native, resource-admission or universal joint/open theorem |
| Shared control agreement | [Agreement](Zkc/Source/ControlAgreement.lean), [controls](Tests/LocatedCalls.lean) | Exact nonempty-list agreement check over actual optional values; accepted Bool choices determine actual typed local branches. No inferred public input, communication, global branch merge or larger projection theorem |
| Interpreted admission | [InterpretationAdmission](Zkc/Semantics/InterpretationAdmission.lean), [summary translation](Zkc/Source/PhaseAdmissionInterpretation.lean) | Relates entry and returning phases, transports conformance and uniform call bounds; checked summaries can retain their source abstraction |
| Changed-source checking | [Refinement](Zkc/Compiler/Refinement.lean), [Transformation](Zkc/Compiler/Transformation.lean), [Horner](Zkc/Compiler/Arithmetic/Horner.lean) | A concrete rule checks the actual source and target plan under semiring laws; tests cover two fields, shifted operands, loops, aborts and candidate/source mismatches |
| Algebraic-round source | [Source](Zkc/Protocols/AlgebraicRounds/Source.lean) | Typed message/claim/check/evaluation operations and public repetition; exact denotation, phase, return and bound proofs for arbitrary quadratic messages |
| Fresh and framed constructions | [Construction](Zkc/Protocols/AlgebraicRounds/Construction.lean), [Fresh](Zkc/Protocols/AlgebraicRounds/Fresh.lean), [Framed](Zkc/Protocols/AlgebraicRounds/Framed.lean) | One actual source; distinct construction effects; independently recursive references; adaptive messages and retained failed query state |
| Available role inputs | [LocalInputs](Zkc/Source/LocalInputs.lean), [Endpoints](Zkc/Protocols/AlgebraicRounds/Endpoints.lean) | Actual declared input/capture resolution, complete local execution equality, prover reaction and verifier evaluation; foreign captures and unavailable future/provider inputs are rejected |
| Public payload shape and checked local arithmetic | [MessageSchema](Zkc/Source/MessageSchema.lean), [LocalArithmetic](Zkc/Source/LocalArithmetic.lean), [Dag](Zkc/Compiler/Arithmetic/Dag.lean) | Executable public shape formation and exact natural-word decoding admit arbitrary shape-valid payloads; local input checking supplies evaluator confinement, and DAG certificates bind actual source/site and available inputs |
| Finite local prover language | [Code](Zkc/Protocols/Sumcheck/LocalProver/Code.lean), [Source](Zkc/Protocols/Sumcheck/LocalProver/Source.lean), [Admission](Zkc/Protocols/Sumcheck/LocalProver/Admission.lean) | Explicit inputs, four local registers, local coins and a terminal quadratic message; pure reachability, public call bounds and checked endpoint admission build without ArkLib |
| Captured program composition | [Selection](Zkc/Protocols/CapturedPrograms/Selection.lean), [Installation](Zkc/Protocols/CapturedPrograms/Installation.lean), [Inputs](Zkc/Protocols/CapturedPrograms/Inputs.lean), [Probability](Zkc/Protocols/CapturedPrograms/Probability.lean) | A concrete paired service/local-prover payload exercises whole-tree capture checking, namespace installation, role binding and publication/history transport; it is not a generic frontend requirement |
| Indexed product-family source | [Basic](Zkc/Protocols/Sumcheck/ProductFamily/Basic.lean), [Indexed](Zkc/Protocols/Sumcheck/ProductFamily/Indexed.lean), [Typed](Zkc/Protocols/Sumcheck/ProductFamily/Typed.lean) | The family `product(coordinates) + firstCoordinate`, arbitrary indexed environments, prefix locality and typed-check elaboration retain their actual source-to-terminal equations |
| Early and deferred checking | [Early](Zkc/Protocols/AlgebraicRounds/Early.lean), [EarlySource](Zkc/Protocols/AlgebraicRounds/EarlySource.lean), [BlockEvaluation](Zkc/Protocols/AlgebraicRounds/BlockEvaluation.lean) | Actual early-stop source and checked block evaluator preserve complete early execution; deferred checking agrees on verdicts but can consume more challenges after rejection |
| Bound expression inputs and allocation | [closure elaboration](Zkc/Source/Elaboration.lean), [factor binding](Zkc/Modules/FactorBinding.lean), [allocation](Zkc/Modules/Allocation.lean), [fresh allocation](Zkc/Modules/FreshAllocation.lean), [scoped compilation](Zkc/Compiler/FactorScopes.lean), [registered compilation](Zkc/Compiler/FreshAllocation.lean) | Actual captured values, ordered-prefix installation, namespace separation, failed allocation and registered-name preservation; retained callers now use maintained imports |
| Factor polynomial laws | [Factors](Zkc/Polynomial/Factors.lean) | Contraction, multiplicity-preserving sums of products, scale hoisting and final pending-challenge application; Boolean equality alone does not justify polynomial replacement |
| Randomized joint release | [Disclosure](Zkc/Probability/Disclosure.lean), [controls](Tests/RandomizedDisclosure.lean) | Actual normalized marginals and one coupling preserving the whole artifact/runtime pair; projection and event transport; independent marginal secrecy is insufficient |
| Persistent probability | [ProductTape](Zkc/Probability/ProductTape.lean), [ConditionalTape](Zkc/Probability/ConditionalTape.lean), [FiniteKernel](Zkc/Probability/FiniteKernel.lean) | Actual PMF product execution, complete residual state, pre-draw conditional laws and rational joint-kernel inequalities; no scalar-protocol or external-library import |
| Finite-event concentration | [Concentration](Zkc/Probability/Concentration.lean), [EmbeddedRoots](Zkc/Polynomial/EmbeddedRoots.lean), [one-round application](Zkc/Protocols/Sumcheck/ProductFamily/OneRound.lean) | Cardinality times point-mass bound and injective-domain polynomial root bound; the scalar application needs a false claim, and probability interpretation needs its actual sampling premises |
| Execution representations and locality | [InstructionSequence](Zkc/Realization/InstructionSequence.lean), [simulation](Zkc/Realization/InstructionSimulation.lean), [AdaptiveClient](Zkc/Semantics/AdaptiveClient.lean), [Locality](Zkc/Semantics/Locality.lean), [ByteEncoding](Zkc/Realization/ByteEncoding.lean) | Instruction and adaptive-client executions embed into `Proc`; common relational transport preserves exact terminal data, state and events. View descent requires fiber constancy and representative premises; endian round trips do not prove protocol codecs |
| Block analysis and replacement | [Analysis](Zkc/Compiler/Blocks/Analysis.lean), [Typing](Zkc/Compiler/Blocks/Typing.lean), [Rewriting](Zkc/Compiler/Blocks/Rewriting.lean), [StateRefinement](Zkc/Compiler/Blocks/StateRefinement.lean) | Backward demand, projected whole-block keys, ordered exports, checked arithmetic and interpretation transport; an auxiliary reference block language with explicit observer and algebraic premises |
| Bounded physical caches | [BoundedCache](Zkc/Modules/BoundedCache.lean), [block consumer](Zkc/Compiler/Blocks/BoundedCache.lean) | Finite slots, full-key comparison, collision replacement and bypass preserve the actual program result; weighted primitive work excludes lookup/storage overhead |
| Session phase framing | [Sessions](Zkc/Semantics/Sessions.lean) | Retains the existing selected/other-session phase and actual-call laws; generic [Boundary](Zkc/Semantics/Boundary.lean) now builds without Mathlib |
| Immutable preparation | [ImmutableCache](Zkc/Modules/ImmutableCache.lean), [Memoization](Zkc/Transformations/Memoization.lean), [costs](Zkc/Modules/Preparation.lean), [complete execution](Zkc/Semantics/Preparation.lean) | Shared cache-validity laws, adaptive consumers, cost accounting and retained stopped states; existing source/session consumers use the maintained names |
| Encoding reuse | [EncodingReuse](Zkc/Transformations/EncodingReuse.lean), [message shape](Zkc/Protocols/AlgebraicRounds/MessageShape.lean), [interpolation](Zkc/Polynomial/LinearInterpolation.lean) | Reusing already encoded messages preserves the supplied deterministic provider state, challenge, absorption sequence and final payload; encoder-call counting is separate from runtime measurement and freshness |
| Interpreted table preparation | [TablePreparation](Zkc/Source/TablePreparation.lean), [bilinear materialization](Zkc/Polynomial/Bilinear/Preparation.lean), [installation](Zkc/Polynomial/Bilinear/Installation.lean), [guarded compilation](Zkc/Polynomial/Bilinear/Compilation.lean) | Total natural-number register code, exact keys and costs; actual residual coefficients establish factor facts, survive allocation framing and feed refusal-preserving inference. Fixed bilinear application, separate from the general field-polynomial representation |
| Atomic commitment sessions | [Execution](Zkc/Protocols/CommitmentSessions/Execution.lean), [Preparation](Zkc/Protocols/CommitmentSessions/Preparation.lean), [Source](Zkc/Protocols/CommitmentSessions/Source.lean) | Two-session commit/open state machine, trace-adaptive schedulers and actual common-source execution. Tables may be shared; coins and messages remain local. Modular-seven controls test the abstraction and make no binding or hiding claim |
| Factor facts and state | [Factor](Zkc/Modules/Factor.lean), [plan inference](Zkc/Compiler/Analysis/FactorReuse.lean), [FactorState](Zkc/Modules/FactorState.lean), [FactorContract](Zkc/Modules/FactorContract.lean), [FactorProgram](Zkc/Compiler/FactorProgram.lean) | Existing fact, demand, frame, availability and outcome-specific transfer claims migrated with their actual consumers; generic closure needs only Std |
| Ordered table source adequacy | [Multilinear](Zkc/Polynomial/Multilinear.lean), [TableExpression](Zkc/Polynomial/TableExpression.lean), [TableSource](Zkc/Protocols/Sumcheck/TableSource.lean), [controls](Tests/TableSource.lean) | Actual cell/index bijection, all-point extension/product equality, repeated occurrences, accepted degree-two compilation and original-expression terminal/soundness premises; longer products explicitly refused by this profile; no native decoder or efficient table prover theorem |
| Fixed polynomial and materialization | [Quadratic](Zkc/Polynomial/Quadratic.lean), [coordinates](Zkc/Polynomial/Coordinates.lean), [PolynomialPreparation](Zkc/Modules/PolynomialPreparation.lean), [compiler law instance](Zkc/Compiler/PolynomialPreparation.lean) | Arbitrary arity, per-coordinate degree at most two, fixed ordered prefix, independently recomputed evaluation and actual residual-coefficient installation |
| Correlation and adaptive randomness | [probability](Zkc/Probability/AdaptiveTape.lean), [setup](Zkc/Protocols/CorrelatedSetup/Basic.lean), [service](Zkc/Protocols/CorrelatedSetup/Service.lean) | Migrated joint setup/mask/adaptive coupling and finite-mass results with existing consumers; generic probability has no protocol dependency |
| Correlated-service preparation | [Preparation](Zkc/Protocols/CorrelatedSetup/Preparation.lean), [tests](Tests/CorrelatedPreparation.lean) | The same checked transformation interface selects cached coefficients while preserving every response, stop, event and remaining coin; actual execution transports to the joint publication/history simulation |
| Complete interactive Sumcheck | [source](Zkc/Protocols/Sumcheck/Source.lean), [security](Zkc/Protocols/Sumcheck/Security.lean), [admission](Zkc/Protocols/Sumcheck/Admission.lean) | Fixed degree-two-per-coordinate polynomial, actual input and terminal, arbitrary adaptive prover callbacks, independent uniform challenges, perfect completeness and ordinary soundness at most `2*n/card F` |
| Statement-bound framed Sumcheck | [Framed](Zkc/Protocols/Sumcheck/Framed.lean), [encoding](Zkc/Polynomial/Encoding.lean) | Injective fixed-dimension coefficient encoding, actual statement initialization, complete reference execution and retained statement root in every attempted query; typed frames only |
| Composed local Sumcheck endpoints | [Composition](Zkc/Protocols/Sumcheck/Endpoints/Composition.lean), [tests](Tests/SumcheckEndpoints.lean) | Actual bound prover send/react and verifier check/advance/terminal programs; permitted-view locality, Fresh/framed full execution equality and interactive property transfer under synchronous delivery |
| Sumcheck verifier optimization | [Optimization](Zkc/Protocols/Sumcheck/Optimization.lean), [tests](Tests/SumcheckOptimization.lean) | Executes the checked Horner child plan on actual received coefficients and challenges; full parent execution equality transports completeness and soundness with the same adversary |
| Checked factor optimization | [FactorQueries](Zkc/Source/FactorQueries.lean), [FactorOptimization](Zkc/Compiler/FactorOptimization.lean), [tests](Tests/FactorOptimization.lean) | Actual typed source/candidate with terminal equality; module-produced facts, invalidation and unchanged readiness guards; exact complete execution under a preserved binding invariant |

The root execution model, heterogeneous realization relation, typed source,
binding, direct-plan and phase-checking APIs retain their existing contracts.
All retained library capabilities now use maintained modules without `Compat`
or numbered namespaces. The [boundary check](checks/check_library.py) covers the full
owned import closure; the build also audits declaration types and bodies.

The instruction adapter returns the instruction language's `Exit` as data. A
returned `.incomplete` is not a successful protocol result: it can mean list
falloff or an explicit primitive halt. The latter stops before the suffix;
continuation composition must retain that distinction.

`MessageSchema` is a maintained
[message-shape reference client](../docs/spec/profiles/README.md#message-shape-reference-client).
It describes natural-word payload shape, without selecting a Sumcheck byte
format or honest equations. The scalar-byte consumer supplies its trusted
header internally after receiving the three scalar words.
`LocalArithmetic` is an auxiliary first-order source language
whose checker examines both branches and all referenced inputs. The DAG checker
scans raw input instructions, including dead ones, with a proved equivalence to
expanded-node availability. Its total evaluator gives
missing internal references zero semantics; successful source-relative checking
supplies the stronger structural and availability premises. The concrete scalar
range/byte connection is in `ScalarBytecode.CheckedExpression`, outside these
generic modules.

The bilinear and commitment-session clients use the same table interpreter and
immutable preparation laws. Their preserved observer sees results and ordered
protocol events, not work or cache hits. Checked controls retain cost-dependent
scheduling, secret-dependent hits, reordered global traces, cancellation and
fresh-versus-reused coins. Session requests are atomic; these theorems do not
provide asynchronous network projection or cancellation inside preparation.

The generalized preparation API also has [word-valued controls](Tests/PreparationDomains.lean)
and [correlated-service parameter reuse](Tests/CorrelatedPreparation.lean).
Distinct-width word results retain XOR, shift and wide-product meanings.
Reused immutable request parameters still make separate stateful service calls,
retaining both masked responses, exhausted tapes and complete history. The new
interface tests do not extend to a complete Binius protocol.

`Horner.rule` is a real mathematical checker rule with a `Unit` certificate.
The native artifact codec and CLI still admit their existing direct rule.
Selecting a serialized rule, its certificate codec and its interpretation remains
an explicit engineering join. The fixed-object/materialization rule below has its own proved premises.

`FactorOptimization.rule` starts with no supplied facts or availability assertions.
The source's module calls establish them using proved post-state contracts. The
polynomial client discharges those contracts, including a failed overwrite that
changes storage and invalidates a fact. `Proc.run_invariant` retains the
fixed binding through both returned and stopped calls. The equality operation
compares the actual query result with the caller's terminal claim.

The factor rule shares the continuation when both actual fact and availability
transfers agree. Otherwise it specializes to each external Boolean outcome and
can still duplicate syntax exponentially. [Compiler controls](Tests/CompilerComplexity.lean)
prove an `n + 1` syntax bound for the equal-transfer call-chain family and retain
both-result execution checks. This is not a general polynomial-complexity theorem
or a prescription to expand a production CFG exponentially. Loops retain their
direct body and forget analysis facts at exit. A more precise or compact analysis
must supply its own transfer and source-relative correctness law. The contrasting
service client now uses the same immutable-cache law and source/candidate checker.
Its typed syntax stays fixed while its handler and private state change; the
field rule changes the source algorithm. The Sumcheck verifier now executes a checked arithmetic child plan and transports
its security property through complete parent execution equality. This round
evaluation rewrite is separate from the stateful factor rule, as specified in
the roadmap.

The separate [conservative rule](Zkc/Compiler/FactorOptimization/Conservative.lean)
now merges guaranteed fact and availability lists by intersection, retaining one
suffix and the actual external Boolean. It proves complete execution equality
under the same module invariant and post-state laws. Its
[size theorem](Zkc/Compiler/FactorOptimization/Size.lean) proves unchanged
structural node count for every finite source and its actual lowered candidate.
[Controls](Tests/FactorMerge.lean) cover useful shared facts, lost success-only
facts, retained failed writes/events, readiness refusal, original branches,
direct loops, candidate substitution and unequal-transfer chains through 64 calls.
The existing polynomial preparation example falls back to direct evaluation
because its fact is exported only on success. Descriptor bytes, analysis work,
native realization and usefulness across field-table/Merkle clients remain open.

The materialization theorem establishes an algorithmic equality, not a timing
result. The source already requests preparation; the rule reuses its residual
instead of recomputing a later query. Automatic insertion, profitable placement,
native layouts and end-to-end speedups are separate work. Preparation cost obeys
the explicit avoided-work/overhead criterion; memoization can cost more overall.

## Contrasting structure and failure clients

The [Sigma verifier](Tests/ProtocolGenerality/Sigma.lean) retains distinct scalar
and group sorts, three interaction sites and the actual verification equation.
Its generic module-law completeness and source/plan execution theorems require
no polynomial-specific core. The [Merkle verifier](Tests/ProtocolGenerality/Merkle.lean)
retains a public-height path operation and interprets it into ordered node calls;
its fold equation, root/coordinate rejection and failed-node execution are checked.
These are structural and algorithmic clients, not Sigma extraction, commitment
binding or FRI soundness proofs. A complete MPC-view protocol remains unconnected.

The [opening-reduction example](Examples/OpeningReduction/README.md) computes
cubic rounds for three multilinear factors, with arbitrary-round adaptive
ordinary soundness `3n/|F|`. Its typed source returns a scalar/ordered point;
the actual joined consumer returns three opening obligations. A separate theorem
bounds false acceptance by `3n/|F| + ε` under the reached terminal false-opening
event bound. The terminal is currently a Boolean function of the bundle, not a
cryptographic PCS implementation. The nine example modules are in the main audit;
their table/claim types are not yet promoted common APIs. The parallel quadratic
composition's tighter degree-two bound remains useful. No new native or FS
guarantee follows.

[Scoped allocation](Tests/ScopedAllocation.lean) compares conservative and
registered nested compilation against independently specified complete results.
It retains quota/capacity refusal and clobber effects, and shows an incorrect
stale answer when an imported name is used without the stronger registration
premise. Reconciled registration restores the advertised theorem's use.

[Memoization execution](Zkc/Transformations/Memoization/Execution.lean) embeds the
adaptive immutable client in the shared `Proc` signature, with exact result/event
and residual-cache laws. Preservation requires a valid cache. Generic monadic
execution has an additional boundary: an outer exception may return no
`Execution` record. [Outer-effect controls](Tests/OuterEffects.lean) distinguish
that behavior from an inner stop retaining its failed state and emitted prefix.

Two request/emit reference trees remain: `Memoization.Client` and
`Modules.Preparation.Program`. Both embed into the same `PIR.Preparation`
signature, but their evaluators answer different questions. `Client` permits
arbitrary store/bypass policies and has no cost events; `Program` uses always-store
memoization and binds values together with work, saved work and overhead.
They share immutable-cache validity, not an interchangeable accounting theorem.
Keep these reference clients until a native policy/cost consumer warrants a
shared evaluator; do not silently transfer a priced result to another policy.

## Construction and endpoint scope

The retained indexed product-family representation is a separate source client
with its own occurrence map and terminal equation. Its arbitrary-environment
theorems have been preserved; the newer fixed-polynomial completeness theorem
does not silently replace them. The early-round adapter also retains an arbitrary
supplied evaluator, including its existing checked-block consumer.

`CapturedPrograms` checks a concrete payload containing a correlated service and
a local quadratic-message program. The five-capture constraint belongs to that
paired application. It is absent from the standalone local-prover frontend.
The actual probabilistic local execution, verifier, conditional challenge laws
and acceptance consumers are in the separate [ArkLib package](integrations/arklib/README.md).

The algebraic-round component binds its initial count and scalar claim. The
complete `Sumcheck.Framed.run` also binds the original polynomial through an
injective, fixed-order coefficient list and a schema tag. `run_exact` relates
that actual initialized source to the independent reference; `queries_bound`
retains the statement root even in an attempted query whose provider stops.
The typed encoding is injective for the fixed dimension, not a byte codec or
canonicalization modulo polynomial-function equality. Byte encoding, hash/query
interpretation and cryptographic reductions remain distinct obligations.

`Sumcheck.Endpoints.Composition` executes the local bound source programs for
prover send/react and verifier check/advance/terminal. Complete Fresh and framed
execution equality connects their returned values, states, events and stops to
the global source. The interactive completeness/soundness consumer uses this
connection. Locality fixes the interpretation and callbacks independently of
hidden/provider inputs; it does not audit arbitrary host-language closures.
Missing delivered values and foreign private captures fail during binding.
The supplied delivery discipline is synchronous. General endpoint projection,
asynchronous progress and cryptographic noninterference remain separate work.

The provider interface retains failed query state but models total message
receipt and no additional provider-internal events. Fresh security uses the
specified independent uniform tapes; the framed correspondence does not prove
Fiat–Shamir security. Randomized prover soundness currently averages finite
uniform private seeds independent of those tapes.

The finite phase checker now checks compact regions directly, including shared
`bind`, and reuses that algorithm for tree programs through `toRegion`.
`checkRegion_sound` proves conformance and returning coverage without flattening;
[phase tests](Tests/PhaseAdmission.lean) include changed bodies, mixed exits, stops
and certificate codec controls. The [artifact admission join](Zkc/Compiler/Admission.lean) binds those laws to the
actual checked region and proves call/return permission; maintained artifact
tests exercise both. The table application supplies
[all-reply summary laws](Examples/TableProtocol/Admission.lean) and
[artifact permission instances](Tests/TableAdmission.lean). Its
[native certificate consumer](../docs/compiler/phase-admission.md#native-table-admission)
retains the selected profile and evidence with the actual plan; native code
correspondence remains an implementation assumption tested differentially.

The finite phase checker joins both branch exits without refining their guards.
The source's validity-dependent challenge branch therefore uses its proved
semantic admission directly. A value-sensitive checker needs a sound producer
of those guard facts before it can certify this same claim automatically. This
is a declared compiler extension; it is not a missing premise in the direct proof.

## Bytecode, checked readback and complete callers

The fixed scalar bytecode [codec](Zkc/Protocols/ScalarBytecode/Codec.lean) and
[prover correspondence](Zkc/Protocols/ScalarBytecode/ProverCorrespondence.lean)
now have Std-only dependencies. The latter connects actual supplied local
programs, derived challenge views, canonical payloads, provider state and the
verifier prefix, including the claim-reachability condition. Hash functions
remain arbitrary deterministic interpretation parameters. Finite hash examples
and the atomic-versus-streaming failure-state separator are downstream
[tests](Tests/ScalarBytecode/Prover.lean), not assumptions of the library.
[Public dimensions](Zkc/Source/PublicDimensions.lean) and
[parameter families](Zkc/Protocols/AlgebraicRounds/ParameterFamily.lean) own the
substitution law independently of fixed scalar/group wire carriers. The group
carrier still denotes a canonical residue representation, not subgroup membership.

The bytecode [execution](Zkc/Protocols/ScalarBytecode/Execution.lean),
[live-register frames](Zkc/Protocols/ScalarBytecode/Frames.lean) and
[message evaluation](Zkc/Protocols/ScalarBytecode/MessageEvaluation/Composition.lean)
are separate Std-only APIs. Generic
[instruction composition](Zkc/Realization/InstructionComposition.lean) supplies
the list and block-flattening law, with an explicit prohibition on primitive
`.incomplete` halts. [Its counterexample](Tests/InstructionSequence.lean) shows
why that premise is necessary. The concrete
[Horner client](Zkc/Protocols/ScalarBytecode/Horner.lean) retains provider state,
proof suffix, offset, binding, ordered events and all registers except its three
declared scratch locations. It does not assert equality for an observer that
inspects those scratch registers.

The bytecode [endpoint execution](Zkc/Protocols/ScalarBytecode/Endpoint/Execution.lean),
[complete read packets](Zkc/Protocols/ScalarBytecode/ReadPackets.lean),
[supplier contracts](Zkc/Protocols/ScalarBytecode/Suppliers/Contracts.lean) and
[open frames](Zkc/Protocols/ScalarBytecode/Endpoint/Frames.lean) have Std-only
closures independent of concrete schedules and Horner. Reads retain failed
results, post-state, consumed offsets and events. Supplier relations preserve
external state through reads, end queries and challenge notices; persistent
closure is a separately stated, weaker contract. The
[causality countermodel](Zkc/Protocols/ScalarBytecode/Suppliers/Causality.lean)
retains the distinction between a tape chosen after each notice and one tape
fixed before all notices. The concrete
[endpoint optimization](Zkc/Protocols/ScalarBytecode/Endpoint/Horner.lean)
preserves the entire supplied strategy state; its local observer deliberately
omits PC, history and the stated scratch registers, and each program receives
its own sufficient execution fuel.

[Structural readback](Zkc/Compiler/Readback/Compilation.lean) is parameterized by
the literal type, literal interpretation and operation resolver. Successful
readback implies equality of the compiled interaction trees, including lazy
choice and ordered logical calls. The fixed scalar/FRI
[profile checker](Zkc/Protocols/BackendProfiles/Definitions.lean) instantiates
that API. [JSON array representation](Zkc/Realization/JsonArrays.lean) has its own
profile-independent exactness and uniqueness proofs. The
[source-selected admission](Zkc/Protocols/BackendProfiles/Correctness.lean)
consumes an independently supplied anchor; algebraic source rewriting and
physical backend conformance remain separate obligations.

The [one-round compilation](Zkc/Protocols/ScalarBytecode/OneRound/Compilation.lean)
consumes the independently selected source identifier, slice, input order, export,
guards and sites. The admitted backend profile supplies the actual block module;
[extraction](Zkc/Protocols/ScalarBytecode/BlockExtraction.lean) and
[optimization](Zkc/Protocols/ScalarBytecode/BlockOptimization.lean) join it through
an effectful prefix and continuation. Failed prefixes skip the module. These are
proofs about the represented instruction source, not extraction from Rust.

[Four-round scheduling](Zkc/Protocols/ScalarBytecode/FourRound/Scheduling.lean)
composes twelve checked exchanges on an actual 73-row source. Its
[Horner composition](Zkc/Protocols/ScalarBytecode/FourRound/Optimization.lean)
produces a 72-row represented body. Scheduling preserves every register;
Horner hides exactly the declared scratch registers. Neither row count nor
logical cache work is a new native speedup claim.

## Constructed artifact consumer

The [original-source artifact reference](design/artifact-reference.md) executes
actual candidate proof bytes from original explicit-binding or generic-library source
for the installed two-role public-artifact profile. Explicit configuration admits
multiple authorized setups with source-port and executable receive selection.
It owns source control, arithmetic, framing and observations, with exact public
SHA/Merlin/group/PCS requests through an explicitly trusted native service;
Lean independently reduces raw Merlin bytes. Full nominal admission, failure
prefixes and byte/field vectors have [executable controls](Tests/ArtifactReference.lean).
These are executable consumers and bounded evidence, separate from the existing
typed projection and interactive-security theorems.

[Length framing](Zkc/Realization/Framing.lean) proves list-byte payload separation
and suffix preservation. It does not prove correspondence with the executable
ByteArray cursor or Rust reader. No native construction correctness or FS security
theorem is added by these implementations.

## Verification

The package builds with exhaustive import and declaration audits, standalone
consumers and fresh source reconstruction. The permitted axioms are `propext`,
`Classical.choice` and `Quot.sound`. Declaration counts are reported separately
and do not measure maturity.

## Remaining realization and research

The [handoff](design/implementation-handoff.md) specifies the required MLIR/Rust
joins; [implementation status](../docs/status.md) records which are built.
The laws in this library do not themselves prove the native optimizer, storage
runtime or protocol executor. The controller comparison and resource tests
likewise retain their bounded evidence scope rather than supplying an
actual-source Rust refinement proof.

The [research agenda](design/research-agenda.md) retains automatic phase-sensitive
analysis/projection, stronger probability/security transport, FS/duplex/QROM,
ZK/extraction, asynchronous execution and verified native toolchains as separate
work. Their absence does not invalidate the stated finite ordinary theorems.

## Compiled relation and BN254 extension

`Zkc.Relation.QuadraticArithmetic` constructs the actual ordered sparse A/B/C
interpolants and proves satisfaction equivalent to vanishing-polynomial
divisibility at distinct row points. ONE/public binding stays explicit.
Padding, appended public rows with zero B/C, and finite vector-slice laws are
reusable and separate from security.
The source-C interpolant equals the rowwise A-times-B interpolant under actual
R1CS satisfaction; that hypothesis is enforced by the authored producer's check.
The executable reference adds independent BN254 scalar, vector, matrix and
polynomial arithmetic; generic PairingField/G1/G2 formation and source-relative
endpoint checks; exact matrix identity serialization; and bounded slicing.
Pairing/group validity and SHA256 retain the named external-service assumptions.

The native relation envelope is explicitly materialized before Lean admission.
This does not prove native relation generation or raw elaboration adequate.
Complete membership proving runs natively; independent Lean direct transforms
are bounded to 128 cells.

## External representation and schedule boundaries

`Zkc.Algebra.Representations` separates raw observations from many-to-one images
and proves conditional scalar-action, inverse-eight, interpolation, embedding
and reindexing laws. `Tests.Representations` includes torsion-action and ordered-axis
counterexamples. The native Edwards and table adapters are tested against these
obligations; their correspondence is not proved by importing the Lean module.

`Tools.Interactive.ExternalReference` is an independently executable schedule
reference for the installed external Monero/OpenVM transitions. It computes
state-envelope checks and transition order, using explicit trusted replies for
exact versioned hash/permutation requests. Archived checkpoints supply finite
correspondence evidence. No primitive security proof, complete BP+/OpenVM
verification or native resource refinement is claimed. Input-selected carrier
execution likewise reuses the family/count laws without a proved raw-to-typed
elaboration of the serialized input.

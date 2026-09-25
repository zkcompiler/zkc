# Assurance and formal coverage

The reference distinguishes **defined meaning**, **proved propositions**,
**actual source correspondence**, **finite/native evidence**, and **declared
trust**. None is a substitute for all the others. The selected model's definition
homes are in this tree and its maintained Lean sources are in `formal/`.

The correspondence maps separate definitions, proved consequences and the
obligations a source or native implementation still owes for the clauses they
cover. Their subjects are
[core execution and observations](spec/correspondence/core.md),
[programs, inputs and interaction](spec/correspondence/programs.md),
[domains and source](spec/correspondence/domains.md),
[modules, transformations and judgments](spec/correspondence/transformations.md),
[realization and binding](spec/correspondence/realization.md), and
[properties, probability, release and continuations](spec/correspondence/properties.md).
Each entry names the exact declarations and the hypotheses they retain, so a
declaration name alone never supplies a semantics. These maps are not an
exhaustive audit of every profile: some profiles give their Formal references
in-page, and others retain explicit implementation or proof obligations. Read
them with the [support map](../formal/SUPPORT.md) and [status](status.md); neither
a reference nor a map entry expands native or cryptographic implementation claims.

## 1. Claim-to-definition map

| Claim | Maintained formal source | Exact scope |
|---|---|---|
| Complete finite execution and sequencing | [Execution](../formal/Zkc/Semantics/Execution.lean), [MonadExecution](../formal/Zkc/Semantics/MonadExecution.lean) | Returned/stopped outcome, actual residual state and ordered events; generic monadic interpretation |
| Different reply representations | [Simulation](../formal/Zkc/Realization/Simulation.lean) | Value relation at actual final states, exact stops, projected events and sequencing/composition; no native progress or concrete Rust heap theorem |
| Interaction, returned phases and public bounds | [Interaction](../formal/Zkc/Semantics/Interaction.lean), [Boundary](../formal/Zkc/Semantics/Boundary.lean) | All interface-typed replies; returned-path conditions; finite atomic sessions; no honest completion inferred |
| Actual invocation records | [ExecutionPath](../formal/Zkc/Semantics/ExecutionPath.lean) | Exact erasure; conformance implies actual permission; `Within n` bounds actual calls including the stopping call, independently of handler event count and internal cost |
| Actual role inputs and immutable source | [Inputs](../formal/Zkc/Source/Inputs.lean), [Closures](../formal/Zkc/Source/Closures.lean), [Elaboration](../formal/Zkc/Source/Elaboration.lean) | Ordered available inputs, actual captures, fixed-source agreement and pure execution correspondence |
| Original table-expression adequacy | [TableExpression](../formal/Zkc/Polynomial/TableExpression.lean), [TableSource](../formal/Zkc/Protocols/Sumcheck/TableSource.lean) | All-point and Boolean-sum equality for accepted compilation; complete run including short/extra tapes; terminal and ordinary interactive soundness premises use the original actual tables |
| Effectful source and common admission | [pure frontend](../formal/Zkc/Source/Frontend.lean), [local-code admission](../formal/Zkc/Protocols/Sumcheck/LocalProver/Admission.lean), [Installed](../formal/Zkc/Protocols/CapturedPrograms/Inputs.lean) | Checked local code, no missing-input fallback, phase/bound/input preservation, source selection and actual installed-world use |
| Mixed analysis and preparation | [Analysis](../formal/Zkc/Compiler/FactorExecution.lean), [Mixed](../formal/Zkc/Polynomial/Bilinear/Execution.lean), [guarded compilation and readiness](../formal/Zkc/Polynomial/Bilinear/Compilation.lean) | Actual caller, failure/alias framing and valid immutable cache; original legal-caller law plus preservation up to actual readiness refusal under reached-call premises |
| Contextual preparation and component connection | [generic law](../formal/Zkc/Semantics/Preparation.lean), [Sumcheck source](../formal/Zkc/Protocols/Sumcheck/Preparation.lean), [residual connection](../formal/Zkc/Protocols/Sumcheck/Connection.lean), [integration](../formal/Tests/SumcheckPreparation.lean) | Valid cache and pure provider, arbitrary stateful external operations, full source outcome/state/projected events; the actual Fresh source also meets the common direct-evaluator acceptance connection. No native speedup, cryptographic PCS or universal construction-security theorem |
| Communication and scheduling | [Communication](../formal/Zkc/Protocols/CorrelatedSetup/Communication.lean), [AtomicSessions](../formal/Zkc/Protocols/CommitmentSessions/Source.lean) | Finite supplied clients/scheduler, retained state/events and actual preparation accounting |
| Persistent product provider | [ProductTape](../formal/Zkc/Probability/ProductTape.lean), [Provider](../formal/Zkc/Probability/ConditionalTape.lean) | Conditional product initialization, every finite adaptive prefix, residual reconstruction and next-output mass |
| Source-to-property consumer (optional ArkLib integration) | [SourceProvider](../formal/integrations/arklib/ZkcArkLib/LocalProver/Provider.lean) | Actual local code/committed messages and selected scalar reduction with its field/point-cap/false-claim premises |
| Correlated setup observer | [ServiceProbability](../formal/Zkc/Protocols/CapturedPrograms/Probability.lean) | Existing service publication/history mass law, fixed setup/source conditions and sufficient tape |
| Joint artifact/runtime release | [Deterministic](../formal/Zkc/Semantics/Disclosure.lean), [normalized PMF](../formal/Zkc/Probability/Disclosure.lean) | Exact allowed-world relation or one common coupling with actual marginals; pair-leakage and status-release controls; computational hiding requires another experiment |
| Conditional admission and use | [Judgment](../formal/Zkc/Properties/Judgment.lean), [local-code judgment](../formal/Zkc/Protocols/Sumcheck/LocalProver/Admission.lean) | Actual contextual premises retained through formation/refinement; uncertainty and caller requirements separate |
| Accepted atomic export | [AuthorizedContinuation](../formal/Zkc/Semantics/AuthorizedContinuation.lean) | Actual source, installed policy/handler/arm, phase/bound composition, current isolated ledger, retained verdict and no authorized partial export after stop |
| Residual-to-terminal use | [Relation](../formal/Zkc/Semantics/Relation.lean) | Reduction direction with explicit bad event, composed residual contract and actual scalar terminal; no automatic probability bound |

The library uses capability APIs and separately resolved optional integrations.
[Formal support](../formal/SUPPORT.md) records their actual clients and limits.
Their generic records specify obligations; their concrete instances and laws
show where those obligations are actually established. A record constructor
does not certify an arbitrary native implementation.

## 2. Integration boundaries

The shared integration contracts have these homes:

| Contract | Definition and evidence | Implementation extension |
|---|---|---|
| internal binding versus disclosure | [Observation contract](guides/execution.md#observations-and-refinement), `Disclosure`, actual private-receipt versus `publicStatus` controls | Native release/diagnostic/identifier schema must implement its chosen projection |
| retained verdict and authorized export | [Continuation contract](guides/accepted-continuations.md), installed service and joined failure/replay controls | Native identity, custody storage and publication; richer transferable/multiple exports only when promised |
| interpretation and checked inputs | [Binding](guides/artifact-binding.md), immutable issuance, installed-world interpretation, field/capture controls | Native resolver, dependency/FFI binding and lawful mutable rebinding |
| conditional judgments and attempts | [Judgments](guides/security-properties.md#judgments-premises-and-use), actual formation-to-refinement composition, unknown/requirement/cost controls | Native checker result correspondence; complete search only if claimed |
| source adequacy and erasure | [Source](guides/source-and-inputs.md), scoped erasure, all-capture/readiness checks and wrong-body/input controls | Actual structured/native lowering and imported source parser |
| relation-bearing results | [Relations](guides/security-properties.md#relation-bearing-results-and-terminal-verification), generic reduction/terminal laws and finished-scalar rejection | Complete argument-specific relation/security theorem for each promised consumer |

These definitions close the selected semantic integration without pretending
that all implementation or cryptographic extension work is done. In particular,
the atomic export model is a single-service, single-export interpretation;
general distributed/reentrant custody is outside its promise.

## 3. Verification and reproducibility

The [formal reproducer](../formal/reproduce.py) rebuilds selected pinned inputs
without prior Lean objects. The [development guide](development/README.md) and
[test guide](../tests/README.md) distinguish this source reconstruction from
incremental builds and individual check scopes. An available reproducer is not
evidence that it ran successfully for the current revision.

The audit permits only `propext`, `Classical.choice` and `Quot.sound` in the
transitive dependency of every reached zkc/control declaration. External
libraries can contain unfinished declarations; no dependence on their proof
holes is allowed for these declarations. Generated auxiliary theorem counts
are not counts of new authored contributions or a percentage of model maturity.

The [integration controls](../formal/Tests/Integration.lean) are kernel-checked
discriminators alongside general laws. [Protocol interpretations](guides/protocols.md)
explain the contrasting boundaries; [status](status.md) and maintained example
and [benchmark guides](../bench/README.md) identify native evidence and comparison
conditions. Reorganizing documentation does not rerun those measurements.

## 4. Trust and unmechanized boundaries

| Boundary | Current assurance |
|---|---|
| Lean propositions | Checked by the installed pinned Lean kernel with the audited standard axioms |
| Lean/Std toolchain | Pinned by `formal/lean-toolchain`; a build record must identify the actual source/cache scope and completed audits; no toolchain bootstrap claim |
| Mathematical external libraries | Exact source pins; reached proof assumptions audited |
| Native checker/parser and artifact bytes | Correspondence obligation for implementation; no universal decoder correctness theorem yet |
| Structured MLIR source and lowering | Bounded compiler routes exist; their exact supported scope is in [status](status.md), with source/lowering correspondence still required |
| Rust runtime and backend | Explicit common contracts; native realization can be proved or declared trusted at its actual scope |
| Concrete cryptography/providers | Scheme/model-specific assumptions and experiments; product-tape math does not prove native entropy/PRG/hash security |
| Full protocol security | Only the exact existing scoped propositions; no blanket completeness, soundness, knowledge or zero-knowledge theorem |

Reached-axiom auditing cannot establish kernel correctness.

The selected semantics can be a complete implementation basis while these
native and property-specific proofs remain separate milestones. A stronger
claim must identify and discharge its additional boundary rather than
reclassifying existing evidence.

The [verification design map](../formal/design/verification-map.md#5-assurance-is-a-collection-of-scoped-results)
separates kernel proof replay, compiled checker acceptance, native-evaluation
axioms and implementation correspondence. `native_decide` adds a
native-evaluation axiom to whatever it closes, so it does not meet the
restricted-axiom policy and appears in none of the proof library, its tools or
its examples; a control in `formal/checks/test_checks.py` keeps it out of them.

The conformance cases under `formal/Tests/` do use it, and always on an
`example`. What such a case establishes is that the compiled evaluator agrees
with a stated value on a named input, which is native-evaluation evidence
rather than a kernel proof. An `example` enters no declaration into the
environment, so the axiom audit neither covers nor could cover those; the
declaration and theorem counts it reports are the library's.

## 5. Theory coverage

[Theory](theory.md) owns the inventory of mathematical methods, their
applications and primary references. Its application table separates mechanized
laws, design methods with narrower current instances, and further research.
These categories constrain assurance claims: explicit framing is not a full
separation logic, and phase conformance is not a general session-type projection
or progress result.

The [research triggers](roadmap.md#3-research-triggers) record remaining candidates,
including stronger concurrency/projection, computational provider models,
aggregate attempts, richer reduction/custody interfaces, search completeness and
native confidentiality. These are not omitted theories silently assumed by the
current proofs. A new design task examines the theory needed by its exact
obligation; an open topic gets a concrete research target before expanding scope.

## 6. Implementation correspondence policy

Differential testing is the default practical validation
of correspondence between executable Lean meanings and actual MLIR/Rust
implementation paths. It is required evidence for each delivered native slice;
a proof of the Rust implementation is an optional strengthening, not a gate for
the first useful compiler component. Mathematical compiler/checker and promised
protocol-security theorems retain their own completion conditions.

Each campaign identifies the supported source subset, actual compiler route,
executables, inputs, initial states/providers and comparison relation. Compare
returned values or stops, related residual state and the selected ordered
observations. Different representations or lawful optimizations may use an
explicit projection/relation instead of equality of internal buffers or caches.
The relation must come from the semantic contract before evaluating results.
Shared explicit random tapes test operational correspondence; they do not prove
the sampling law or security of a changed challenge construction.

Use generated cases alongside boundary, failure and regression cases, independent
reference checks where feasible, and controls that show the comparator detects
disagreement. Record coverage gaps and retain reproducible failing artifacts.
A timeout or unsupported case is not agreement. Passing a finite campaign is
empirical evidence, not a universal equivalence theorem or a numerical bound on
the chance of a remaining bug. Unproved implementation boundaries remain explicit.

The [native design](../formal/design/native-correspondence.md#21-default-validation-route)
specifies the working method. The [status page](status.md) and
[test map](../tests/README.md) identify the maintained routes. A campaign
establishes only its recorded input, execution
and comparison scope; this policy does not expand that evidence.

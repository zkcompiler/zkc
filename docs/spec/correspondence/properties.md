# Property, probability, release and continuation correspondence

The common [experiment](../properties/experiments.md),
[relation](../properties/relations.md),
[probability](../properties/probability.md) and
[disclosure](../properties/disclosure.md) definitions, with the retained
[Sumcheck](../profiles/README.md#sumcheck-components),
[product-tape](../profiles/providers/product-tapes.md),
[correlated-service](../profiles/README.md#service-components) and
[continuation](../profiles/services/accepted-continuations.md) profiles, are mapped below.
`D` denotes definitions, `T` theorems under actual
hypotheses, and `O` specification/adapter obligations. Root and optional
declarations have separate import and assurance scopes.

## Experiment and probability definitions

The experiment operand record and completeness/soundness
schemas are specification interfaces; the concrete Sumcheck definitions remain
their selected mechanized instance. Adaptive false-instance acceptance,
construction-change inequalities and simulation/extraction access are explicit
claim obligations, not new general Lean security theorems.

The PMF equations correspond to installed Mathlib `PMF`, `PMF.bind_apply`,
`PMF.map_apply` and map composition. The finite-kernel complete successor
equation gives the experiment's required outcome/emission/view updater; the
generic Formal `FiniteKernel.update` remains the successful-output-indexed
marginal. Complete-update mass conservation and the relation-to-probability
event inclusion are explicit derivations in the specification, not claims that Formal
already provides a universal experiment framework. Coarsening retains the
actual constant-cap theorem and the separately stated varying-cap sum.

`RandomPermitted` in the specification corresponds to
`Zkc.Probability.Disclosure.Permitted`; deterministic `Permitted` corresponds
to `PIR.Disclosure.Permitted`. The different prose names disambiguate the two
Formal namespaces. Fixed-kernel postprocessing is congruence of `PMF.bind`
under equality of its input distribution. The exact public-status equations
correspond to `PIR.AuthorizedContinuation.decision`, `eraseValue` and
`publicStatus`, including receipt absence and stopped verifier outcomes.

## Selected experiment and framing

`Security.sourceAcceptance` fixes the
statement, callbacks and private state outside the independent uniform tape
average. `Execution.accepted_iff` and `TableSource.accepted_iff` bind the actual
terminal to that same source. Framed queries retain the actual statement root,
attempted request and successor provider state even when the provider stops.

## Providers and services

The provider profiles specify complete product
reconstruction and the actual projected next-request law. `requesting` selects
active nonempty returned fibers, while an active empty request still attempts
the provider and exhausts. `nextJoint` retains the prior checkpoint and next
outcome, rather than the next operation's entire execution record.

The correlated profile defines `Source.Program.Good`, `Service.Request`,
typed `Execution.Response`, actual handler transitions, and the uniform finite
publication/history coupling. `CapturedPrograms.Probability.view_exact` and
`witness_mass` connect that observer to the actual issued source. Stateful
coefficient preparation additionally uses `CorrelatedSetup.Preparation.Rel`,
`run_refines` and `experiment_mass`. Their observer excludes coefficients and
unused tape; complete deterministic refinement preserves the latter under its
state relation. The optional issued causal experiment retains its distinct
one-round verdict, conditional sampler cap and refusal projection.

## Continuation transition

Policy receives source, binding, actor, site, consumer and
target; validation of the future arm value belongs to its installed contract.
Every permitted fresh attempt allocates a run number and receipt, but only
verifier acceptance consumes the target. Ordinary negative arm data still
exports. The isolated ledger and common public-status projection retain their
separate custody and release premises. Final-state framing is not a reentrancy theorem.

## Probability notation

The local
consumer and issued experiment use the common `PMF` notation. In the optional
ArkLib implementation, each displayed sampler law is the PMF interpretation
of the actual supplied `ProbComp` sampler. This separates mathematical
laws from package availability; it does not transfer optional results into
the root build or claim that every abstract PMF has an executable sampler.

For [product requests](../profiles/sumcheck/one-round-consumer.md#committed-local-prover-consumer),
`ZkcArkLib.LocalProver.Provider.request_consumer` and `source_consumer_exact`
use `liftM draw`; `lift_mass` identifies its point masses with the original
sampler. The consumer applies its one-round kernel only on a requesting,
committed checkpoint, and returns `none` otherwise. The product suffix, actual
active decision, supported false-claim premise and point cap remain unchanged.

For the [issued experiment](../profiles/services/issued-causal.md#issued-causal-experiment),
`ZkcArkLib.LocalProver.pre_normalized`, `response_normalized`, `committed_mass`
and `conditional_draw` justify normalized law notation and conditioning at a
reachable commitment. `ZkcArkLib.CapturedPrograms.experiment_bound` retains
the actual issued source, sampler, injective embedding and support premises.
The affine-service witness-observation experiment remains separate.

The controller equation uses the common notation `eval env expression`
and an explicit `decide` for its Boolean cut. It denotes the same
`Zkc.Protocols.CorrelatedSetup.Source.Program.denote`, with the six-slot `Good`
policy and checked-source quantifiers.

## Properties

| Clause | Formal correspondence | Actual hypotheses and limits |
|---|---|---|
| [PROP-01](../properties/experiments.md#experiment-operands), [strategy information and statement selection](../properties/experiments.md#strategy-information-and-statement-selection) | D: concrete `Zkc.Protocols.Sumcheck.Security.sourceAcceptance`; O: general experiment and statement mapping schema | Fixed polynomial/claim and independent verifier tape; actual source, allowed strategies and observer must be supplied per experiment |
| [PROP-02](../properties/experiments.md#completeness-and-soundness-schemas), [simulation and extraction claim boundaries](../properties/experiments.md#simulation-and-extraction-claim-boundaries) | T: `Zkc.Protocols.Sumcheck.Security.source_perfect_completeness`, `Zkc.Protocols.Sumcheck.Security.source_soundness`; O: other general property/quantifier schemas | Finite field and degree-two polynomial; arbitrary supplied callbacks/private state independent of tape; no universal ZK/knowledge framework |
| [PROP-03](../properties/experiments.md#observation-based-transport) | T: `Zkc.Probability.Disclosure.coupled_release`, `Zkc.Probability.Disclosure.event_transport`, `Zkc.Protocols.Sumcheck.Optimization.acceptance_exact` | Actual distributions/marginals and observation equality; event determined by observation; Sumcheck exact complete execution supplies identity strategy transport |
| [PROP-04](../properties/experiments.md#construction-changes-and-contexts) | D: `PIR.HandlerRelated`; T: `PIR.run_related`, `Zkc.Protocols.AlgebraicRounds.Construction.framed_formed`; O: changed-experiment strategy/reduction and target-context laws | Common reply-adaptive body for generic refinement; framed formation has its own interaction; no generic adversarial target linking theorem |
| [PROP-05](../properties/relations.md#relation-families-and-instances) | D: `PIR.Relation.Family`, `PIR.Relation.Valid`, `PIR.Relation.ReductionContract` | Actual statement/witness interpretation and residual operands; native identifiers do not establish it |
| [PROP-06](../properties/relations.md#soundness-direction-reduction), [terminal decisions and contracts](../properties/relations.md#terminal-decisions-and-contracts), [scalar terminal](../properties/relations.md#scalar-terminal), [from reduction to a probability claim](../properties/relations.md#from-reduction-to-a-probability-claim) | T: `PIR.Relation.ReductionContract.then`, `PIR.Relation.terminal_sound`, `PIR.Relation.scalar_contract` | Same intermediate predicate/result and actual accepting terminal; exceptional disjunction has no automatic probability/completeness/extraction theorem |
| [PROP-07](../profiles/sumcheck/interactive.md#complete-verifier-source), [honest execution and interactive soundness](../profiles/sumcheck/interactive.md#honest-execution-and-interactive-soundness), [checked evaluation and table bound entry](../profiles/sumcheck/interactive.md#checked-evaluation-and-table-bound-entry) | T: `Zkc.Protocols.Sumcheck.Security.source_completeness`, `Zkc.Protocols.Sumcheck.Security.randomized_source_soundness`, `Zkc.Protocols.Sumcheck.Optimization.run_exact`, `Zkc.Protocols.Sumcheck.Optimization.soundness`, `Zkc.Protocols.Sumcheck.Optimization.perfect_completeness`, `Zkc.Protocols.Sumcheck.TableSource.soundness`, `Zkc.Protocols.Sumcheck.TableSource.perfect_completeness` | Exact field/tape and original false-claim premises; private seed finite/nonempty uniform and independent; table profile compile success; run equality covers arbitrary short/extra tapes but probability theorem fixes product length |
| [PROP-08](../profiles/sumcheck/framing.md#typed-framing-and-construction-phases), [complete statement root and framed execution](../profiles/sumcheck/framing.md#complete-statement-root-and-framed-execution) | T: `Zkc.Protocols.Sumcheck.Framed.root_injective`, `Zkc.Protocols.Sumcheck.Framed.run_exact`, `Zkc.Protocols.Sumcheck.Framed.optimized_exact`, `Zkc.Protocols.Sumcheck.Framed.root_retained`, `Zkc.Protocols.Sumcheck.Framed.queries_bound` | Same actual domain, dimension, coefficient object, provider and source; root injectivity stated at fixed dimension; failed-query prefix retained; O: byte/RO/FS security |

## Probability

| Clause | Formal correspondence | Actual hypotheses and limits |
|---|---|---|
| [PROB-01](../properties/probability.md#normalized-discrete-distributions) | D: `PIR.MonadHandler`, `PIR.Proc.runM`; T: `PIR.ProductTape.next_normalized`, `Zkc.Probability.UniformTape.average_eq_sum`, `Zkc.Probability.UniformTape.nonnegative`, `Zkc.Probability.UniformTape.at_most_one` | PMF normalization from Mathlib; rational average over finite nonempty coordinate domain for bounds; O: arbitrary rational/subdistribution interpretation |
| [PROB-02](../properties/probability.md#joint-initialization-and-persistence) | T: `PIR.ProductTape.initialized_execution`; O: actual joint setup/source selection | Arbitrary sampled local state/length but fixed conditional product suffix; local handler never receives future tape |
| [PROB-03](../properties/probability.md#reached-views-and-finite-masses), [point caps and information](../properties/probability.md#point-caps-and-information) | D: `Zkc.Probability.FiniteKernel.viewMass`, `Zkc.Probability.FiniteKernel.outputMass`, `Zkc.Probability.FiniteKernel.JointCap`; T: `Zkc.Probability.FiniteKernel.conditional_of_joint`, `Zkc.Probability.FiniteKernel.conditional_cap`, `Zkc.Probability.FiniteKernel.coarsen_cap` | Actual joint factorization/cap and positive denominator; finite rational algebra does not itself assert normalization or nonnegativity; coarsening direction only |
| [PROB-04](../properties/probability.md#adaptive-events-and-complete-updates) | T: `Zkc.Probability.FiniteKernel.adaptive_bad_set`, `Zkc.Probability.FiniteKernel.stopped_adaptive_bound`, `Zkc.Probability.FiniteKernel.update_output_mass`, `Zkc.Probability.FiniteKernel.output_normalized` | Actual full-view-selected finite set and active fibers; normalization lemma explicitly assumes normalized kernel; generic update is output-indexed, full experiment supplies view update and stopped outcomes |
| [PROB-05](../profiles/providers/product-tapes.md#interface-and-product-initialization), [persistent and online handlers](../profiles/providers/product-tapes.md#persistent-and-online-handlers), [complete residual reconstruction](../profiles/providers/product-tapes.md#complete-residual-reconstruction) | D: `PIR.ProductTape.persistent`, `PIR.ProductTape.online`, `PIR.ProductTape.expand`; T: `PIR.ProductTape.handler_expand`, `PIR.ProductTape.execution_expand`, `PIR.ProductTape.initialized_execution` | Fixed PMF `q`, conditional product suffix, finite source and tape-free local operations; exact residual reconstruction includes stopped outcomes |
| [PROB-06](../profiles/providers/product-tapes.md#actual-next-request-decision), [committed local prover consumer](../profiles/sumcheck/one-round-consumer.md#committed-local-prover-consumer) | D: `PIR.ProductTape.checkpoint`, `PIR.ProductTape.request`, `PIR.ProductTape.nextJoint`; T: `PIR.ProductTape.next_joint_exact`, `PIR.ProductTape.next_mass`, `PIR.ProductTape.conditional_next`, `PIR.ProductTape.joint_cap`; optional T: `ZkcArkLib.LocalProver.Provider.source_acceptance_bound`, `ZkcArkLib.LocalProver.Provider.initialized_acceptance_bound` | Positive requesting fiber for division; other successful mass zero; optional field, finite injective domain, point cap and false claim on reached committed support; guarded wrapper treats local abort separately |
| [PROB-07](../profiles/services/affine.md#joint-service-coupling-and-its-observer), [affine setup and response values](../profiles/services/affine.md#affine-setup-and-response-values), [checked controller expressions](../profiles/services/affine.md#checked-controller-expressions), [literal selection and issuance](../profiles/services/affine.md#literal-selection-and-issuance) | T: `Zkc.Probability.Observation.fiberEquiv`, `Zkc.Probability.FramedMask.continuation_mass_preserved`, `Zkc.Protocols.CapturedPrograms.Probability.witness_mass`, `Zkc.Protocols.CapturedPrograms.issue_agreement`, `Zkc.Protocols.CapturedPrograms.issued_service_mass` | Actual observation-preserving equivalence; finite uniform law for masses, same issued source/setup and Good; selected-source agreement required by root issuance theorem; no generic probability from a bijection alone |
| [PROB-08](../properties/probability.md#attempts-and-extensions) | O: explicit enclosing-attempt, computational and oracle-model contracts | Existing finite/product and deterministic framed laws do not mechanize these stronger experiments |

## Release

| Clause | Formal correspondence | Actual hypotheses and limits |
|---|---|---|
| [DISC-01](../properties/disclosure.md#allowed-worlds-and-selected-release) | D: `PIR.Disclosure.Permitted`; T: `PIR.Disclosure.deliberate_release` | Actual allowed world relation and release; permitted deliberate value explicitly restricts comparison; O: policy adequacy |
| [DISC-02](../properties/disclosure.md#deterministic-joint-release) | D: `PIR.Disclosure.publish`; T: `PIR.Disclosure.joint_release`, `PIR.Disclosure.joint_requires_artifact` | Same deterministic allowed relation for both channels; no randomized marginal composition inference |
| [DISC-03](../properties/disclosure.md#randomized-joint-release), [couplings and joint agreement](../properties/disclosure.md#couplings-and-joint-agreement) | D: `Zkc.Probability.Disclosure.Permitted`; T: `Zkc.Probability.Disclosure.map_supported`, `Zkc.Probability.Disclosure.coupled_release`, `Zkc.Probability.Disclosure.joint_release`, `Tests.RandomizedDisclosure.marginals`, `Tests.RandomizedDisclosure.joint_leaks`, `Tests.RandomizedDisclosure.masked_joint` | Actual normalized PMF marginals and one common support agreement for both channels; controls include non-identity coupling; no statistical/computational bound |
| [DISC-04](../properties/disclosure.md#postprocessing-and-continuation), [authorized service status projection](../properties/disclosure.md#authorized-service-status-projection) | T: `PIR.Disclosure.project_release`, `Zkc.Probability.Disclosure.project_release`, `PIR.IntegrationControls.released_status_hides_capture`; D: `PIR.AuthorizedContinuation.publicStatus` | Postprocessing existing permission; concrete failed-arm capture example only; status permission still required for other experiments/contexts |
| [DISC-05](../properties/disclosure.md#cost-and-implementation-observations) | T: `Zkc.Modules.Preparation.priced_improvement_iff`, `PIR.Preparation.Emission.priced_improvement`; O: selected native cost/side-channel observer | Actual total preparation profile, cost units/prices and projected charge erasure; no native performance or cache privacy theorem |

## Continuations and authority

| Clause | Formal correspondence | Actual hypotheses and limits |
|---|---|---|
| [CONT-01](../profiles/services/accepted-continuations.md#verifier-decisions-and-ordinary-composition) | D: `PIR.Continuation.Terminal`; O: actual verifier/security meaning | Constructor is result data; actual source and terminal contract supply meaning |
| [CONT-02](../profiles/services/accepted-continuations.md#verifier-decisions-and-ordinary-composition), [phases and finite bounds](../profiles/services/accepted-continuations.md#phases-and-finite-bounds) | D: `PIR.Continuation.after`; T: `PIR.Continuation.rejected_no_arm`, `PIR.Continuation.stopped_no_arm`, `PIR.Continuation.accepted_retains_prefix`, `PIR.Continuation.formed` | Actual verifier result, residual state and events; all accepted returned-phase arm premises; no rollback |
| [CONT-03](../profiles/services/accepted-continuations.md#retained-verifier-and-arm-report) | D: `PIR.Continuation.Report`, `PIR.Continuation.runReport`; T: `PIR.Continuation.report_verifier`, `PIR.Continuation.report_combined`, `PIR.Continuation.report_accepted` | Actual execution expressions, not arbitrary report records; O: native retained representation/authentication/disclosure |
| [CONT-04](../profiles/services/accepted-continuations.md#single-entry-handoff) | D: `PIR.Continuation.take`; T: `PIR.Continuation.wrong_target`, `PIR.Continuation.replay_refused`, `PIR.Continuation.consumed_under_frame` | Already-authorized actual key and residual ledger; arm final-state frame alone gives no reentrant/intermediate custody |
| [CONT-05](../profiles/services/accepted-continuations.md#admitted-invocation-and-installed-service) | D: `PIR.AuthorizedContinuation.Invocation`, `PIR.AuthorizedContinuation.Service`; T: `PIR.AuthorizedContinuation.Service.formed`, `PIR.AuthorizedContinuation.Service.bounded` | Same admitted frontend/source/binding/body and installed policy/handler/arm; phase and uniform public arm bound fields |
| [CONT-06](../profiles/services/accepted-continuations.md#ledger-receipt-and-export-result), [atomic service transition](../profiles/services/accepted-continuations.md#atomic-service-transition) | D: `PIR.AuthorizedContinuation.execute`, `PIR.AuthorizedContinuation.exportReturned`; T: `PIR.AuthorizedContinuation.source_bound`, `PIR.AuthorizedContinuation.actual_report`, `PIR.AuthorizedContinuation.accepted_consumed`, `PIR.AuthorizedContinuation.failed_arm_no_export`, `PIR.AuthorizedContinuation.unauthorized_refused`, `PIR.AuthorizedContinuation.replay_refused` | Actual allowed/fresh invocation and result hypotheses; monotone run allocation and ledger isolation by the concrete transition; successful export is ordinary arm return, no extra hidden predicate |
| [CONT-07](../profiles/services/accepted-continuations.md#authenticity-custody-and-disclosure) | D: `PIR.AuthorizedContinuation.Authentic`; O: native instance identity, current ledger custody and release | Equality to actual atomic transition is mathematical authenticity; no signature, serialized receipt proof, durable/distributed/reentrant authority theorem |

## Controls

`Tests.RandomizedDisclosure` adds normalized PMF marginal leakage and a positive
common coupling. `Tests.Integration` and `Tests.Composition` cover actual private
receipt leakage, approved status projection, retained acceptance after failed
arm, consumed authority, replay/wrong binding, and an illicit ledger-writing
arm. `Tests.ChallengeConsumption` and `Tests.ProviderSampling` distinguish
actual request timing, local abort and exhausted provider behavior.
`Tests.Sumcheck`, `Tests.SumcheckAdversary`, `Tests.SumcheckOptimization`,
`Tests.SumcheckFramed` and `Tests.TableSource` cover the whole verifier, false
claims, source/point order and checked evaluation paths.

## Profiles

The complete [interactive verifier](../profiles/sumcheck/interactive.md),
[framed construction](../profiles/sumcheck/framing.md),
[affine service](../profiles/services/affine.md) and
[issued causal experiment](../profiles/services/issued-causal.md) retain their
distinct experiments and theorem premises.

## Finite controller probability

[`Probability.Iteration`](../../../formal/Zkc/Probability/Iteration.lean) proves
nonnegative complete-transition pushforward, total mass preservation, an event
pushforward identity, geometric tails under a supplied one-step pending-mass
bound, and accepted-mass accounting. `Iteration.evaluateM` interprets actual
finite prefixes with `Proc.runM`; `evaluateM_add` proves resumption and
`evaluateM_pure` recovers deterministic execution. These provide an execution
subject for a concrete probability proof, not its conditional bound.
The kernel is finite and rational. These laws neither establish a concrete
protocol's conditional retry bound nor normalize successful outputs, construct
an infinite stream distribution or prove honest termination.

`Tests.IterationProbability.PersistentCoin` computes the pending mass of actual
controller executions retaining one hidden fair bit: every positive horizon
has mass `1/2`. It refutes geometric decay from a marginal retry probability and
reusing an information-losing current observation as sufficient future state.

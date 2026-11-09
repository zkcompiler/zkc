# Fixed property meanings

The framework fixes the claim before accepting a proof. An `Experiment E O` supplies a
normalized probability law for every environment. An `Observation O V` is a measurable map
of the entire outcome. `Experiment.observe` pushes forward all probability mass, including
explicit rejection and abort outcomes; it never conditions on success. For Process clients,
`System.experiment` produces canonical `PIR.Execution State Event Result` from `ZkcProgram`,
with outcome, reached state and ordered events. An observation selects what is visible without
silently replacing that underlying execution meaning.

The environment fixes the public input, setup and admitted adversary or honest strategy.
It is semantic context, not automatically an argument available to an adversary. A mathematical
model must still choose its intended relation, observable view and admitted environments
correctly. A kernel proof validates that chosen meaning, not the application's intent.

## Property-specific requests

| Request | Fixed meaning | Author or reusable method supplies |
| --- | --- | --- |
| `SoundnessRequest` | For every admitted environment, `Pr[accept ∧ problem.no(outputStatement)] ≤ error` | A mathematical bad-event bound and any required execution/observation correspondence |
| `CompletenessRequest` | For every admitted honest environment, `1 - error ≤ Pr[accept]` | Honest computation, valid-input and termination/mass facts |
| `RecoveryRequest` | Failure probability of the fixed transcript recovery map is at most `error` | A correctness theorem for that recovery map; this does not imply a knowledge theorem |
| `ExtractionRequest` | The fixed extractor succeeds with probability at least the selected function of acceptance, and meets its weighted-call budget | Acceptance-to-extraction mathematics and an abstract-call bound |
| `StatisticalSimulationRequest` | The fixed real/simulated views differ by at most `error` on every measurable event, and the simulator meets its call budget | A view-comparison proof and call bound; exact equality suffices at zero error |
| `DistinguisherSimulationRequest` | Each admitted observer's true-output probability differs by at most `error`, with the same simulator call bound | An argument for the fixed normalized observer family and call bound |

`UpperRequest` and `LowerRequest` are underlying event-bound interfaces, not the universal
definition of every security property. `ViewComparison` is a reusable mathematical comparison
of two complete laws; the operational simulation requests additionally fix the simulator's
access and resources.

`PromiseProblem` has disjoint positive and negative regions. A gap is permitted. A separate
`WitnessRelation` proves that a related witness implies membership in the positive region;
coverage of all positive instances is an additional theorem if an application needs it.
This avoids forcing proximity soundness to mean the negation of exact membership.

## Extraction: algorithm, access and threshold

Extraction and simulation share
`AccessExecution Public Environment Interface State Event Result`. Its fields are, with
parameters and measurable instances understood:

```lean
system : System Environment Interface State Event
publicInput : Environment → Public
algorithm : Public → Process Interface Result
```

Its experiment returns `Execution State Event Result`. Operation replies must be countable
with measurable singletons for this kernel interpretation; state, event and result spaces
carry their stated measurable structures. Requests retain measurable success/event premises.

The algorithm gets the selected public input and typed operation answers. The request also
fixes the handler and initial state law. Private state is threaded by `System`; it is not
implicitly an algorithm parameter. Reset, forking, straight-line queries and other capabilities
must occur in the selected interface/handler if allowed. Naming an algorithm an extractor
does not grant those capabilities.

The implemented extraction profile uses a statement fixed by the public input. Acceptance and
extraction are indexed by the same environment. Success means that the selected program returns
a record with `out.outcome = .returned (some w)` and `w` satisfies the request's witness relation
for that statement. Returned `none`, invalid witnesses and every stopped reason retain their
mass as failure. `successRequest environment` exposes this as a regular lower-bound proof goal,
and `establish` conjoins its proof with the selected resource bound.

`ExtractionGuarantee` fixes a monotone success function, its probability range, and positivity
above an explicit threshold. `direct` is the concrete profile `lower p = p`, with threshold zero.
Other extraction methods may supply another proved profile; evidence for an existing request
cannot select an easier one. `Informative` asks whether its threshold is below one.

`OperationCost.bound` is a structural fold over the well-founded Process tree:

```text
bound (.done value) = 0
bound (.halt reason) = 0
bound (.call operation next) = weight operation + ⨆ reply, bound (next reply)
```

It preserves adaptive call choices and charges no continuation after an explicit stop, including
`halt.bind`. The call itself is charged; a handler stop prevents further execution under the
fixed System semantics, while this uniform structural bound may overestimate that path.
`OperationCost.calls` gives each abstract call weight one. Every Process path is finite, but
unbounded reply branching can still give an infinite supremum; a finite budget is a separate
obligation. This fold computes a resource bound, not another probability evaluator.
`Internal.bound_eq_charge` connects it to PolyFun's charge fold on the stop-aware encoding;
authors still supply a Process and its selected call budget.

These are worst-case weighted **abstract calls**. Pure computation is uncharged; operations can
represent substantial work. The claim is therefore named bounded extraction, not general
efficient proof of knowledge. An efficient knowledge definition needs a justified computational
and adversary-resource profile as well as the cryptographic extraction theorem.

## Simulation: uniformity and observations

`SimulationProfile` fixes `real : Experiment (Context × Witness) (Outcome View)`, one simulator over
`Context`, and the valid context/witness relation. The simulator can depend on public input and
the context-selected verifier through allowed services. It does not receive the witness as an
argument. Its handler is indexed by context, not by the subsequently quantified witness.

The simulated law observes the complete Execution through `Observation.outcome`, giving
`Outcome View`. Every stopped reason remains visible; it is neither discarded nor replaced by
a successful view. The returned `View` must contain the claimed transcript/leakage fields.
Private state and event logs are not automatically added to that view. Omitting a field changes
the security claim; the framework cannot infer the author's intended observation.

Statistical simulation quantifies over every measurable event. Zero error plus exact view-law
equality is the supported perfect-simulation case. Selected-observer simulation instead fixes
normalized test kernels on `Outcome View` and their admitted class. A restricted test family
is not automatically a polynomial-time class, and either profile must state the
actual verifier/context capabilities before being interpreted as a particular ZK definition.

## Receipts, premises and diagnostics

`Claim` has six built-in property constructors and a separate `custom` constructor. Its `Meaning`
and `kind` are computed from that constructor; no proof provider supplies a free proposition
under a security-label string. `Receipt claim` contains a proof of that exact meaning. Any valid
proof route works, including a direct theorem or an imported theorem behind a proved adapter.

Canonical means framework-defined **schema**. It does not certify that a relation expresses the
intended problem, that the view is sufficient, that admission is populated, or that the error is
useful. A custom proposition remains custom even when extensionally equal to a canonical one.

`ConditionalReceipt claim P` proves `P → claim.Meaning`. Its `close` theorem requires an actual
proof of `P`. An inconsistent unproved premise can therefore produce conditional evidence but
cannot produce a closed receipt for a false claim. Ordinary Lean theorem parameters also remain
parameters; placing a theorem in a definition does not discharge them.

`AdmissionAssessment` records a witnessed admitted input, a proof of emptiness, or `unchecked`.
`ErrorAssessment` records a uniform bound below one, an admitted bound at least one, or
`unchecked`. `BudgetAssessment` distinguishes a finite budget from an admitted infinite one.
These assessments supplement proof validity, independently of the proof route.
They are typed interfaces for later reporting, not a new report generator. In particular, an
informative error assessment alone can be vacuous if admission is empty: both axes matter.

## Model boundary examples

The Process migrations of the adaptive/nested and shared-state clients use `UpperEvidence`
and `LowerEvidence`, with ordinary truth embedded by `PromiseProblem.ofPredicate`. The property
models exercise the following boundaries; their current integrated validation belongs to the
parent's final gate, separately from the historical records:

- `PropertyProfiles`: one persistent-state service, fixed extraction and simulation algorithms,
  wrong extractor, wrong public statement, insufficient budget, adaptive call accounting, leaked
  witness, and closed receipts for extraction and both simulation meanings. Stop controls cover
  retained state/events, refused stopped extraction and distinguishable terminal reasons.
- `ClaimBoundaries`: accepted promise gap versus accepted negative/adaptive statement, honest
  half-abort behavior, measurable observation retaining rejection mass, closed soundness,
  completeness and recovery receipts, conditional closure, custom classification and emptiness.
- `BoundaryControls`: proved refusals for false acceptance, honest rejection, wrong recovery,
  leaked views, lost probability mass and missing initial-state coverage.

These are small complete model experiments. They do not claim an IR connection, an automatic
proof-construction engine, or newly proved cryptographic protocols.

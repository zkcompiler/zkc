# Process-facing implementation interfaces

Namespace: `ProtocolProof`. The package depends on `ZkcProgram` at `../program` and pinned
VCVio, PolyFun and Mathlib. `PIR.Signature`, `PIR.Process`, `PIR.Outcome`, `PIR.Execution` and
`PIR.Stop` are canonical declarations from `ZkcProgram`, not aliases. The generic
`Zkc.Source.Region` also belongs to that shared package; its namespace does not imply a
concrete IR dependency. The Process-facing carrier parameters use `Type`.

## Execution and quantitative contracts

- `Semantics/Execution.lean` supplies measurable structures and
  `PIR.Execution.measurableEquiv : Execution S L A ≃ᵐ Outcome A × (S × List L)`.
  `Semantics/EventLog.lean` supplies measurable list operations for ordered event accumulation.
- `System E I S L` fixes `operations : E → (op : I.Op) → Kernel S (Execution S L (I.Reply op))`
  and `initial : E → Measure S`, with fields `operation_mass` and `initial_probability`.
  `System.run` takes an environment and a `Process I A` and returns a kernel from `S` to
  `Execution S L A`. `System.runFrom` additionally accepts an existing event prefix as part
  of `S × List L`. `System.experiment` takes `E → Process I A` and returns the complete
  `Experiment E (Execution S L A)`.
- `System.accumulatedOperations` preserves the joint outcome/state law and appends newly
  emitted events to the prefix, including on a stopped reply. `System.initialWithEvents`
  maps the whole initial law by `fun state => (state, [])`.
- `Internal.effects I` gives operations outcome-valued replies. `Internal.encode` translates
  Process once, stopping after a failed reply. `System.runFrom` uses upstream `FreeM.runKernel`
  on this encoding; `System.experiment` uses the same backend and the measurable record
  equivalence. These are not independent probability evaluators or alternative authoring APIs.
- `OperationSpec I S L` consumes a continuation of type
  `Outcome (I.Reply op) → (S × List L) → ENNReal`. `OperationSpec.Monotone` is pointwise
  monotonicity. `opExpectation (system.accumulatedOperations environment)` is the exact spec.
  `wpFold spec program post` applies the upstream specification fold to the encoding, with
  `post : Outcome A → (S × List L) → ENNReal`.
- `UpperBound spec program post potential` and `LowerBound ...` are Process-indexed contracts,
  with `potential : (S × List L) → ENNReal`. Their `pure`, `halt`, `operation`, `bind`,
  `consequence`, `ite`, `dite` and `iterate` rules retain stop rewards. The public single-call
  expression is `PIR.Process.call operation .done`. Bind and iteration require an explicit
  stopped-branch inequality, in opposite directions for upper and lower bounds.
- `Semantics/Probability.lean` supplies `System.runFrom_bind`,
  `System.wpFold_eq_lintegral_runFrom`, `System.lintegral_wpFold_eq_experiment`, the event
  indicator specializations and `System.experiment_eq_dirac`. These relate the same
  interpretation to full-record expectations and deterministic experiments. Dirac experiment
  agreement requires both the primitive Dirac laws and a Dirac initial law.
- `Components/Adequacy.lean` exposes `UpperBound.adequate`, `closed_expectation_le` and
  `closed_event_le`, plus `LowerBound.adequate`, `le_closed_expectation` and `le_closed_event`.
  These reuse internal adequacy for `System.runFrom` and whole experiments. Local spec
  comparisons, measurable rewards/events and whole-initial-law budgets remain explicit.

Kernel execution and root closure require measurable state, event and result spaces, and
countable operation replies with measurable singletons. The backend measurable-reward bridge
`Internal.wpFold_eq_runExpectation_of_measurable` requires a measurable terminal reward, not
countable state or result spaces. Its unrestricted-reward specialization additionally requires
countable state/result spaces with measurable singletons. Event transports require measurable
events; expectation transports require measurable rewards. `System.runFrom_bind` additionally
requires a countable intermediate return type with measurable singletons. The exact measurable
reward and whole-initial-law expectation theorems do not add that return-type restriction.

## Installation and root closure

`Installation actual model admissible related` is exact same-interface installation. Both
systems use the same `Signature`; their states and event types may differ. The relation has
type `E → (S × List L) → (T × List M) → Prop`. Its `operations` field is VCVio's
`KernelHandler.CouplingContract` for the two accumulated handlers, including complete equal
outcomes and related accumulated states. Its `initial` field couples the entire
`initialWithEvents` laws. There is no public `Connection` compatibility alias.

`Installation.mass_eq`, `lintegral_le`/`lintegral_ge` and `event_le`/`event_ge` transport the
same Process client at an admitted environment. Their terminal premise compares complete
outcomes and related state/log pairs. `upper_bound`/`lower_bound` and
`event_upper_bound`/`event_lower_bound` compose these transports with a model bound.

`Representation.contractOfMap` constructs the local coupling from a measurable, possibly
non-injective map on accumulated state and a full local commutation equation.
`Installation.ofMap` also requires the whole initial-law pushforward;
`Installation.reflexive` handles identity. These constructors require the stated measurable
equality structure on the target accumulated state. They do not decode differing interfaces.

`UpperEvidence request actual model client related` and `LowerEvidence ...` fix a request over
`Execution S L A` and a client `E → Process I A`. Their fields are `subject`, `installation`,
`spec`, `local_bound`, `model_event`, `measurable_event`, `terminal`, `potential`, `mathematics`
and `budget`. The terminal implication compares full outcomes and related state/log pairs.
The budget integrates over the whole model `initialWithEvents` law. `.establish` reuses
`Internal.UpperEvidence.establish` or `Internal.LowerEvidence.establish` through the measurable
record equivalence; no field is the requested whole-game conclusion.

## Property modules

- `Semantics/Experiment`: normalized laws, measurable observations and environment reindexing.
- `Semantics/Access`: `AccessExecution Public Environment Interface State Event Result`, with
  `algorithm : Public → Process Interface Result`; its experiment returns full Execution.
  `OperationCost.bound` is a structural Process call bound, not a probability interpretation.
  `Internal.bound_eq_charge` relates it to the upstream charge fold of the stop-aware encoding.
- `Claims/Problem`, `Quantitative`, `Soundness`, `Completeness`, `Recovery` and `View`: distinct
  fixed meanings and reusable event/view bounds. `Claims/Request` is their import surface.
- `Claims/Extraction`: explicit Event parameter, fixed access and success guarantee; success
  requires `out.outcome = .returned (some witness)` and the witness relation.
- `Claims/Simulation`: explicit Event parameter; real and simulated experiments observe
  `Outcome View`. Selected observer kernels also take `Outcome View`, retaining every stop.
- `Claims/Receipt`, `Diagnostics`: built-in/custom and closed/conditional evidence, with
  admission, error and resource assessments. `Claims/Transfer` supplies statistical upper game
  transport with explicit environment translation and losses.

The complete request indexes `Receipt`; `ConditionalReceipt claim P` closes only with a proof
of `P`. Computations and constructors use descriptive lower camel case names; propositions
such as `Holds`, `Meaning` and `CallsBounded` are capitalized. Public meaning definitions use
selective `@[expose]` for downstream unfolding; mathematical proof bodies need no such policy.
Package numbers describe the architecture plan, not shipped API names.

See [IMPLEMENTATION.md](IMPLEMENTATION.md) for Package 1 proof ownership and the parent-owned
P2/integration boundary and [VALIDATION.md](VALIDATION.md) for the final package build and
standard-axiom audit. The construction engine remains a later unit.

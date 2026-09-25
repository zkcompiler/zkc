# Experiments and property claims

A property concerns an actual experiment: the selected programs, participants,
information, initialization, execution and observation. A claim about one such
experiment does not automatically apply to a different construction, a larger
adversary class or a recipient with additional observations.

## Experiment operands

The normalized discrete interface uses the following operands. Types may
depend on public parameters; the equations below fix those parameters so that
their arguments are well-typed.

| Operand | Meaning |
|---|---|
| `κ : Parameters` | Public instance parameters and their domain/operation interpretation; a security index when the profile uses one |
| `x : Input κ` | Actual ordered invocation inputs and their selected statement/witness mapping |
| `a : Strategy κ x` | A complete tuple of supplied participant and environment strategies, including their specified access interfaces |
| `Allowed κ x a : Prop` | The strategy, information and resource restrictions of the claim |
| `Z : Type` | The joint initialization configuration, including setup, role inputs, private coins, correlated resources and provider state |
| `init κ x a : PMF Z` | The actual joint initialization law |
| `Result : Type` | The retained complete result, including execution outcome, residual state and ordered observations at each claimed boundary |
| `run κ x a : Z → PMF Result` | Execution of the selected source and interpretation with those strategies and initial values |
| `observe κ x a : Z × Result → O` | The complete observation used by this particular comparison or property event |

For fixed `κ,x,a`, define:

```text
record = bind(init κ x a,
              z ↦ map(r ↦ (z,r), run κ x a z))
observed = map(observe κ x a, record)
eventProbability(B) = Pr[record : B].
```

The mathematical record retains initialization so that a predicate can refer
to the actual selected statement, setup or witness. It does not publish all
of `Z`. The observer selects the recipient's information; a security proof may
reason about hidden data without giving it to a strategy.

An instance of this interface supplies actual definitions of `init`, `run`,
the statement mapping and the claimed events. In the finite source profile,
`run` is the [monadic execution](probability.md#normalized-discrete-distributions)
of the actually selected, interpreted and bound body. A composite service can
retain additional reports, provided they are related to its actual execution.
An arbitrary function named `run` with no source connection does not establish
a source property.

The assumptions of a claim identify their subjects separately: mathematical
domain laws, cryptographic assumptions, strategy restrictions and backend or
artifact correspondence. An identifier contributes meaning through its
[resolved interpretation](../realization/artifacts.md), not through its spelling.

## Strategy information and statement selection

Each allowed strategy has an explicit interaction interface and permitted view.
A source-based strategy uses the
[local-information boundary](../language/interaction.md#local-information)
and input-access contract applicable to that source. Private controller state
and earlier replies may influence its next action; hidden provider state and
future coins influence it only through the specified access interface.
Initialization correlations are fixed by `init`, not inferred from locality.

For a fixed-instance claim, the actual statement and source are fixed before
the randomness from which their independence is assumed. A later adaptive
strategy can still react to delivered replies. For an adaptive-instance claim,
the selection operation, the information it receives, the selected instance
and its timing are part of the experiment. The event uses that actual instance.
Secret-dependent source or setup selection also has its own
[disclosure obligation](disclosure.md#allowed-worlds-and-selected-release).

An experiment may sample a private seed and then execute a deterministic
strategy selected from it. Extending a fixed-strategy probability bound to
that mixture requires the actual conditional experiment at each supported
seed to satisfy the bound. A seed correlated with future verifier randomness
cannot use a theorem whose hypothesis fixes the strategy independently of
that randomness.

Resource restrictions identify what is bounded: public source calls, execution
steps, oracle queries, memory, running time or an asymptotic algorithm class.
A finite reply-adaptive body need not have a uniform public bound. A source
[call bound](../core/execution.md#uniform-call-bounds) does not bound arbitrary
internal provider work or native runtime.

## Completeness and soundness schemas

A completeness instance selects a relation family, actual valid
statement/witness inputs, honest participant strategies and the event `Accept`
of their actual verifier. Let `CompleteInputs(κ)` contain those bound inputs,
`Honest(κ,x)` be the selected honest strategies, and `δ(κ,x,a) ∈ [0,1]` their
allowed failure probability. Its claim is:

```text
∀ κ, x ∈ CompleteInputs(κ), a ∈ Honest(κ,x),
  Allowed κ x a ∧ Pr[recordκ,x,a : Accept] ≥ 1 - δ(κ,x,a).
```

Membership in `CompleteInputs` includes satisfaction of the stated relation
and the actual witness binding used by honest execution. The profile supplies
that membership definition and the honest class; an empty class would make
the probability condition vacuous rather than establish a usable honest
prover. Perfect completeness has `δ=0`.

A soundness instance selects an allowed prover/environment class and a
mathematical event `FalseInstance` meaning that the actual claimed statement
is invalid. For a nonnegative bound `ε(κ,x,a)`, its claim is:

```text
∀ κ x a, Allowed κ x a →
  Pr[recordκ,x,a : Accept ∧ FalseInstance] ≤ ε(κ,x,a).
```

For a fixed false statement, `FalseInstance` holds on the entire supported
record, so this is its acceptance bound. A bound for adaptive statements uses
the event that the selected statement is false and accepted; it is not a
conditional probability obtained by discarding true selections. A profile can
instead choose another explicitly defined experiment, but cannot change these
events while retaining this claim.

Bounds greater than one remain valid numerical upper bounds and are
uninformative as security estimates. Stops and a verifier's negative result
remain in the normalized record. An adopted verifier's `Accept` predicate
identifies its actual positive decision; successful host return or phase
completion alone does not define it. The
[Sumcheck profile](../profiles/sumcheck/interactive.md#complete-verifier-source)
selects concrete honest and adversarial callbacks, the full terminal event
and its field/dimension bound.

## Simulation and extraction claim boundaries

A zero-knowledge instance supplies actual real and simulated observation
ensembles, a verifier class, simulator class and access, admissible input/auxiliary
information, comparison and quantifier order. For example, the shape
`∀ verifier, ∃ simulator, ∀ admissible inputs, real ≈ simulated` fixes one
simulator for that verifier across the quantified inputs. A shape allowing a
new simulator for each hidden witness is a different statement. The instance
specifies which inputs and resources the simulator receives; equality of two
honest executions does not construct one.

The comparison is explicit: perfect equality of distributions, statistical
distance with a stated bound, or distinguishing advantage against a stated
algorithm class and resources. The observation includes the verifier's
permitted auxiliary information and final view, and any jointly released
artifacts claimed to be hidden. A computational or statistical comparison
needs its selected experiment and loss laws; the exact-distribution interface
does not supply a default for them.

A knowledge instance supplies the relation, prover class, extractor class,
quantifier order, exact extractor access and its witness-success condition.
Access can distinguish straight-line interaction, restarting, rewinding or
another selected interface. Its claim connects the actual prover acceptance
probability to extraction of a witness for the actual statement, with the
stated knowledge error, probability loss and resource bounds. The binding
also specifies setup and auxiliary information. A soundness-direction
[reduction contract](relations.md#soundness-direction-reduction) alone contains
no witness-producing algorithm or extraction-success law.

These are parameterized claim boundaries. A protocol's concrete simulation or
extraction claim selects their complete experiment and theorem; the common
specification does not choose one universal zero-knowledge or knowledge notion.
Completeness, soundness, zero knowledge and knowledge remain separate claims.

## Observation-based transport

Let `p : PMF X` and `q : PMF Y` be the actual complete experiment laws. Let
`f : X → O` and `g : Y → O` be their selected observations. If:

```text
map(f,p) = map(g,q),
```

then, for every event `B : O → Prop`:

```text
Pr[p : B∘f] = Pr[q : B∘g].
```

The event must factor through the preserved observation. If soundness uses
both acceptance and the actual statement's invalidity, the compared event
must preserve both; equality of an unrelated transcript does not suffice.
An [observation-preserving coupling](disclosure.md#couplings-and-joint-agreement)
with these actual marginals is a sufficient way to prove the distribution
equality. Pointwise complete-execution equality under the same initialized
sample is another sufficient way.

Transport of a quantified claim supplies this equality for every parameter,
input, allowed strategy and context in the target claim. Equality only for the
honest strategy transports that honest experiment. A
[handler-replacement law](../core/observations.md#handler-replacement) lifts
through a common reply-adaptive body, with its actual initial-state relation;
it does not on its own choose or relate experiment initialization or larger
strategy classes.

## Construction changes and contexts

For soundness transport from experiment family `E` to `E'`, a strategy
translation has direction:

```text
T : AllowedTargetStrategy → AllowedSourceStrategy.
```

It may also translate parameters and actual instances, with corresponding
statement and assumption laws. An exact transport proves equality of the
relevant event probabilities between `E'(a')` and `E(T(a'))`. A lossy reduction
states its actual inequality, for example:

```text
Pr[E'(a') : Win'] ≤ α * Pr[E(T(a')) : Win] + β,
```

with nonnegative `α,β`, specified dependence on parameters/resources, actual
access used by `T`, and all premises. A source bound `ε` then gives the target
bound `α*ε+β`. This example is a reduction interface, not an assumed inequality
for every transformation. Completeness or simulation transport supplies the
corresponding honest-strategy or simulator connection separately.

A context model fixes linking, code inspection, intervention points, provider
access, artifact release and the final observation. Quantifying over arbitrary
target code requires an explicit target-context class and an argument for all
its members. The context allowed by common-body handler replacement is
narrower. The native representation or local arithmetic theorem alone does
not extend that quantifier.

Fresh interactive challenges and transcript-derived challenges have different
provider experiments. Preserving an arithmetic step in both constructions
does not identify their challenge laws or prove a random-oracle reduction.
The construction selects those obligations at the
[interpretation boundary](../core/interpretations.md), while ordinary local
rewrites use the experiment and context law actually established for them.

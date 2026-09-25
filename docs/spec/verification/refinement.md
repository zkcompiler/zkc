# Refinement and checked transformations

A refinement compares the complete executions of an actual source and target
under selected meanings, inputs, states and observations. Its premises state
where that comparison applies. A checked transformation additionally binds the
externally supplied candidate to the plan for which the rule proves refinement.

## Preservation subjects

Local algorithm refinement concerns computation, state and observation for a
selected source and context. Representation refinement relates different
encodings, values and states of the same logical subject, including failures
and consumed input. Protocol or property transformation changes an experiment
and supplies its property-specific strategy translation, coupling or reduction,
with assumptions and quantitative loss.

These obligations can overlap in one compiler pass. Same-reply handler
replacement alone does not establish a different wire representation. An honest
codec round trip does not establish behavior on hostile wire data. Changing
challenge order, accepted messages or setup requires the corresponding protocol
property argument as well as any local implementation refinement.

## Selected execution models

For a [language](../language/programs.md#language-signatures) `L`, an execution
model consists of:

```text
interface : Signature
meaning   : Interpretation L interface
State     : Type
Event     : Type
handler   : Handler interface State Event
```

For a source program `Γ ⊢ p : τ`, its selected run is:

```text
runSource M p η s = run M.handler (⟦p⟧M.meaning η) s.
```

The selected typed-plan interface uses the
[logical plan evaluator](../profiles/compiler/direct-plan.md#typed-plans):

```text
runPlan M q η s = evaluatePlan M.meaning M.handler q η s.
```

Both produce complete executions. The model fixes actual operation meanings
and a handler. A rule can quantify over a family of such models by supplying
the laws its proof needs; operation spelling does not infer those laws.

The source and target models may use different languages, signatures, value
carriers, states and events. This mathematical source/plan interface does not
require a native compiler to retain two isomorphic IRs. A different target
carrier supplies its evaluator and the corresponding source-relative relation.

## Refinement parameters

Fix source model `Ms`, context `Γ` and result sort `τ`, and target model `Mt`,
context `Δ` and result sort `υ`. Let `EnvS`, `EnvT` be their interpreted context
environments, and let `S, T, A, B` be their respective state and result types.
A refinement policy `ρ` consists of:

```text
initial    : EnvS → S → EnvT → T → Prop
states     : S → T → Prop
values     : A → S → B → T → Prop
Observation : Type
sourceView : Ms.Event → List Observation
targetView : Mt.Event → List Observation
```

The initial relation constrains actual input environments and starting states.
The final state and value relations are independently selected obligations;
initial validity is not inferred from their names or from artifact metadata.
The value relation refers to the actual states left by the runs.

For source `p` and target plan `q`, define:

```text
Holds ρ p q ⇔ ∀ η s ξ t, ρ.initial η s ξ t →
  Relates ρ.states ρ.values ρ.sourceView ρ.targetView
    (runSource Ms p η s) (runPlan Mt q ξ t).
```

`Relates` is the [complete-result representation relation](../realization/representations.md#related-complete-results).
It retains related final states, matching stops, related returned values at
those states, and equal ordered projected events.

## Exact and conditional cases

For one model, context and result sort, the exact policy is:

```text
initial η s ξ t ⇔ η = ξ ∧ s = t
states s t      ⇔ s = t
values a s b t  ⇔ a = b
sourceView e     = [e]
targetView e     = [e].
```

Equality of complete source and plan executions for every environment and state
establishes this policy. In particular, direct lowering satisfies it under the
same actual interpretation and handler.

A conditional policy can restrict initial inputs and states. To use it at an
invocation, the consumer establishes `ρ.initial` for that invocation's actual
operands. An uninhabited initial domain makes the universal proposition vacuous;
it provides no execution conclusion for an arbitrary invocation.

Refinement does not itself prove that the source faithfully expresses an
external mathematical statement. That connection also uses exact
[input binding](../profiles/source/named-inputs.md#exact-ordered-binding) and
[domain adequacy](../domains/values.md#domain-adequacy).

## Advertised input coverage

A refinement's initial relation can be empty. An executable profile that
advertises source inputs additionally supplies an actual binding function and
establishes coverage of that domain. For an admission predicate `admitted`:

```text
bind : EnvS → S → Option (EnvT × T)
covered : ∀ η s, admitted η s → ∃ selected, bind η s = some selected
valid : ∀ η s ξ t, admitted η s → bind η s = some (ξ,t) →
  ρ.initial η s ξ t.
```

Together with `Holds ρ p q`, these laws establish related complete executions
for the target inputs actually selected by `bind`. The advertised predicate
must describe the profile's promised domain; narrowing it changes that promise.
Outside the advertised domain, the profile may reject the input or supply
separate evidence. Coverage of input binding proves neither successful native
execution nor honest protocol acceptance.

Source coverage is a forward obligation. It does not establish adequacy for
every input an independently callable target accepts. Such a claim additionally
binds target admission to a valid decoding, proves correspondence for every
accepted target input, or supplies an equivalent reverse-domain argument. A
target may otherwise have extra accepted inputs unrelated to any source input.

## Remaining consumers

If a later consumer requires the exact source observation `observe`, erasing a
value through `encode` requires a retained consumer satisfying:

```text
∀ s, admitted s → consume (encode s) = observe s.
```

In particular, admitted source values with the same encoding must have the
same required observation. This is observational factorization, as used by the
[locality law](../../../formal/Zkc/Semantics/Locality.lean); it requires neither an inverse
for every source value nor preservation of observations no remaining consumer
uses.

Before a common representation is shared by multiple target routes, its
retention argument covers all remaining consumers of that representation.
Reducing an integer modulo a field characteristic may suffice for a field
consumer while losing information needed by a later integer comparison.
Splitting the routes before that loss permits different representations and
proofs. A [sound analysis summary](analysis.md#summaries-and-exact-consumers)
can lose precision; it does not by itself supply an exact consumer.

## Transformation rules

For a fixed refinement policy `ρ`, a transformation rule consists of:

```text
Certificate : Type
apply       : SourceProgram → Certificate → Option TargetPlan
sound       : ∀ p c q, apply p c = some q → Holds ρ p q.
```

`SourceProgram` and `TargetPlan` have the model, context and result parameters
fixed above. `apply` is partial in the sense that it can return `none`; as a
mathematical function it is defined on every supplied program and certificate.
`sound` concerns every plan it returns for those actual inputs.

Generating a certificate does not prove soundness. A rule with no search data
can use a singleton certificate type. The generic interface imposes no finite
certificate codec, external rule registry, parser or native backend theorem.
An external profile resolves its actual rule and certificate to this interface.

## Checking the actual candidate

For a retained source `p` and raw candidate `raw`, a checked transformation
contains:

```text
plan    : TargetPlan
decoded : decodePlan Δ υ raw = ok plan
correct : Holds ρ p plan.
```

Assume decidable equality of target sorts and operation descriptors. The
selected rule checker is:

```text
check rule p c raw =
  match accepted : rule.apply p c with
  | none => none
  | some q =>
      if erase q = raw then
        some (q, decoding evidence for raw, rule.sound p c q accepted)
      else none.
```

The decoding evidence follows from typed plan erasure and exact candidate
equality. Every successful result therefore binds this source, this raw
candidate and the actual plan returned by the rule. If the same raw candidate
decodes under the same context and result sort to another plan, that plan
equals the retained checked plan.

A nonmatching candidate is unsupported by this rule; rejection is not proof
that no refinement could hold for it. Rejection selects no fallback executable.
The candidate cannot choose a different operation interpretation to justify
itself. The consumer supplies the models and the resolved rule.

The erasure comparison concerns raw structured data. A claim about external
bytes also supplies the profile's parsing, encoding and custody correspondence.
Decoding uniqueness alone does not prevent a native caller from replacing the
checked object unless the actual admission-to-use boundary enforces that binding.

## Composition and observation

Sequential replacement establishes suffix correspondence from the prefix's
actual related returned values and residual states. The
[represented sequencing rule](../realization/representations.md#sequencing-represented-values)
gives a sufficient universal premise. A stopped prefix executes neither suffix.

Successive transformations compose through the same actual intermediate run,
value interpretation and observation. If the first produces a plan and the
second consumes source syntax, an applicable equality or representation bridge
connects those two middle subjects before applying
[transitive composition](../realization/representations.md#transitive-composition).
Two independently certified transformations with incompatible intermediate
subjects do not acquire that bridge from certificate names.

Initial-domain composition likewise supplies a common intermediate environment
and starting state satisfying both initial relations. For related endpoint
inputs, those witnesses determine the intermediate run used in both premises.
The final relation then uses that run's actual residual state and returned value.

An observer can be weakened by a justified projection. A property transports
through execution refinement only when its experiment and conclusion are
determined by the selected relation or a separate theorem supplies the required
transport. Projected event equality alone is not a cryptographic reduction.

## Interpreted operation laws

An algebraic rewrite uses laws of its actual interpreted operations, preserving
their operand order and the surrounding effectful computation. It cannot rely
on names such as `add` or `quadratic` being interpreted as expected.

*Example.* The selected arithmetic interpretation gives quadratic evaluation
the pure result `a + (b * r + c * (r * r))`. Over a semiring it equals
`a + (b + c * r) * r`. The Horner rule expands the operation into two ordered
multiplications and two additions and preserves the original continuation's
captures. Its law needs neither a field nor commutative multiplication. The
arbitrary supplied effectful invocation remains fixed, including any stop,
state mutation or event it produces.

Factor reuse additionally requires valid facts, actual availability and
justified state transfer. The [typed factor rule](../profiles/compiler/factor-preparation.md#typed-factor-rule)
defines these premises on the actual module implementations and proves
complete-execution preservation under its guarded handler. The common
refinement judgment applies that law to the selected initial domain and
candidate.

## Effects and admission timing

Reordering, eliminating or specializing operations preserves the selected
outcome, state and observation relation and any required admission behavior.
Equal arithmetic returns do not permit discarding failed prefixes, provider
consumption or source checks. Draws, commits, public failures and mutable
operations require their actual effect laws.

Before erasing a meaningful source distinction, an implementation retains its
interpretation, establishes it at a checked boundary, justifies its erasure,
or refuses the unsupported target. Static specialization uses its declared
available inputs. Runtime specialization has an explicit stage, lifetime and
disclosure contract. A provenance label is not an erasure theorem.

The quantified execution relation states the runs it compares. If a claim also
covers pre-execution formation or admission failures, it supplies that boundary's
correspondence explicitly; a theorem quantified only over already-formed source
programs does not automatically prove it.

Phase admission also concerns every interface-typed reply, rather than only runs
under a selected handler. Combining source phase evidence with an execution
refinement requires a law transporting that admission to the actual target, or
separate target admission evidence. The [phase interpretation law](../core/interpretations.md#phase-admission)
and the [finite phase realization](../profiles/compiler/finite-phases.md#realizing-a-policy)
state the relevant operation and phase premises. A decoded source certificate
and equality under one handler do not supply those premises.

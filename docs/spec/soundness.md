# Soundness Kernel

Status: **normative v0.5 core semantics, including the separate completeness
track**. The Soundness Kernel consists of an immutable native signature, closed
runtime values, `RULE_WF`, occurrence-specific `APPLY`, plan-driven `DERIVE`,
and PIR projection. The signature is the only theorem authority: the artifact
carries no theorem citation, and no registry, policy snapshot, or certificate
can author a `SecurityJudgment`. Soundness and completeness are distinct
conditional notions throughout the type model; neither judgment establishes
the other.

## 1. Scope and placement

The Protocol Kernel decides whether a finite protocol is structurally valid
and seals its identity. The Soundness Kernel is a sibling service after seal:

```text
sealed protocol + soundness context + explicit derivation plan
  -> conditional security result
```

It answers one question: *what exact conditional security judgment follows
from these typed rule applications?*

It does not:

- prove a paper theorem or its faithful encoding;
- prove a cryptographic game assumption or an external proposition;
- decide runtime admission policy;
- infer an application relation that the protocol does not contain;
- search for, optimize, or silently choose a derivation;
- define certificate, evidence, release, or migration machinery; or
- claim whole-application or backend soundness.

Protocol identity therefore does not depend on a soundness analysis. Every
soundness-dependent consumer, including the compiler, must nevertheless use
this one evaluator.

## 2. Central abstraction

The single semantic principle is:

> A `SoundnessRule` is a typed conditional monotone map from notion-indexed
> premise security results to one notion-indexed conclusion security result.

An application is meaningful only at an exact site in a sealed artifact:

```text
SoundnessRule
+ RuleBinding
+ ApplicationSite
+ resolved sealed facts
+ typed premise judgments
  -> SecurityJudgment
```

The kernel has two reusable catalog declarations:

- `SoundnessRule`, the reusable conditional transformation; and
- `RuleBinding`, the mapping from that rule to an exact protocol schema.

A context, an explicitly asserted external premise, and a derivation plan are
caller inputs, not additional theorem authorities. Applied judgments and
evaluated derivation trees are kernel outputs. An assumed judgment is a typed
marker-free caller input whose canonical `AssumedJudgmentHolds` proposition is
constructed and retained as a hypothesis, never a kernel-derived fact.

## 3. Notion-indexed judgments

### 3.1 Subjects and sites

Security subjects are a closed tagged sum:

```text
SecuritySubject :=
    ProtocolClaim {
      artifact_id,
      claim_ref
    }
  | ConsumedClaimVector {
      artifact_id,
      consumer_claim_ref,
      ordered_source_claim_refs
    }
  | ExternalInstance {
      subject_schema,
      typed_arguments
    }
```

`ProtocolClaim` is the ordinary result subject. `ConsumedClaimVector` is
required for reductions, such as KZG batching, whose premise ranges over an
ordered family of consumed source claims rather than one same-subject claim.
`ExternalInstance` is for a typed object not represented as a protocol claim,
such as a scheme/SRS instance. Its schema and arguments must be declared in the
context; it is not an opaque dictionary.

An `ApplicationSite` is separate and tagged:

```text
ApplicationSite :=
    ReductionOccurrence {
      artifact_id,
      owner_claim_ref,
      transformer_position,
      output_index
    }
  | PathOccurrence {
      artifact_id,
      claim_ref
    }
```

The site identifies an occurrence. The subject identifies what the resulting
judgment is about. A path occurrence identifies only an exact artifact and
claim; the enclosing `Apply` node separately selects the binding that gives the
application its semantics. A reduction occurrence additionally includes
transformer position and output index.

The conclusion subject is constructed by the kernel, not supplied by the
caller or binding:

```text
subjectOf(sealed, ReductionOccurrence(site)) =
  ProtocolClaim(
    sealed.artifact_id,
    resolveReductionOutput(
      sealed,
      site.owner_claim_ref,
      site.transformer_position,
      site.output_index))

subjectOf(sealed, PathOccurrence(site)) =
  ProtocolClaim(sealed.artifact_id, site.claim_ref)
```

Resolution is exact and must name one claim in the sealed artifact. The
artifact identifier in the site must equal `sealed.artifact_id`. A binding's
`subject_schema` validates the derived subject; it never constructs or
overrides it. Direct rule application therefore always concludes about an
exact protocol claim. `ConsumedClaimVector` and `ExternalInstance` are premise
subjects in v0.

### 3.2 Security indices

`SecurityIndex` is an admitted tagged sum, not a free Cartesian product of
strings:

```text
SecurityIndex :=
    SpecialSoundness {track}
  | ComputationalSpecialSoundness {track}
  | RoundByRound {track, admitted_variant}
  | StateRestoration {track, admitted_variant}
  | FiatShamir {track, admitted_model, admitted_variant}
  | Completeness {}
```

The admitted `track` values are `soundness`, `knowledge`, and `completeness`.
Only combinations listed by the versioned vocabulary are admitted. In
particular, a rule cannot invent a model, variant, track, or bridge by
composing strings. The completeness notion and track come together or not at
all: a completeness judgment prices honest-prover acceptance and says
nothing about any adversary, so its index must never read as a soundness or
knowledge claim, and no soundness notion may borrow the completeness
spelling — an index mixing them has an impossible kernel shape.

The computational regime is derived from the quantitative result:

```text
Regime := IT | Comp(set<PrimitiveGameInstance>)

regime(result) =
  IT                                      if gameSupport(result) is empty
  Comp(gameSupport(result))                otherwise
```

`gameSupport` is the structural set of exact primitive-game instances in the
closed result bound, including instances inside substituted premise bounds.
It is computed before any resource valuation and retains a syntactically
present term even when some valuation could make its coefficient zero. A rule,
binding, context, or external input cannot choose, lower, or overwrite the
regime.

### 3.3 Typed security results

There is no universal “payload plus scalar bound.” The result is indexed by
the security notion:

```text
SecurityResult :=
    ExtractionResult {
      coordinates: nonempty ordered [
        {label, arity, optional challenge_space}
      ],
      failure_bound: optional ClosedBound
    }
  | RoundResult {
      rounds: nonempty ordered [
        {round_index, challenge_space, bound: ClosedBound,
         optional state_predicate}
      ]
    }
  | ScalarResult {
      bound: ClosedBound
    }
```

The schema is fixed:

| Index | Required result |
|---|---|
| `SpecialSoundness` | `ExtractionResult` with no failure bound |
| `ComputationalSpecialSoundness` | `ExtractionResult` with a failure bound |
| `RoundByRound` | `RoundResult` |
| `StateRestoration` | `ScalarResult` |
| `FiatShamir` | `ScalarResult` |
| `Completeness` | `ScalarResult` |

Round bounds have no independent aggregate field. The projection

```text
roundMaximum(RoundResult) = Max(round.bound for round in rounds)
```

is derived when a later rule explicitly requests it. An IT extraction result
similarly does not carry a decorative zero bound.

Round-by-round soundness is defined over a state function on partial
transcripts — the empty transcript is alive, a doomed transcript stays doomed
except with the round's probability, and a doomed full transcript is rejected.
The `state_predicate` names that function rather than leaving it implicit in
the bound:

```text
state_predicate := claim_unsatisfied(claim_ref)
```

is the one admitted form: the state is doomed exactly when the named claim is
unsatisfied. The predicate is computed, not declared — rounds built at a
reduction occurrence name the site's owner claim, since that claim is what the
rounds argue, and rounds built anywhere else carry no predicate rather than a
default, since no claim is consumed there. A rule that concatenates round
sequences from two occurrences keeps each entry's own predicate, which is why
the predicate is a field of the entry and not of the result: the composed
transcript dooms on different claims over different spans, and that fact is
the claim graph restated rather than a new obligation.

### 3.4 Hypotheses

`Hypothesis` represents a qualitative proposition:

```text
Hypothesis {
  proposition_schema,
  typed_arguments
}
```

Examples include setup conditions, algebraic conditions, model assumptions,
and theorem-side facts without a machine decider. A primitive advantage term
is quantitative and is **not** duplicated as a Boolean hypothesis.

Every application inherits hypotheses monotonically:

```text
conclusion hypotheses
  = union(all specialized premise hypotheses,
          instantiated local external hypotheses,
          canonical AssumedJudgmentHolds propositions for assumed premises)
```

Here “specialized” means after the premise port's total resource substitution
has been applied. The rule transform cannot select this set. Removing or
discharging a hypothesis requires a future explicit rule whose conclusion
states that effect; no v0 rule does so.

The truth and faithful encoding of a `SoundnessRule` and `RuleBinding` are
meta-level antecedents of the kernel interpretation. `RULE_WF` does not prove
them. They must be stated explicitly and do not become kernel evidence or
derivability inputs.

### 3.5 Judgment and meaning

```text
SecurityJudgment {
  subject: SecuritySubject,
  index: SecurityIndex,
  result: SecurityResult,
  resource_variables: typed declarations,
  hypotheses: set<Hypothesis>      // kernel-derived
}
```

`regime(result)` is a derived projection, not an independently stored field.

Each admitted index defines a predicate
`Holds_index(subject, result, resource_valuation)`. A judgment means:

```text
for every non-negative, well-typed resource valuation,
  if all qualitative hypotheses hold,
  then Holds_index(subject, result, valuation).
```

An integer resource is assigned an exact non-negative integer and a rational
resource an exact non-negative rational. Zero is admitted. Consequently, a
v0 structural arity or challenge-space expression is an exact, strictly
positive, resource-free integer. Bounds and primitive-game resource
substitutions may depend on resources and may be zero, but never negative
under the admitted valuations.

Primitive-game advantages occurring in `result` remain symbolic quantitative
leaves in this statement. The exact definitions of `Holds_index` and each
primitive game are part of the admitted semantic context. A free-form prose
description is not executable semantics.

For the completeness index, `Holds` quantifies over the honest prover
rather than an adversary: an honest prover holding a witness in the
subject's relation is accepted except with probability at most the scalar
bound (0 is perfect completeness). Completeness and soundness are separate
results in every record: a subject may carry either, both, or neither, and
soundness without completeness is reported as exactly that.

## 4. Exact expressions and bounds

Rule templates and closed results are different syntactic categories.
Evaluation may not leave catalog parameters, fact ports, or premise selectors
inside a `SecurityJudgment`.

### 4.1 Exact quantities

Quantity expressions are rational-valued. Intermediate expressions may be
signed; non-negativity is checked at the result position that requires it.

```text
QuantityTemplate :=
    Rat(numerator, positive_denominator)
  | Parameter(name)
  | ArtifactFact(port)
  | ContractRoundFact(case_name, admitted_round_field)
  | PremiseCoordinate(port, selector)
  | ResourceVariable(name)
  | Add(nonempty [QuantityTemplate])
  | Sub(QuantityTemplate, QuantityTemplate)
  | Mul(nonempty [QuantityTemplate])
  | Div(QuantityTemplate, QuantityTemplate)
  | Pow(QuantityTemplate, integer-valued QuantityTemplate)
  | Pow2(integer-valued QuantityTemplate)
  | Pow2Up(half-integer-valued QuantityTemplate)
```

`ClosedQuantity` has the same constructors but permits only rational literals
and declared resource variables as leaves.

`ContractRoundFact` is legal only inside a contract-derived sequence case in
§5.1. It reads one of `ChallengeSpace`, `ChallengeCount`, `RoundDegree`, or
`ChallengeSpaceLog2` from the case's currently matched authenticated contract
round.
It is a lexical binder, not a string path.

The grammar is total only under explicit domains:

- denominators are nonzero;
- integer and half-integer requirements hold exactly;
- exponentiation is defined for the resolved base and exponent, and every
  resolved v0 exponent is in the closed interval `[-4096, 4096]`;
- every final probability, challenge-space size, arity, scale, and bound is in
  its declared non-negative or positive domain; and
- overflow or an unsupported exact representation refuses.

These are typed checks or named machine conditions. “Checked arithmetic” is
not an escape constructor. `Pow2(x) = 2^x` for an integer `x`, while
`Pow2Up(x) = 2^ceil(x)` is the explicit outward dyadic bound for half-integer
`x`.

### 4.2 Rule bounds

Primitive games separate their fixed semantic instance from their
computational-resource coordinates:

```text
PrimitiveGameDefinition {
  game_ref,
  ordered_instance_argument_types,
  resource_schema
}

PrimitiveGameInstanceTemplate {
  game_ref,
  ordered_instance_arguments: [BindingValue]
}

PrimitiveGameInstance {
  game_ref,
  ordered_closed_instance_arguments: [typed_value]
}
```

Each instance argument is a direct typed `BindingValue` from §5.2. Instance
arguments identify such values as the group, field, SRS, degree limit, or
adversary class. Resource variables such as time or query count are not
hidden inside those arguments; they are mapped separately by the total
resource substitution.

```text
RuleBound :=
    Quantity(QuantityTemplate)
  | ScalarBound(premise_port)
  | PrimitiveAdvantage(
      instance_template: PrimitiveGameInstanceTemplate,
      resource_substitution)
  | Add(nonempty [RuleBound])
  | Scale(nonnegative QuantityTemplate, RuleBound)
  | Max(nonempty [RuleBound])
```

A projection of a premise result is admitted only for a schema some body can
place in a bound. The bodies with a free bound slot take no premise, a
special-soundness premise, or a state-restoration premise, so `ScalarBound` is
the only one reachable and it is the only one declared. Projections of
extraction-failure and per-round results are what a composition body would
need; they are introduced with that body rather than kept ahead of it, because
a constructor no declaration can form is evaluator surface that must still be
trusted and formalized.

```text
ClosedBound :=
    Quantity(ClosedQuantity)
  | PrimitiveAdvantage(exact_game_instance, closed_resource_substitution)
  | Add(nonempty [ClosedBound])
  | Scale(nonnegative ClosedQuantity, ClosedBound)
  | Max(nonempty [ClosedBound])
```

There is no generic error atom. A statistical error is an exact quantity. A
computational term is a named primitive-game advantage. A premise selector is
typed by the premise result schema, so, for example, a rule cannot read a
scalar bound from an extraction result.

For a selected primitive-game definition, `RULE_WF` requires the template's
argument count and types to equal `ordered_instance_argument_types` and its
resource substitution to be total over `resource_schema`. `APPLY` resolves
every direct `BindingValue` and closes the bound by:

```text
resolveInstance(
  PrimitiveGameInstanceTemplate(game_ref, arguments),
  environment)
= PrimitiveGameInstance(
    game_ref,
    [resolve(argument, environment) for argument in arguments])

close(PrimitiveAdvantage(instance_template, resource_substitution))
= PrimitiveAdvantage(
    resolveInstance(instance_template, environment),
    closeResourceSubstitution(resource_substitution, environment))
```

Every resolved argument must be a closed value of the definition's
corresponding type. A missing definition, extra or missing argument, ill-typed
argument, unresolved value source, or partial resource substitution refuses.
Thus a display-level game name can never stand in for an exact game instance.

These constructors are monotone in premise bounds. Subtraction, division,
products, and powers are available only inside exact quantity coefficients,
never around premise bounds or primitive advantage terms.

### 4.3 v0 executable normal form

The abstract bound tree is closed and inspectable. The executable normal form
admits exactly the part that normalizes to the following graded-linear form:

```text
ground rational
+ sum(exact rational coefficient * PrimitiveAdvantage instance)
+ sum(exact rational coefficient * resource_variable^positive_integer)
```

All coefficients must be non-negative. A product may contain at most one
symbolic-valued factor; divisors must be ground and nonzero. A `Max` is admitted
only when all alternatives resolve to ground rationals. Unsupported symbolic
products, symbolic maxima, negative coefficients, or inexact powers refuse;
they are never approximated.

This normal-form boundary is not a second semantics. A later version may extend
what `ClosedBound` can decide without changing the rule principle.

## 5. Rules, bindings, and contexts

### 5.1 Rule declarations

Conditions and local hypotheses have closed signatures:

```text
MachineConditionTemplate {
  condition_slot,
  predicate_ref,
  ordered_argument_types
}

ExternalHypothesisTemplate {
  hypothesis_slot,
  proposition_schema,
  ordered_argument_types
}
```

The rule fixes the predicate or proposition identity and its ordered typed
signature. A binding supplies only the argument values. Slots are unique
within a rule; argument arity and types must match exactly.

```text
SoundnessRule {
  rule_ref,
  status: admitted | declared,
  typed_parameters,
  typed_resource_variables,
  premise_ports,
  artifact_fact_ports,
  machine_condition_templates,
  external_hypothesis_templates,
  exact_parameter_pins,
  conclusion_index,
  body: RuleBody
}
```

`status` records whether this signature offers the rule for execution. A
`declared` rule is well-formed and inspectable but unreachable: no binding may
name it, so no derivation can apply it, and binding well-formedness refuses
one that tries. The mechanism is the one section 5.4 already gives a rule with
no selected binding; status makes the condition declarable rather than
incidental, and it unifies two cases that were otherwise unlike — a rule whose
cited theorem was refuted, and a rule that exists only to state what a
provider supplies.

Status is declaration content and enters the declaration digest, because
anything with effect is content: otherwise two signatures with the same digest
could offer different executable rules, and naming a signature by its digest
would stop identifying an analysis. It is a signature-authoring decision, not
a judgment about whether the cited theorem is true. `RULE_WF` certifies no
validity class; a declared rule is unreachable because no binding names it,
not because the evaluator inspects a claim about the world. Reproducing a
superseded analysis is done by naming the historical signature under which it
was produced.

`RuleBody` is a closed algebraic variant, not an arbitrary callback:

```text
RuleBody :=
    SpecialSoundnessEntry
  | NativeRoundByRoundEntry
  | ComputationalEntry
  | CompletenessEntry
  | SpecialSoundnessPreservation
  | RoundByRoundPreservation
  | RoundScaling
  | SpecialSoundnessToRoundByRound
  | RoundByRoundToStateRestoration
  | StateRestorationToFiatShamirDuplex
```

Each body has one exact index signature:

| Body | Premise indices | Conclusion index |
|---|---|---|
| `SpecialSoundnessEntry` | none | `SpecialSoundness{track}` |
| `NativeRoundByRoundEntry` | none | `RoundByRound{track, variant}` |
| `ComputationalEntry` | none | `ComputationalSpecialSoundness{track}` |
| `CompletenessEntry` | none | `Completeness{}` |
| `SpecialSoundnessPreservation` | one `SpecialSoundness{track}` | `ComputationalSpecialSoundness{same track}` |
| `RoundByRoundPreservation` | one `RoundByRound{track, variant}` | the exact same RBR index |
| `RoundScaling` | one `RoundByRound{track, variant}` | the exact same RBR index |
| `SpecialSoundnessToRoundByRound` | one `SpecialSoundness{track}` | `RoundByRound{same track, declared variant}` |
| `RoundByRoundToStateRestoration` | one `RoundByRound{track, variant}` | `StateRestoration{same track, same variant}` |
| `StateRestorationToFiatShamirDuplex` | one `StateRestoration{track, variant}` | `FiatShamir{same track, same variant, the admitted duplex model}` |

Extra premise ports refuse. The table is stronger than result-schema
compatibility: in particular, sharing `ScalarResult` does not permit FS→SR,
SR→SR, or FS→FS under either scalar body.

The supporting sequence templates are closed:

```text
CoordinateTemplate {
  label: literal label,
  arity: positive-integer QuantityTemplate,
  challenge_space: optional positive-integer QuantityTemplate
}

RoundTemplate {
  round_index: literal index,
  challenge_space: positive-integer QuantityTemplate,
  bound: RuleBound
}

ContractRoundSelector :=
    AllContractRounds
  | RoundKind(exact_kind)
  | RoundPosition(nonnegative_integer)

ContractCoordinateCase {
  case_name,
  selector: ContractRoundSelector,
  label_projection: RoundIndex | RoundKindOccurrence | CaseName
                  | SiteQualifiedRoundIndex,
  arity_template,
  challenge_space_template
}

ContractRoundCase {
  case_name,
  selector: ContractRoundSelector,
  index_projection: RoundIndex | RoundKindOccurrence | CaseName
                  | SiteQualifiedRoundIndex,
  challenge_space_template,
  bound_template
}
```

`SiteQualifiedRoundIndex` prefixes the contract-local index with the
occurrence's canonical transformer position.  The first three projections are
functions of the pinned contract and the case alone, so every occurrence of one
contract produces the same labels; a row that composes two occurrences cannot
tell their rounds apart and refuses on the duplicate.  Qualification is opt-in
per case, so a row that does not compose keeps contract-local labels and its
witness is unchanged.

Two selectors cannot reach into a qualified sequence:
`RoundSelector.ByRoundIndex` and the compiler's exact round projection both
name a round by a literal index, while a qualified index contains an artifact's
transformer position, which a reusable declaration must not carry.

```text
CoordinateSequence :=
    ExplicitCoordinates(nonempty ordered [CoordinateTemplate])
  | ContractCoordinates {
      contract_fact_port,
      cases: nonempty ordered [ContractCoordinateCase]
    }

RoundSequence :=
    ExplicitRounds(nonempty ordered [RoundTemplate])
  | ContractRounds {
      contract_fact_port,
      cases: nonempty ordered [ContractRoundCase]
    }
```

`CaseName` names the output entry after the case that matched. A heterogeneous
contract needs that name when several rounds collapse into one coordinate,
because neither a round index nor a kind occurrence gives the appended
coordinate a stable name.

Each case lexically binds `CurrentContractRound(case_name)`;
`ContractRoundFact(case_name, field)` reads only that bound round. Resolution
walks contract rounds in contract order and requires every round to match
exactly one case and every case to match at least one round.
`AllContractRounds` is legal only when it is the sole case. `RoundKind`
requires every contract round to have a kind and matches by exact equality;
`RoundPosition` is the closed fallback for position-specific unkinded
contracts. An overlap, gap, unused case, partially kinded kind-match, or
out-of-range position refuses.

This closed matching law expresses both homogeneous rows (one
`AllContractRounds` case) and heterogeneous FRI rows (exact `fold` and
`query` cases) without a callback or binding-specific expansion. Output order
is always contract order.

The admitted contract-wide artifact projections in v0 are
`FoldRoundCount` and other fields explicitly listed by the selected contract
fact schema. The admitted per-round projections are `RoundIndex`,
`RoundKind`, `ChallengeSpace`, `ChallengeCount`, `RoundDegree`, and
`ChallengeSpaceLog2`. Selectors and projections above are enum cases over the
sealed contract schema, not callbacks or string paths.

The only admitted dynamic round selector is:

```text
RoundSelectorTemplate :=
    ByRoundIndex(exact_index)
  | AdjacentPredecessorRound(authenticated_adjacency_fact_port)
```

`SpecialSoundnessToRoundByRound` binds a finite
`CoordinateIndex(source_port)` variable inside its
`per_coordinate_bound`; this is the sole meaning of the notation `[i]` below.
No free string selector or general iterator is admitted.

The closed body records and their evaluation equations are:

In these equations every `premise_port` denotes the specialized premise view
defined in §5.2, never the raw child judgment.

```text
SpecialSoundnessEntry {
  coordinates: CoordinateSequence
}

result =
  ExtractionResult(resolve(coordinates), failure_bound = none)
```

```text
NativeRoundByRoundEntry {
  rounds: RoundSequence
}

result =
  RoundResult(resolve(rounds))
```

```text
ComputationalEntry {
  coordinates: CoordinateSequence,
  failure_bound: RuleBound
}

result =
  ExtractionResult(resolve(coordinates),
                   failure_bound = close(failure_bound))
```

```text
CompletenessEntry {
  bound: RuleBound
}

result =
  ScalarResult(close(bound))
```

```text
SpecialSoundnessPreservation {
  source_special_soundness_port,
  appended_coordinates: CoordinateSequence,
  conclusion_failure_bound: RuleBound
}

result.coordinates =
  source_special_soundness_port.coordinates
  ++ resolve(appended_coordinates)

result.failure_bound =
  close(conclusion_failure_bound)
```

Its source port must be `SpecialSoundness`, and coordinates are appended in
the stated order and must remain unique.

```text
RoundByRoundPreservation {
  source_round_by_round_port,
  appended_rounds: RoundSequence
}

result.rounds =
  source_round_by_round_port.rounds
  ++ resolve(appended_rounds)
```

No bound is combined. The composed error is a reindexing of the components'
error functions, not their sum and not their maximum, so every round keeps the
bound its own component gave it and the sequence is their concatenation.

For a KZG preservation rule, the conclusion failure is the whole cited
reduction bound:

```text
Adv^EB(tau_eb) + Adv^DB(tau_db)
```

or

```text
Adv^ARSDH(tau_arsdh) + Adv^ARSDH(tau_arsdh)
  = 2 * Adv^ARSDH(tau_arsdh)
```

respectively. The cited preservation result does not consume the separate KZG
PCS computational-special-soundness result; adding that failure would
double-count a theorem-independent bound. A preservation row therefore
declares exactly one source special-soundness premise over the consumed claim
vector. The standalone PCS provider remains an independent zero-binding
external-judgment schema, but it is a catalog declaration and is not directly
executable. A preservation rule may not insert it as another premise.

The `EB + DB` atoms retain their separate exact adversary-resource
substitutions through `tau_eb` and `tau_db`. Reusing one display symbol does
not prove those substitutions equal. The collapsed sibling encodes two
separate ARSDH leaves whose substitutions both name the declared common upper
bound `tau_arsdh`; exact normalization then combines those identical leaves to
coefficient two. This does not identify `tau_arsdh` with either EB/DB
coordinate.

The Vandermonde-coefficient condition remains an explicit qualitative external
hypothesis. Degree-within-SRS, exact algebra correspondence, and SRS-ceremony
provenance remain explicit hypotheses. The structural same-point and
transcript-ordering deciders below do not discharge any of them.

```text
RoundScaling {
  round_by_round_port,
  selected_round: RoundSelectorTemplate,
  scale: nonnegative QuantityTemplate
}

result.rounds[j] =
  if j = selected_round
  then {same index and challenge space,
        bound = close(Scale(scale, premise.rounds[j].bound))}
  else premise.rounds[j]
```

Exactly one round must be selected. Every unselected round, its index, its
challenge space, and its bound are preserved byte-for-value in the typed
result. `ByRoundIndex` selects the unique textual round label.
`AdjacentPredecessorRound` instead selects the authenticated predecessor-round
ordinal and requires that the adjacency fact name the exact consumed
round-by-round premise claim; an ordinal is never reinterpreted as a textual
round label.

```text
SpecialSoundnessToRoundByRound {
  special_soundness_port,
  per_coordinate_bound: RuleBound with bound coordinate i
}

result.rounds[i] = {
  round_index = coordinate[i].label,
  challenge_space = coordinate[i].challenge_space,
  bound = close(per_coordinate_bound[i])
}
```

Every source coordinate must have a challenge space; order and cardinality are
preserved. The body instantiates `(arity[i] - 1) / challenge_space[i]`.

```text
RoundByRoundToStateRestoration {
  round_by_round_port,
  move_budget: nonnegative QuantityTemplate
}

result =
  ScalarResult(
    close(Scale(move_budget, max over j of premise.rounds[j].bound)))
```

```text
StateRestorationToFiatShamirDuplex {
  state_restoration_port,
  local_duplex_bound: RuleBound
}

result =
  ScalarResult(
    close(Add(ScalarBound(state_restoration_port),
              local_duplex_bound)))
```

`local_duplex_bound` contains only the construction-specific capacity and
codec-bias terms; it cannot reread or replace the premise scalar. Thus the
premise loss is inherited exactly once.

One of its terms is not a sponge quantity: a protocol that binds a relation
identity into its transcript does so through the 216-bit anchor projection
(`relations.md` §2.8), and the shortfall of that binding is a computational
quantity. The duplex bound therefore carries the named advantage
`Adv^CR[sha256-216]` scaled by the artifact's bound-relation-anchor count — a
projection of the sealed artifact, not a declaration — so the addend is
exactly zero for a protocol that binds no relation identity and one advantage
term per bound anchor otherwise. The non-interactive argument is where the
truncated value is all a verifier checks, which is why the addend lives on
the Fiat-Shamir step rather than on the interactive rounds.

`resolve` evaluates a sequence template against authenticated facts. `close`
performs typed substitution and produces a `ClosedBound`; failure to close
refuses. Duplicate coordinate labels, duplicate round indices, absent
challenge spaces, empty output, or a result/index mismatch refuse.

`RoundByRoundPreservation` concatenates the premise's round sequence with its
own resolved rounds and refuses a duplicate index **across the join**, not only
within either side. Its conclusion is the premise index exactly: it cannot
shift the notion, and concatenating two sequences priced under different
variants would mean nothing.

Two further conditions are enforced by that body rather than by the signature,
and are recorded here because a body-level guard is invisible to a reader of a
rule declaration. The composition it performs is stated over a transcript whose
components occupy contiguous blocks in spine order, and a claim edge does not
imply that — the spine and the claim graph are independent and bodies may
interleave (kernel.md §1.4). So the body requires that the premise occurrence's
rounds all precede the conclusion occurrence's in the spine, and that every
challenge inside the composed span belongs to one of the two occurrences. An
unowned squeeze between them is one the composed error function does not index,
and pricing around it would price a protocol that is not the one composed.

Three limitations of that pair are deliberate and named, and the first is
narrower than it reads at first sight. Both guards locate the premise's
transcript block by the *subject claim*: they find the reduction that produced
it. So a premise about an artifact source claim has no producing occurrence
and the composition refuses. A premise established at a path occurrence, or
asserted by an assumption, about a claim some reduction did produce is **not**
distinguished — a `SecurityJudgment` carries no site, so the guards see that
reduction's rounds and compose against them. What the guards establish is
therefore a property of the subject claim's producer, not of the derivation
step that supplied the premise; a plan that reaches a produced claim by a path
application or an assumption is checked against the producing occurrence's
span rather than refused. Distinguishing the supplying derivation step requires
threading the premise's own site into the judgment. Second, the span condition
is over squeezes only, so message interleaving inside an otherwise well-ordered
span is unguarded; representing that distinction requires per-occurrence
message positions. And third, the span condition reads the artifact's squeeze
facts, so a purely interactive artifact carrying none refuses rather than
composing.

The round-scaling body's authenticated ordinal is a position in the premise
reduction's own contract round list, so it selects the intended round only
while the premise result is that reduction's rounds one for one. A composed
premise is longer, and the range check alone would pass while the scale landed
on another component's round, so the requirement is checked — by cardinality:
the premise result must have exactly as many rounds as the premise reduction's
contract declares. That refuses every composed premise, which is the case it
exists for. It does not establish positionwise identity: a premise result with
the right number of rounds in another order would still be scaled at the
ordinal. Admitting such a premise requires an explicit identity relation
between rounds in the two representations, which is a kernel question rather
than a tightening.

These are the admitted body shapes. Adding another variant is a
specification change with a defined result schema and evaluator, not a
free-form extension field.

A rule fixes the machine predicate identifiers and external proposition
schemas it requires. A binding supplies their typed arguments; it cannot swap
in a different decider or proposition.

### 5.2 Premise ports and bindings

A v0 premise port consumes exactly one judgment:

```text
PremisePort {
  name,
  expected_subject_schema,
  expected_index,
  expected_result_schema,
  expected_resource_declarations,
  result_constraints: set<PremiseResultConstraint>,
  resource_substitution:
    map<premise_resource,
        QuantityTemplate over conclusion resources>
}

PremiseResultConstraint :=
    RequiresEmptyGameSupport
  | RequiresNoBoundResourceSupport
```

`RequiresEmptyGameSupport` is a structural predicate over the closed premise
result, not an authored regime. `RequiresNoBoundResourceSupport` requires every
premise bound coordinate to be ground after closure. The v0
`RoundByRoundToStateRestoration` body requires both because multiplying the
premise's round maximum by the formal move budget would otherwise create
`resource * PrimitiveAdvantage` or a product of resource variables, outside
the admitted graded-linear normal form. The admitted body therefore accepts
only ground information-theoretic premises. A later normal-form extension may
remove these constraints explicitly; v0 never silently drops or approximates
a term.

```text
ConsumedClaimSelector :=
    ReductionInput(nonnegative_operand_index)

ConsumedClaimVectorSelector :=
    AllReductionInputs
  | ReductionInputs(nonempty ordered [nonnegative_operand_index])

SubjectRelation :=
    SameSubject
  | ConsumedClaim {
      selector: ConsumedClaimSelector
    }
  | ConsumedClaimVector {
      selector: ConsumedClaimVectorSelector
    }
  | ExactExternalSubject {
      subject_schema,
      typed_argument_pattern
    }
```

Subject relation and child origin are orthogonal. An `Apply` child derives its
judgment; an `Assume` child asserts it conditionally. Thus grinding uses
`Apply + ConsumedClaim`, while the first KZG slice uses
`Assume + ConsumedClaimVector`.

Consumed selectors are legal only at a `ReductionOccurrence`. Let
`output_claim_ref` be the claim constructed by `subjectOf(sealed, site)`.
Their exact subjects are:

```text
select(ConsumedClaim(ReductionInput(i)), sealed, site) =
  ProtocolClaim(
    sealed.artifact_id,
    resolveReductionInput(sealed, site, i))

select(ConsumedClaimVector(AllReductionInputs), sealed, site) =
  ConsumedClaimVector(
    sealed.artifact_id,
    output_claim_ref,
    allReductionInputClaimRefs(sealed, site) in operand order)

select(ConsumedClaimVector(ReductionInputs(indices)), sealed, site) =
  ConsumedClaimVector(
    sealed.artifact_id,
    output_claim_ref,
    [resolveReductionInput(sealed, site, i) for i in indices])
```

Every operand position must be in range and positions in an explicit vector
must be unique; claim-reference multiplicity caused by distinct operand
positions is retained. `AllReductionInputs` must be nonempty. A path site,
missing input, reordered child subject, different consumer claim, or different
artifact identifier refuses.

`ConsumedClaimVector` binds one judgment whose subject is the exact
`ConsumedClaimVector` selected from the sealed artifact. The selected claim set
and order must match exactly. Individual judgments about the vector's members
do not establish a joint judgment about that vector: an explicit future
aggregation rule would be required.

The per-port resource substitution is total and type preserving. Before a
parent rule reads a premise, the kernel constructs one specialized view:

```text
specialize(premise_judgment, resolved_resource_substitution)
```

Specialization substitutes every premise resource occurrence in the result
quantities, primitive-game resource substitutions, hypothesis arguments, and
any typed external-subject arguments. Its free resource declarations are
exactly the conclusion resources used by the substituted expressions;
coordinate and round structure and the closed primitive-game instance
arguments are preserved. All premise projections and all inherited hypotheses
are read from this same specialized view; no unspecialized premise variable
may escape into the conclusion. The admitted bodies use an empty map when the
premise has no resources, identity on `t` for SR-to-FS, and exact declared maps
for computational games. An absent, extra, cyclic, or ill-typed substitution
refuses.

Bindings use one closed artifact-projection algebra:

```text
ArtifactProjection :=
    ConclusionReductionContract
  | ContractRoundAdjacency
  | ReductionInputCount
  | ReductionParameter(exact_key, expected_type)
  | PathBindingField(exact_key, expected_type)
  | ContractRoundFamilyField {
      selector: AllContractRounds | RoundKind(exact_kind)
                | RoundPosition(nonnegative_integer),
      field: admitted_round_field,
      aggregate: UniqueEqual | Count
    }
```

`UniqueEqual` requires every selected round to yield the same typed value;
`Count` yields the exact selected cardinality. Empty selection refuses except
where a projection schema explicitly admits zero count. The reduction
constructors are reduction-site-relative and kernel evaluated over the sealed
artifact. `PathBindingField` is path-site-relative and selects an admitted
typed construction field from the authenticated path occurrence. In
particular, codec-bias values are derived by the kernel from the sealed
challenge, sponge, and codec facts rather than accepted as opaque booleans or
precomputed assertions. `ContractRoundAdjacency` yields the exact
round-adjacency fact authenticated by the reduction occurrence and its pinned
contract. A reduction projection at a path site, a path projection at a
reduction site, an unknown field, or a type mismatch refuses.

`ReductionInputCount` is the exact cardinality of the authenticated reduction
input vector at the occurrence. It is not a count supplied by a transform
provider or inferred from a premise judgment. The KZG preservation bindings
use it for the theorem parameter `s`.

For every consumed input, the sealed reduction view also carries its exact
descriptor-anchor map and, separately, the canonical event position of each
anchor that is tied to a transcript event by `pir.material_bind`. Both vectors
follow the authenticated reduction-input order. They are theorem-independent
protocol facts: projection copies them into `ReductionContractValue`, while
the selected theorem binding determines which named decider may read them.

The v0 KZG deciders are total and fail closed:

- `SamePoint(contract)` requires at least two inputs, an exact anchor-map entry
  for every input, and a nonempty `point` anchor in each map; it returns true
  only when all those anchor values are equal.
- `BatchAfterMaterial(contract)` requires at least two inputs, the one
  authenticated batch round, and nonempty `commitment`, `point`, and `value`
  anchors with material-event positions for every input; every such position
  must be strictly before that round's challenge-event position.

Missing anchors, missing material bindings, unequal points, an unsupported
round shape, or a material event at or after the challenge returns false.

The value-source grammar is:

```text
BindingValue :=
    Literal(typed_value)
  | SealedArtifactProjection(ArtifactProjection)
  | ConclusionSubject
  | ApplicationPathTransition
  | ConclusionResource(resource_name)
  | ResolvedParameter(parameter_name)
```

`ConclusionSubject` reads only the value already constructed by `subjectOf`;
it cannot replace it. `ApplicationPathTransition` is resolved by `APPLY` only
at a `PathOccurrence`: the binding selected by `Apply` is the sole transition
authority, must carry a `PathTransition` anchor, and produces that exact
anchored transition. It is not a sealed-artifact projection and is invalid at a
reduction occurrence. There is no dictionary path or callback.

Primitive-game instance arguments and exact-external-subject arguments are
direct `BindingValue`s. v0 has no rule-level metavariable declarations,
pattern terms, or unification state. The admitted equality shape is
deliberately narrower than general value equality:

```text
ExactParameterPin := Pin(
  declared_parameter_name,
  expected: Literal(typed_value))
```

`RULE_WF` requires the pin to name one declared parameter exactly once, and
requires the expected value to be a literal of that parameter's exact sort.
`APPLY` compares the already-resolved parameter to that literal. A binding may
use this form to pin an algebra carrier, reuse direct `ResolvedParameter`
values across primitive-game and hypothesis bindings, and carry resource flow
through typed quantity names and substitutions.

```text
RuleBinding {
  binding_ref,
  rule_ref,
  subject_schema,
  protocol_anchor:
      ReductionContract(exact_ref)
    | PathTransition(exact_ref),
  premise_relations: map<premise_port, SubjectRelation>,
  parameter_bindings: map<parameter, BindingValue>,
  fact_bindings: map<fact_port, BindingValue>,
  condition_argument_bindings:
    map<condition_slot, ordered [BindingValue]>,
  hypothesis_argument_bindings:
    map<hypothesis_slot, ordered [BindingValue]>
}
```

Every direct artifact application has one binding and one site. A reusable
rule can have many bindings. A premise provider with no honest artifact anchor
has no direct binding and can only describe an assumed exact external subject.
`subject_schema` is a predicate over `subjectOf(sealed, site)`, not a subject
factory. At a reduction occurrence the binding's exact
`ReductionContract` anchor must equal the occurrence's authenticated contract.
The sealed soundness view contains theorem-independent structural facts; a
theorem is never an artifact fact: the artifact carries no citation at
all. This permits several rules to be valid alternatives over the same
exact structural transformation while the explicit immutable context,
binding, and derivation plan select exactly one semantics. At a path
occurrence the explicit selected context, binding, plan, and typed premise
authorize the application, and nothing in the artifact names a theorem.

A declaration's revision is its own content digest: the canonical document of
the declaration under a domain-separating tag, with the declaration's own
revision excluded from the preimage. A binding's preimage keeps its
`rule_ref` whole, revision included, because naming an exact rule revision is
what a binding is for. Only the fields a variant's semantics reads enter the
preimage; well-formedness already forces every inactive field to its default,
so two declarations that evaluate identically have the same digest.

The two argument-binding maps must cover their rule templates exactly.
Bindings cannot add a slot, omit one, reorder arguments, replace a predicate,
or replace a proposition schema. Missing artifact facts cannot be converted
to a successful machine condition. If the cited theorem is legitimately
conditional on a fact that the sealed view does not authenticate—such as an
SRS identity or degree limit—the rule must declare that exact typed proposition
as an external hypothesis and retain it in the conclusion.

Artifact-fact ports have constructor-level provenance. A
`ReductionContract` fact is bound only by
`SealedArtifactProjection(ConclusionReductionContract)`, a `RoundAdjacency`
fact only by `SealedArtifactProjection(ContractRoundAdjacency)`, and a
`PathTransition` fact only by `ApplicationPathTransition`. A literal,
conclusion resource, or resolved parameter can never occupy one of these
ports merely because it has the same runtime sort.

### 5.3 External judgments

```text
ExternalJudgmentAssumption {
  asserted_judgment: closed SecurityJudgment
}
```

The consuming port and binding own the expected index, result, resources, and
subject relation. The kernel validates the supplied closed judgment against
them and canonically constructs:

```text
AssumedJudgmentHolds(canonical(asserted_judgment))
```

Here `canonical(asserted_judgment)` encodes the caller's original closed
judgment, including its original proposition hypotheses. An external input
that already contains any `AssumedJudgmentHolds` marker refuses; only `DERIVE`
constructs that marker. The evaluated `Assumed` conclusion is:

```text
asserted_judgment with hypotheses =
  asserted_judgment.hypotheses
  union {AssumedJudgmentHolds(canonical(asserted_judgment))}
```

The generated marker is one level deep and its asserted judgment is
marker-free. Resource specialization commutes with this constructor:

```text
specialize(
  AssumedJudgmentHolds(canonical(J)),
  sigma)
= AssumedJudgmentHolds(canonical(specialize(J, sigma)))
```

The right-hand `specialize` acts on the original marker-free `J`, before the
synthesized proposition is added, so the definition is not recursive and
introduces no independent nested binder. A nested marker refuses rather than
guessing binder identity. Every dependent conclusion retains the specialized
proposition and the asserted judgment's specialized original proposition
hypotheses. The caller cannot provide a pre-existing or mismatching assertion.
In an `Assumed` node the judgment fields are asserted, not recomputed; in every
`Applied` node the kernel derives them by the rules in §3. A provider
reference, citation, SRS reference, or status label cannot manufacture this
input.

An asserted judgment is closed-well-formed only if its subject and index are
admitted, coordinate labels or round indices are unique, arities and challenge
spaces have the required domains, its result matches its index, every bound
and hypothesis is closed, its resources are declared exactly once, every game
instance resolves in the context, and `regime(result)` is defined. Any failure
refuses the assumption.

An independently requested scheme/SRS-level KZG computational-special-soundness
judgment is represented as an exact external judgment. A KZG batching
preservation rule whose source-PIoP premise is one joint special-soundness
judgment over an exact `ConsumedClaimVector` does not derive that premise merely
because the vector is exposed in the sealed artifact. Without an admitted
aggregation rule, the premise must enter as an exact external judgment; partial
synthetic bindings from individual source claims refuse.

### 5.4 Catalog and context

```text
SoundnessCatalog {
  schema_context: {
    security_index_schemas,
    subject_schemas,
    primitive_game_definitions,
    proposition_schemas,
    machine_deciders
  },
  rules: exact-id map<SoundnessRule>,
  bindings: exact-id map<RuleBinding>
}

freezeSoundnessCatalog(owned schemas, owned rules, owned bindings)
  = immutable SoundnessCatalog | refuse
```

Freezing is the only native construction boundary. It requires every map key
to equal its declaration's exact reference id, every rule to pass `RULE_WF`,
every binding to name an exact rule revision in the same snapshot, and every
binding to pass binding well-formedness. Duplicate or structurally impossible
schema entries and unresolved exact references refuse. The resulting catalog
is registry-independent and immutable.

A signature is frozen from owned declarations. Every loader and programmatic
construction path must pass the same declaration types through
`freezeSoundnessCatalog` and therefore share the same catalog well-formedness
boundary.

```text
Signature {
  catalog: immutable SoundnessCatalog,
  annotations: exact-id map<DeclarationAnnotation>
}
```

The separation is structural rather than conventional. The kernel judgments
receive a `SoundnessCatalog` and never a `Signature`, so an annotation cannot
reach `RULE_WF`, `APPLY`, or `DERIVE`, and no declaration digest can pick one
up. An editorial change therefore cannot re-mint a rule, and the presence of a
citation cannot discharge a premise.

An annotation carries the declaration's statement in the author's words, the
loss as an author would write it, the reason for a non-admitted status,
citations, source anchors, and formalization receipts — or, where no
counterpart statement exists to receipt, a surveyed absence naming the
repository and revision that were read, what was looked for, and where the
demand is recorded. A receipt names a
repository, a revision, a declaration, what that mechanized statement actually
covers, and which axioms its reviewed dependency closure admits; an empty
axiom field means none are admitted, so a receipt cannot overstate what it
carries. Signature freezing checks receipt shape and internal consistency; the
kernel does not validate the external theorem, its correspondence to the rule,
or its applicability to an artifact.

Freezing a signature requires every rule to carry an annotation naming at
least one source anchor, requires a rule whose status is not `admitted` to
state why, and requires every rule to record either a formalization receipt
or a surveyed absence — the catalog stays total, so a new rule cannot be
silent about what the mechanization holds for it. A rule whose statement cannot be located is one nobody can check,
and the requirement is what keeps a citation from being dropped when a
declaration is rewritten. Every annotation key must name something the
signature declares, so a renamed declaration cannot leave its record orphaned.
Bindings need no annotation: a binding connects a rule to protocol structure
and cites no source of its own.

```text
SoundnessContext {
  owned_catalog: immutable SoundnessCatalog,
  selected_binding_refs,
  resolved_parameters
}
```

The caller selects a context explicitly. The context owns an immutable
snapshot of the native catalog, including its closed schema tables, rather
than retaining caller-owned rule or binding values.
Selected binding refs must resolve exactly in that snapshot. A selected binding
is the sole executable authority and derives rule availability through its
exact `rule_ref`; a catalog rule with no selected binding remains a declaration
and is not executable. The context exposes only const lookup; it is not allowed
to alter rule bodies, choose a path, discharge hypotheses, or change
arithmetic. Runtime policy may construct a context, but policy is outside
`RULE_WF`, `APPLY`, and `DERIVE`.

The artifact-projection vocabulary is a finite kernel-owned set of projection
constructors, input artifact shapes, and output types; it is not
caller-extensible context data. Evaluation reads only the sealed artifact and
the closed per-round binders in §5.1, so the context cannot supply an arbitrary
fact resolver. `resolved_parameters` is an exact typed map for explicitly
external values used by `ResolvedParameter`. Such a value is never described
as an artifact fact. If theorem applicability depends on its correspondence to
the artifact, that correspondence remains an instantiated external hypothesis
unless a named machine decider can establish it.

## 6. Explicit derivations

There is one evaluated tree rather than separate application, trace, and
certificate authorities:

```text
DerivationPlan :=
    Assume(ExternalJudgmentAssumption)
  | Apply {
      site,
      binding_ref,
      premises: map<premise_port, DerivationPlan>
    }
```

```text
EvaluatedDerivation :=
    Assumed {
      input,
      conclusion
    }
  | Applied {
      site,
      binding_ref,
      premises: map<premise_port, EvaluatedDerivation>,
      conclusion
    }
```

```text
DerivationTarget {
  exact_subject,
  exact_security_index,
  exact_resource_variable_declarations
}

DerivationResult {
  artifact_id,
  target,
  root: EvaluatedDerivation
}
```

The declarative object is a tree. An implementation may memoize an equal
subtree as a DAG, but every incoming premise occurrence remains semantic.
Caching cannot erase multiplicity, resource substitution, hypotheses, or
loss.

The plan is explicit. A protocol target's root must be `Apply`; `Assume` is
legal only as the child of a declared premise port, where its asserted subject
must satisfy that port's exact `SubjectRelation`. Thus a caller cannot turn a
root target into a successful derivation merely by asserting it.
`DERIVE` performs no theorem search, implicit provider resolution,
cheapest-path selection, or fallback. Callers that enumerate plans do so
outside the judgment and submit the selected plan.

## 7. Normative judgments

### 7.1 `RULE_WF`

```text
RULE_WF(context, rule) = accept | refuse
```

Acceptance requires:

- every parameter, resource, premise, fact, game, proposition, and decider
  reference is declared and typed;
- the rule body is one admitted closed variant;
- all template references are in scope;
- quantity domains are explicit and all result positions have the required
  signs and sorts;
- premise and conclusion indices satisfy the exact body-signature table in
  §5.1, including track, variant, and duplex-model preservation;
- the RBR-to-SR premise declares `RequiresEmptyGameSupport` and
  `RequiresNoBoundResourceSupport`, and every result constraint is one
  admitted structural predicate;
- every premise projection is legal for its notion-indexed result;
- the conclusion index and result schema agree;
- each fixed body equation uses premise bounds only at its named positions:
  round scaling at the selected round, RBR-to-SR through the premise's round
  maximum, and
  SR-to-FS through the fixed premise addend; preservation has only its
  information-theoretic extraction premise and a complete cited conclusion
  failure expression;
- regime is not authored anywhere, and inherited hypotheses are not
  authored by the body;
- the bound constructors are structurally monotone;
- the v0 evaluator can normalize every reachable body expression to the
  admitted exact normal form; an unsupported form is a `RULE_WF` refusal; and
- no opaque payload, arithmetic, decider, condition, or evaluator escape is
  present.

`RULE_WF` proves syntax and typing only. It is deliberately not named
`RULE_OK`: it does not prove theorem truth, source faithfulness, binding
faithfulness, assumptions, or runtime permission.

### 7.2 `APPLY`

`APPLY` and `DERIVE` are representation-neutral trusted-input interpreters.
Their `SealedSoundnessView` argument must already have been reconstructed and
authenticated by the caller's exact representation authority; neither
operation authenticates bytes, MLIR, or a seal by itself. The PIR adapter
accepts an opaque `AdmittedPirArtifact` capability and produces an owned
`SealedSoundnessView`; it has no raw sealed-IR entry. The compiler establishes
the same precondition through its exact `ArtifactSemantics` authority before
invoking `DERIVE`.

```text
APPLY(context, sealed_artifact, site, binding, typed_premises)
  = EvaluatedDerivation::Applied | refuse
```

Acceptance requires:

1. the artifact is sealed, the site resolves exactly, and
   `subjectOf(sealed_artifact, site)` constructs the unique conclusion
   subject;
2. the binding is selected, names an exact well-formed catalog rule, and its
   protocol anchor matches the site; its subject schema accepts the constructed
   subject, and at a `PathOccurrence` the selected binding itself is the sole
   path-transition authority;
3. the binding's premise relations follow the claim graph at the occurrence
   (claim coverage): at a `ReductionOccurrence`, every consumed claim that
   some transformer of the artifact produced is selected by a `ConsumedClaim`
   or `ConsumedClaimVector` premise relation, and every selected input
   position names a consumed claim; the judgment is vacuous at a
   `PathOccurrence`, and a refusal names the uncovered claims in canonical
   claim-index order;
4. every premise port has exactly one child with the required subject
   relation, index, result schema, resource schema, and ordering;
5. `SameSubject` premises match the conclusion subject exactly;
6. `ConsumedClaim` and `ConsumedClaimVector` subjects equal the claims selected
   from the sealed artifact, including multiplicity and order;
7. every assumed premise matches its port and subject relation and gains the
   canonical `AssumedJudgmentHolds` hypothesis;
8. every premise is specialized through its port's total resource
   substitution, and all binding values, exact parameter pins, parameters,
   facts, primitive-game instance arguments, and primitive-game resource
   substitutions resolve against those specialized views exactly with their
   declared types;
9. every declared premise-result constraint holds on the specialized closed
   premise result;
10. every named machine decider exists and returns true on its resolved typed
    arguments;
11. quantity evaluation is total, exact, and within its required domains;
12. the closed rule body constructs the result required by the conclusion
    index, with no unresolved template leaf;
13. the kernel derives the regime from the closed result's primitive
    game support; and
14. the kernel computes the conclusion hypotheses by union over specialized
    premise hypotheses, local hypotheses, and canonical assumption
    propositions.

Claim coverage is containment, not equality, and the producer map behind it —
each claim's producing transformer position and output index, or nothing for
an artifact source — is a fold over the sealed view, never a stored field.
The one-sided form is deliberate: a premise relation may select an artifact
source claim, because a premise about a source is the artifact's own
hypothesis rather than another transformer's conclusion. Two limits are
stated rather than implied. Coverage is local to the occurrence — an author
who instantiates every consumed claim as a source makes every entry
application clean, so the honesty of a derivation lives at the request's
target subject, not here. And coverage reads the binding's premise relations,
not the plan: whether a covering premise is discharged by `Apply` or retained
by `Assume` is the `AssumedJudgmentHolds` half of the ledger. A rule with no
premise ports selects nothing, so an entry body at an occurrence whose
consumed claims are produced refuses — a derivation pricing one reduction of
a chain while concluding about the chain's claim is no longer authorable.

A missing decider refuses. It never degrades into a successful “unresolved
condition.” A condition without a v0 decider is represented as an external
hypothesis only when the rule itself declares that proposition schema.

### 7.3 `DERIVE`

```text
DERIVE(context, sealed_artifact, target, plan)
  = DerivationResult | refuse
```

`DERIVE` recursively checks:

- every `Assume` input is marker-free, closed, well formed, and matches its
  consuming premise port and subject relation;
- the root is `Apply`;
- every `Apply` node satisfies `APPLY`;
- child subjects match `SameSubject`, `ConsumedClaim`,
  `ConsumedClaimVector`, or `ExactExternalSubject` exactly;
- the tree is finite and acyclic as supplied;
- repeated premise edges are retained;
- the root subject and index equal the target;
- the root resource-variable declarations equal the target declarations; and
- all returned values are owned by the result rather than borrowed from a
  temporary registry or artifact.

Several valid plans may derive the same target. That fact creates no
artifact-global result and no implicit choice.

## 8. What the kernel establishes

If `DERIVE` accepts, the result is the exact interpretation of the encoded
rule bodies, bindings, artifact facts, external inputs, and plan under this
specification.

The corresponding cryptographic conclusion additionally depends on:

- the truth and faithful encoding of every used rule;
- the faithfulness of every binding to the sealed protocol occurrence;
- the truth of the returned qualitative hypotheses;
- the admitted definitions of the security notions and primitive games; and
- the intended correspondence between the sealed protocol model and the
  concrete protocol being analyzed.

This is an evaluator-correctness contract, not a claim that zkc has proved the
underlying theorems or the whole protocol. Primitive advantages remain
symbolic unless a separate, explicit game bound is supplied by a future
semantic rule.

### 8.1 The derivation is independently re-checkable

A derivation's witness is a proof object, not a log. A party holding
only the signature, the sealed artifact, and the witness re-checks the
judgment by re-running the rule bodies the witness names against the
facts it records — without re-running the producer, and without
trusting it. The producer's search is unconstrained; what is checked is
its output.

This is the property the rest of this section's contract rests on, and
it is what a `DERIVE` implementation exists to make true: a small
checker of a caller-supplied plan, never a prover. Everything the
kernel refuses to do — theorem search, provider resolution,
cheapest-path selection, fallback — it refuses in order to keep the
checking side small enough to be re-implemented by someone who trusts
none of it.

### 8.2 The bound order is sound on every valuation

`ClosedBound` is a ground rational plus non-negative-coefficient terms
over resource variables and primitive-game advantages. Its order
compares coefficientwise, an absent term reading as zero.

That order is sound: if every coefficient of the candidate is at most
the corresponding coefficient of the ceiling, then for every valuation
of the resource variables and every value of the advantages, the
candidate's value is at most the ceiling's — because non-negative
coefficients make each term monotone in its own coefficient, and a sum
of such terms is monotone in all of them.

It is deliberately incomplete. Two bounds that are equal under every
valuation but spelled differently — a resource substitution written
two ways, a term that a change of variable would align — compare as
incomparable, and dispatch refuses. Refusal is the admitted direction:
an order that answered by approximating would price a protocol under a
bound nobody stated.

### 8.3 The projection algebra is adequate

`ArtifactProjection` is the finite, kernel-owned signature through
which a rule reads a sealed artifact, closed to caller extension. Its
adequacy is the statement that it is the *whole* channel: two sealed
artifacts agreeing on every admitted projection admit exactly the same
derivable judgments.

Adequacy is what makes the projection set a specification rather than a
convenience. It fails the moment a rule reads an artifact through any
other route, which is why the signature is closed — and because the
set is finite, the statement is checkable by exhausting it rather than
argued.

## 9. Core conformance

A conforming implementation:

- owns every returned `DerivationResult`; it retains no borrowed registry,
  artifact, MLIR, callback, or policy object;
- implements every tagged sum and arithmetic operator as a closed,
  fail-unknown switch;
- evaluates theorem applications only through `APPLY` and rooted plans only
  through `DERIVE`;
- keeps repeated premise edges, complete resource substitutions, primitive
  advantages, and inherited hypotheses intact; and
- refuses wrong sites, subjects, exact rule or binding revisions, protocol
  anchors, premise relations, result schemas, resource domains, conditions,
  arithmetic domains, and unsupported normal forms.

Consumers may discover targets or construct plans, but they use this same
evaluator and cannot introduce another pricing semantics. Protocol-specific
inventories, walkthroughs, and implementation sequencing are non-normative and
do not belong in this calculus.

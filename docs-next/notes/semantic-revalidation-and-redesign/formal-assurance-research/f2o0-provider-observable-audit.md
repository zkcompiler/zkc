# F2-O0 Provider-Observable Audit

> **Kind:** Temporary bounded provider-side audit of the admitted source
> **State:** `CannotAnswer/F2O0-C-MISSING-OPERATIONAL-OBSERVABLE` for the
> F1-R1B Fresh Schnorr slice; four operational observables and five property
> premises have no source coordinate in the six normalized owner views
> **Authority:** None. The experiment edits no target semantics, profile
> identity, evaluator, Analysis judgment, or roadmap priority, and the
> generated Lean file carries no authority.
> **Executable evidence:**
> [`evaluation/formal-provider-observables-f2o0`](../../../../evaluation/formal-provider-observables-f2o0/README.md)

## 1. Question and answer

The program reassessment found that every executable package since F1-R1C0
had made the source side of the bridge exact while nothing had tried to build
a provider term from an admitted zkc subject. This package asks the smallest
provider-side question: taking the exact admitted finite Schnorr Core and
Fresh Protocol only through their six normalized owner views, does every
construct of a VCVio-shaped interaction have a source coordinate, or exactly
which observables are missing?

The answer is the second. An untrusted generator emits one `ProbComp`
interaction with one step per Core occurrence, and an independent checker
confirms that its 37-construct ledger is total over the schedule, injective
over the 329 active view leaves, consistent with the Lean text, and free of
invented observables. Twenty-eight constructs claim distinct coordinates. Nine
do not, and the interaction is parametric in exactly those nine:

- four operational observables: the Check's denotation, the terminal guard's
  denotation, the Fresh challenge's sampling law, and the map from the Core's
  verdict and run-outcome partition into the provider's Boolean and failure
  layer; and
- five property premises: the relation predicate, the witness type, the
  Prover's private state type, and the honest commit and respond algorithms.

The generated file elaborates under the pinned VCVio revision with an empty
axiom closure. That is an environment fact only; it makes no correspondence,
applicability, or property claim.

## 2. Method

The method mirrors F1-R1C0 on the other side of the bridge: stop at the first
absent premise, name it exactly, do not invent it.

**Subject and universe.** The generator obtains the admitted Core and Fresh
Protocol handles and the six view values through the F0-V2B1 reference path.
The checker obtains the same facts through the F0-V2B1 clean-room path and
treats them as its owner-side oracle. Both paths reproduce B1's frozen 329-leaf
manifests; the two packages otherwise share no code.

**Determination, not mention.** A construct is sourced only when one view leaf
determines it under a rendering rule declared in the ledger; further leaves the
generator read are listed as consulted and are not claimed. A construct whose
content no leaf determines is emitted as a Lean parameter and recorded as a
typed gap with its class, the exact reason, what needs it, the leaves that
merely name it, and where the fact actually lives. The checker enforces the
distinction structurally: a denotation, distribution, relation, honest
strategy, private type, or outcome map may never claim a leaf, and a sourced
construct may claim only a leaf whose boundary can determine its kind.

**One declared premise.** Reading any leaf presupposes the decoders of the
body compilers named in the B1 schema source and the K1 datum codec. These are
Foundation and PIR laws, not view leaves. The ledger records the premise once
rather than turning every ordinal reference into a gap. Under it the value
types decode to root natural and Boolean types, rendered as `Fin 3` and `Bool`.

**Checks.** The checker's rules and codes are listed in the package README.
Fourteen mutations each yield their named failure; the reassessment's four
required mutations are among them. The elaboration receipt records toolchain,
revision, exit status, wall time, and the `#print axioms` closure of both
emitted declarations, and `run.py --check` binds it to the committed generated
file by digest without needing the checkout.

## 3. Results

| Construct family | Sourced | Gap | Source table |
|---|---:|---:|---|
| subject identities | 2 | 0 | EffectView and ExecutionView identity leaves |
| value carriers | 2 | 0 | EffectView value-producer types |
| Prover guaranteed reads | 7 | 0 | StrategyDecisionView read map |
| Prover decision points | 2 | 0 | StrategyDecisionView decision table |
| strategy parameter and public input | 2 | 0 | StrategyDecisionView law leaf; EffectView value ref |
| terminal verdicts | 2 | 0 | EffectView terminal table |
| challenge interpretation | 1 | 0 | ExecutionView `challenge_interpretation = Fresh` |
| occurrence steps | 6 | 0 | EffectView occurrence schedule |
| challenge law, Check and guard denotations | 0 | 3 | none |
| provider type parameters | 4 | 2 | PublicBindingView class, message types, challenge type |
| provider relation and honest fields | 0 | 3 | none |
| provider verify (outcome map) | 0 | 1 | none |
| **total** | **28** | **9** | 28 distinct leaves of 329 |

The 45 frozen findings contain 17 affirmative structural results, 14 refused
mutations, nine `CannotAnswer` gaps, four `CannotAnswer` non-claims, and the
aggregate.

## 4. Exact findings

### 4.1 Operational observables with no source coordinate

| Gap | What the views carry | What is missing and where it lives |
|---|---|---|
| Check denotation | algorithm identity `zkcidv0:foundation.portable-algorithm:86a47a88…`, evaluation-contract identity, four ordered input references, Boolean output type | the function `Z3 → Z3 → Z3 → Z3 → Bool`; it lives in the 179,147-octet K1 portable-algorithm preimage (`finite_schnorr_algorithm` in the F1-R1B owner model), evaluated under Foundation Sections 5.1, 5.2, and 7.2 |
| Terminal guard denotation | one opaque `guard-body-v0` leaf that decodes to the Boolean-identity algorithm `aa07d7da…`, its contract, and the input `OccurrenceOutput(3, 0)` | the guard's function and any statement that its truth equals the required Check's truth; the preimage lives in `boolean_identity_algorithm`; the link is the B5A gap that B5B1's Check-use predicate would close and B1's views do not carry |
| Fresh sampling law | `challenge_interpretation = Fresh`, value type `Z3`, and nominal references to `pir.challenge-domain` #0 and `pir.public-coin-law` #0 of module `de7f837d…` | the distribution; the referenced bodies are the nominal symbols `finite-additive-z3` and `fresh-uniform-z3`, whose formation proves no distribution (`interactive-core.md` Section 2); Section 5.2 makes distribution truth an Analysis/evidence obligation and Section 12.1 says source identity proves no distribution; the provider's `PerfectlyComplete` fixes `$ᵗ Chal`, the uniform draw |
| Outcome-partition map | verdict cases `Accept` and `Reject` at the terminal rows and `interpretation_failure_schema = None` | a map from `Accept | Reject | Abort` and the run-outcome lanes `CompletedRun`, `InterpretationFailed`, `StrategyStopped`, and the qualified noncompletion partition (`interactive-core.md` Sections 6.4, 12.3, 12.4; Foundation Section 8) into `ChallengeVerifyProtocol.verify : Bool` and the `OptionT` failure layer; the generator renders `Accept` as `true` and `Reject` as `false` and has no image for the rest |

### 4.2 Property premises with no source coordinate

| Gap | Where it lives |
|---|---|
| relation predicate `rel : Stmt → Wit → Bool` | `docs-next/relations/relation-model.md` Sections 3 and 7.2; no relation is bound to this subject's Statement binding, and its ClaimReductionView is empty |
| witness type | the same Relations pages; the Core has no Verifier-private input, no Claim, and no binding |
| Prover private state type | `interactive-core.md` Section 9.2 (the ProverView has no private state field) and 12.3; `interfaces-and-plans.md` (Plan-owned strategy state) |
| honest commit and respond | Sections 9.2 and 12.3; strategies are execution inputs, not Core observables; the provider's `Schnorr.sigma` bundles them |

### 4.3 Candidate gaps that are not gaps

The reassessment predicted "message value types as Lean types" as a likely
missing observable. Under the codec premise it is not: every value type used by
the interaction has a leaf coordinate, and the Lean carrier follows from the
decoded root domain and schema bound by a declared rendering rule. Likewise
the Prover interface (decision points, guaranteed reads, legal move types), the
Fresh interpretation, and four of the six `ChallengeVerifyProtocol` type
parameters are sourced.

## 5. Design consequences

1. **The formal source closure is larger than the six views.** Two of the
   four operational gaps are portable-algorithm denotations. The views carry
   algorithm identities; the D1 cold path already authenticates the exact-used
   algorithm preimages before projecting. The formal-source package must
   therefore include the K1 algorithm closure, and a provider interpretation
   needs a K1-term-to-provider denotation with its own checked
   correspondence. F0-V2C should decide whether the views gain an exact
   algorithm read or the package carries the preimages alongside the views.
2. **The public-coin law needs an owner-side body or an Analysis binding.**
   Every `pir.public-coin-law` and `pir.challenge-domain` declaration in the
   slice is nominal, while the provider's completeness statement hardcodes a
   uniform draw. Either the declaration kind acquires a denotational body, as
   `pir.oracle-domain-law` already has, or the Analysis family that owns
   distribution truth binds the nominal coordinate to a distribution. Until
   one owner does, the sampling law is a Q5 premise supplied from outside the
   subject, not a Q1 observable.
3. **The outcome-partition map has no owner.** The provider's `verify : Bool`
   has no image for `Abort` or for any noncompletion lane. An operational trace
   relation that includes every failure branch, as the F2-O entry contract
   requires, needs either an `OptionT`-layered interaction or an explicit
   statement that noncompletion is outside the relation. This scopes D2: if the
   provider relation is to include the outcome lanes, D2 should define the run
   record in provider-facing form with those lanes, once.
4. **The Terminal gap resurfaces on the provider side.** The interaction had
   to carry the guard as a separate parameter because no view says guard truth
   equals Check truth. The B5B1 selection would make the provider's `verify`
   derivable from the Check alone. This strengthens the case for the reopening
   record the reassessment asked for.
5. **Reversal condition.** The A/S/C selection assumed that a theorem-relevant
   observation can always be selected through an owner view. For the
   view-only reading of the source package that condition is false at this
   resolution for four observables. It remains defensible if the package is
   defined as the views plus the authenticated Foundation closure plus one
   Analysis-owned law binding. That is a choice for F0, not something this
   package decides.
6. **Three owners meet in one provider structure.** `ChallengeVerifyProtocol`
   bundles what zkc separates: PIR supplies the statement, commitment,
   challenge, and response types and the schedule; Relations would supply the
   relation and witness; a Plan would supply the honest strategy and its
   state. The F2-P applicability judgment therefore binds objects from three
   owners, and the entry contract should name them.

## 6. Non-claims

The 45-finding aggregate is finite executable evidence about one ledger over
one admitted subject. It establishes no Q2 provider correspondence, theorem
applicability, protocol or cryptographic property, security result, or target
change. The generated Lean file is untrusted output; its elaboration under the
pinned toolchain is an environment fact and its empty axiom closure says
nothing about meaning. A sourced construct is a coordinate claim under a
declared rendering rule. The checker checks the ledger and the Lean text's
structure, not the semantics of the Lean term. The codec premise is assumed,
not established. Schnorr cannot exercise the shared-challenge discriminator.

## 7. Next gate

F0-V2C should take the four operational gaps as inputs to what it publishes,
alongside the reopening record for the Terminal contract and the lattice
reconciliation table. F2-O1 should repeat this audit on a subject that carries
the shared-challenge discriminator, with the D1 integrated baseline as the
candidate subject, before any Q2 correspondence attempt. D2 should be scoped
by consequence 3 rather than by the census's schema-only reading alone.

# Complete-Argument Architecture Selection

> **Kind:** Temporary cross-case design decision
> **State:** Selected after source reconstruction and adversarial comparison
> **Authority:** None. The durable pages named in Section 8 own accepted
> target semantics.

## 1. Decision

A complete cryptographic argument is not one additional semantic root. It is
a coordinated use of independently identified subjects whose substitution
laws differ:

```text
                         verifier meaning
                               |
                               v
Relation meaning ---> InteractiveCore ---> terminal verdict
       |                    |
       |                    +-- challenge interpretation
       |                    +-- exact verifier profiles
       |                    +-- claims and reductions
       |
       +-- Plan witness correspondence
       +-- setup/relation premises

ProtocolInterface/OIR projects the public proof package.
ProverPlan supplies one honest construction strategy.
Analysis states what acceptance establishes and under which assumptions.
```

The selected architecture has these laws:

1. one exact verifier execution has one flat finite `InteractiveCore`;
2. source-level subarguments are claims, reductions, owner-local declarations,
   and checked authoring elaborations, not runtime child Cores by default;
3. a proof package is an Interface/OIR projection of typed Core publications,
   not a second semantic description of the protocol;
4. verifier-visible parameters are Core `PublicParameter` bindings;
5. public material consumed only by honest proof construction does not enter a
   deliberately minimal verifier Core merely by being public; the existing
   common-parameter and setup-specialized Plan routes remain valid, while a
   reusable typed Plan parameter is deferred to the next Plan co-design;
6. setup honesty and relation/key correspondence are Analysis/Evidence
   premises unless a later consumer requires a separately checked portable
   setup construction;
7. a verifier-side commitment-opening profile is used only for its exact
   claim/evidence shape; and
8. asymptotic or all-size claims use Analysis family subjects with pointwise
   correspondence to finite Core members.

## 2. Why a universal argument root fails

The candidate root would need to contain, or point authoritatively to, all of:

- relation and witness meaning;
- verifier schedule and terminal behavior;
- proof-construction algorithms and private state;
- transcript interpretation;
- proof bytes and endpoint codecs;
- setup production and trust;
- commitment schemes and batching;
- security properties and theorem premises.

Those fields do not share a substitution law. Replacing proof bytes may leave
the protocol unchanged. Replacing a Plan may leave the verifier and accepted
language unchanged. Replacing a transcript construction changes `ProtocolId`
but not `CoreId`. Replacing a relation changes what acceptance is intended to
mean without changing the verifier program. Replacing a theorem changes no
runtime behavior.

Hashing all of them into one root would therefore make semantically neutral
changes rotate unrelated identities and would make a single admission result
appear to establish facts owned by several different judgments. Storing only
references would add a registry-shaped coordinator with no independent law.

The four cases also disagree on basic shape:

| Pressure | PLONK | Groth16 | Bulletproofs | Logup* |
|---|---|---|---|---|
| verifier challenges | many | none | logarithmically many | source leaves interleaving partly open |
| proof construction | polynomial/PCS | QAP + proving CRS | vectors + IPA folds | pushforward + two branches |
| opening profile | exact KZG use | none | none in selected encoding | later exact PCS use |
| source substructure | interleaved arguments | one pairing equation | range-to-IPA reductions | parallel reductions sharing a point |
| external proof | fixed record | three group elements | round-dependent record | not fully specified |

The commonality is the owner graph, not a common proof payload.

## 3. Why one flat Core is selected

### 3.1 Preserved semantics

PLONK, Bulletproofs, and the lookup variants share challenges across logical
components and interleave publications before a single final verdict. A flat
Core preserves:

- one causal order;
- one transcript and scope hierarchy;
- exact challenge occurrences rather than equal sampled values;
- the Last-Challenge law;
- one claim-disposition graph; and
- one terminal authority.

Claims and reductions retain the source's logical boundaries. They do not
pretend to execute a theorem. Reusable authoring may elaborate a checked
template into the same flat Core, but the elaborator cannot become a runtime
transcript or verdict authority.

### 3.2 Rejected child-Core alternative

Splitting PLONK into arithmetic, permutation, lookup, and PCS child Cores would
need a new calculus for interleaving their messages, sharing challenges,
preventing duplicate absorption, constructing one quotient, sharing opening
proofs, and choosing one terminal. Splitting Bulletproofs would similarly
create a second transcript exactly where the source continues the first one.

Such a calculus would be larger than the source behavior it is meant to
represent. No reviewed case requires dynamic child execution. The existing
finite composition boundary remains closed.

### 3.3 Finite unrolling is not an asymptotic claim

An exact Bulletproofs instance fixes `N` and has `log2(N)` IPA rounds. An exact
GKR instance fixes its layers and Sumcheck rounds. Encoding those rounds in a
finite Core is faithful to execution but proves neither uniform construction,
polynomial time, logarithmic communication, nor security for all sizes.

Those statements require an Analysis family definition, size/security-
parameter schedules, uniform constructors, resource laws, and pointwise
correspondence from each family member to its exact admitted Core.

## 4. Public prover-parameter opportunity

### 4.1 Recovered design opportunity

PLONK and Groth16 both expose public material needed by an honest prover but
not by verifier semantics:

- the prover portion of a universal SRS;
- a circuit-specific proving key; and
- preprocessed polynomial or query material not read by the verifier.

Both source-level controls remain expressible:

- Groth16 can supply its formal public CRS to both prover and verifier as one
  Core `PublicParameter`; and
- a setup-specialized Plan can embed one fixed proving value as a recipe
  constant.

Original PLONK also binds its common preprocessed input into the source
transcript. The target must preserve that binding. The new lane is therefore
not required to make these papers representable.

The candidate targets the stricter ideal organization in which Core retains
only material that the verifier semantically reads and one Plan can be
instantiated over several setup outputs. If retained, it would avoid these
costs of the existing routes:

| Existing route | Failure |
|---|---|
| Core `PublicParameter` | Correct for common source setup, but overbinds a deliberately minimal verifier Core when it includes a prover-only projection |
| Core constant | Changes `CoreId` and verifier program identity for producer-only material |
| Plan `Advice` or `ConfidentialContext` | Misclassifies public setup as private |
| recipe `Constant(value)` | Correct for a setup-specialized Plan, but hard-codes one value into `ProverPlanId` and prevents setup-parametric reuse |
| ambient registry/file | Escapes typed identity, causality, and replay |

### 4.2 Minimal owner-local candidate

The candidate gives `ProverPlan` a sequence of typed
`PublicProverParameterDecl` values and a corresponding recipe operand. A
declaration commits to a local key and type, not to a runtime value or
supplier. The values are available to every Plan decision, remain outside
`ProverView`, and are not absorbed by a transcript unless the protocol
separately binds the same semantic value in Core.

This candidate does not make the Plan an endpoint or setup authority. It states
only that one Plan dataflow expects a typed public input. Runtime supply,
source provenance, correct preprocessing, and equality with any Core
parameter remain separate realization, Evidence, Relations, or Analysis
questions.

The name deliberately says `ProverParameter`, not generic “construction
material”: construction already names transcript and Oracle-commitment
subjects, while this role is specifically a public Plan input. The lane does
not subsume proof-carried duplex salt. That salt is generated
before Core execution and then consumed by one transcript construction. Its
existing construction-material satellite has a different lifecycle and
owner. Similar visibility alone is insufficient reason to merge them.

### 4.3 Why no setup-result root is added

A generic `SetupResult { proving_key, verification_key }` would imply that all
setups have one portable generation and verification law. The reviewed cases
do not support that:

- Groth16 circuit setup is randomized and may destroy its trapdoor;
- PLONK separates universal SRS material from circuit preprocessing;
- Bulletproofs may derive transparent generators under a profile;
- setup trust, updateability, and generator independence are different
  security premises.

For v0, the structural roles remain explicit: Relation owns circuit/QAP
meaning, Core consumes the verification material it actually reads, and Plan
consumes the public proving material it actually reads. A theorem or
completeness result names the exact setup-correspondence premise in Analysis.
Evidence may substantiate that premise. This is honest noncompletion, not a
claim that successful verification proves setup correspondence.

Reopen a checked setup-construction subject only when a concrete consumer
needs portable setup-result identity or a checkable setup relation that cannot
be expressed as an Analysis premise plus Evidence.

## 5. Zero-challenge protocol repair

Groth16 has no online public coin. Its semantic Core is:

```text
bind statement and verification key
publish one proof record (A,B,C)
evaluate one exact pairing-product predicate
Accept or Reject
```

This is a valid zero-challenge Core and has one canonical Fresh Protocol. The
`Fresh` tag is vacuous but supplies the existing closed interpretation form;
a new `Direct` tag would create a behaviorally duplicate Protocol identity.

The canonical-framed construction previously allowed an empty challenge-rule
sequence because it was total over an empty Core challenge set. Such a
resolver still initializes its state and absorbs headers, bindings, and prover
messages, so it is not operationally identical to Fresh: it adds provider,
resource, cost, and noncompletion surface. But it transforms no Challenge and
its state never resolves or influences one. That work is not a valid
`ChallengeInterpretation`. If an application needs a proof digest or audit
log, Interface, OIR, or Evidence must own it explicitly.

The repair is an exact-use law:

```text
AdmitTranscriptConstruction(T,C)
    requires C.challenges is nonempty
```

The duplex-sponge family already requires a positive number of message/
challenge rounds. Fresh remains valid for zero-challenge Cores. This removes
kind-inappropriate FS identity without changing any challenged protocol.

## 6. Proof packages and verifier profiles

### 6.1 Package ownership

A proof package is a typed projection of Core prover publications under one
`ProtocolInterface`, followed by concrete OIR codecs and layout. It may group
several semantic messages into one byte record, but it cannot rewrite their
causal order. Conversely, several physical fields may project one semantic
record value.

This law is decisive for PLONK and Bulletproofs: treating the final byte string
as one pre-challenge ProverMessage would erase every Fiat--Shamir dependency.
Groth16 genuinely has one semantic message because no challenge separates its
three proof elements.

### 6.2 Exact commitment boundary

The commitment-opening profile applies only when the verifier consumes:

```text
public verifier setup
ordered commitment/query/asserted-answer claims
public opening evidence
exact bounded verification algorithm
```

- PLONK uses one protocol-specific two-point KZG profile with both same-point
  claim aggregation and post-proof equation aggregation.
- Groth16's group elements and pairing equation are not openings.
- Bulletproofs' Pedersen/vector relations and IPA residual are not the selected
  claim/evidence shape.
- LogUp variants may attach exact PCS profiles after their reductions; the
  lookup construction itself is not a commitment scheme.

Mathematical use of the word “commitment” is therefore insufficient to attach
the shared profile.

## 7. Relation, setup, and property boundaries

Structural admission must not collapse the following propositions:

```text
RelationSatisfied(instance,witness)
ProtocolAccepted(invocation,proof)
PlanGenerated(proof)
VerificationKeyMatchesRelation(vk,definition,setup)
SecurityTheoremApplies(protocol,relation,setup,adversary,model)
ImplementationConforms(artifact,protocol)
```

Relations maps exact Statement, witness, Oracle, phase, claim, reduction, and
commitment coordinates. It may use a purpose-specific grounding equation when
the compared values are structurally available. It cannot prove that a hidden
setup trapdoor was sampled honestly or that a verification key commits to the
intended relation merely from a successful verifier run.

Analysis owns the proposition and theorem profile for completeness,
soundness/knowledge, zero knowledge, setup assumptions, Fiat--Shamir model,
challenge-sharing loss, poles, field characteristic, and batching error.
Evidence supports exact premises; it does not change semantic owners.

## 8. Durable action

| Action | Owner |
|---|---|
| retain `PublicProverParameterDecl` and recipe operand as a candidate; co-design with post-challenge Plan finalization before rotating dependent profiles | next accumulation package, then `pir/interfaces-and-plans.md` if selected |
| require at least one challenge for canonical-framed FS | `pir/fiat-shamir.md` and common Protocol lifecycle clarification |
| state proof-package projection and public-construction boundary | `pir/interfaces-and-plans.md` |
| retain exact commitment-profile use/non-use law | `pir/commitment-opening-verification.md` |
| retain setup/relation correspondence as a separate premise | `relations/relation-model.md` and future Analysis profiles; no new setup root now |
| record cross-case architecture and scope | project indexes and portfolio |

## 9. Reopening conditions

Reopen this selection only with a concrete counterexample showing one of:

1. a verifier schedule cannot be represented without dynamic child execution;
2. transcript continuity cannot survive checked finite elaboration;
3. public construction material must affect verifier semantics despite having
   no verifier read, when the selected architecture deliberately separates the
   common source setup into verifier and prover projections;
4. setup correctness needs a shared, portable checked construction rather
   than a scheme-specific premise and Evidence;
5. proof-package projection cannot preserve a source's causal message order;
6. an exact opening operation cannot fit an existing profile without erasing
   a shared verifier law; or
7. family-level theorem composition cannot refer to finite Core members
   without duplicating runtime authority.

No reviewed case supplies such a counterexample.

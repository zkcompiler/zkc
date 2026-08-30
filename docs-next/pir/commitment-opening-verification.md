# Commitment-Opening Verification

> **Document kind:** Target semantic specification
> **Document state:** Active non-normative target
> **Provisional owner:** `pir`
> **Authority:** None during the transition. Current normative Protocol
> semantics remain under [`docs/`](../../docs/README.md).

## 1. Contract

This page owns the target verifier-side meaning of a public commitment-opening
claim group and its exact use by an admitted `InteractiveCore`. It defines:

- a separately identified commitment-opening verifier profile;
- typed public setup, verification context, commitment, query, asserted-answer,
  and evidence roles;
- exact Core attachment and admission;
- public replay and identity locality;
- exact KZG single, multipoint, same-point aggregation, and independent-proof
  verification-aggregation profile shapes; and
- outcomes, nonclaims, and reversal conditions.

The [Interactive Core](interactive-core.md) owns values, bindings, challenges,
derived values, checks, occurrences, execution, and replay. The
[Oracle-Commitment Construction](oracle-commitment-construction.md) may consume
one of this page's verifier profiles while retaining its own source/target,
producer, advice, evidence-coverage, authority, and run-validation semantics.
Foundation owns canonical values, semantic profiles, portable algorithms,
evaluation contracts, identities, and deterministic evaluation.

This page does not own honest commitment or proof generation, private
polynomial or Oracle material, relation grounding, a setup ceremony, or a
cryptographic property. Those remain with Plan or a construction-specific
producer adapter, Relations, Evidence, and Analysis respectively.

## 2. Semantic profile and declaration intake

For one exact Foundation `PriorMetaAuthenticationBasis B`, this owner consumes
the exact `PIRInteractionProfileId`, authenticated Foundation value types and
portable algorithms, and one exact immutable admitted Core handle.

```text
PIRCommitmentOpeningProfile = SemanticLanguageProfile {
  profile_family: "pir.commitment-opening",
  revision: 1,
  profile_imports: {PIRInteractionProfileId},
  supported_subject_kinds: {
    "pir.commitment-opening-verifier-profile",
    "pir.commitment-opening-use"
  },
  declaration_catalogs: {},
  semantic_law_source: exact nonempty bytes for this page
}

PIRCommitmentOpeningProfileId =
  SemanticContentId<"foundation.semantic-language-profile">(
    B, SemanticLanguageProfileBody(PIRCommitmentOpeningProfile))
```

This owner uses no profile-local `DeclarationRef`, so its Foundation declaration
catalog sequence is exactly empty. The exact subject body compilers below and
the nonempty semantic-law source close the syntax. A verifier profile carries
its own six exact `PIRAlgorithmUse` values, so adding an unrelated verifier-
profile subject does not change the language profile or any existing subject
ID. All six algorithms are total. A mathematical partiality, decoder error, or
malformed proof must be represented by a total tagged input or Boolean result;
it cannot escape as a host exception. Bound derivation has the exact profile-
shape input and intrinsic-bound output described below.

The body compiler has no open arm:

```text
CommitmentOpeningBody =
    CommitmentOpeningVerifierProfileBodyV0(
      CommitmentOpeningVerifierProfile)
  | CommitmentOpeningUseBodyV0(CommitmentOpeningUse)

CommitmentOpeningVerifierProfileBodyV0(p) =
  the exact Foundation MetaValue recursive lift of the Section 3.2 profile
  record in written field order

CommitmentOpeningUseBodyV0(u) =
  the exact Foundation MetaValue recursive lift of the Section 4.1 use record
  in written field order

CommitmentOpeningId<K>(x) =
  ProfiledSemanticId<K>(
    B, PIRCommitmentOpeningProfileId,
    the exact body arm assigned to K)
```

A missing required import or kind is `Refused`; another regime or body arm is
`KindMismatch`; an unrecognized exact profile root is `Unsupported`.

## 3. Exact verifier profile

### 3.1 Static roles and dependent types

```text
AlgorithmUse = PIRAlgorithmUse

CommitmentSetupRole = {
  role_ordinal: Natural,
  value_type: ValueType
}

CommitmentVerificationContextRole = {
  role_ordinal: Natural,
  value_type: ValueType,
  source_requirement: AnyPublicValue | ChallengeOutput
}

CommitmentOpeningScheduleAtom =
    ContextValue(role_ordinal)
  | ClaimCommitment(claim_ordinal)
  | ClaimQuery(claim_ordinal)
  | ClaimAssertedAnswer(claim_ordinal)
  | OpeningEvidence
  | ClaimGroupCheck
  | OpeningCheck

CommitmentOpeningScheduleConstraint = {
  predecessor: CommitmentOpeningScheduleAtom,
  successor: CommitmentOpeningScheduleAtom
}

OpeningClaimValue<P> = {
  public_commitment: CanonicalValue<P.public_commitment_type>,
  query: CanonicalValue<P.query_type>,
  asserted_answer: CanonicalValue<P.asserted_answer_type>
}

OpeningClaimGroup<P> =
  CanonicalRecord<
    ordinal i -> OpeningClaimValue<P>
    for every i in 0 .. P.claim_count-1>

CommitmentSetupAssignment<P> =
  CanonicalRecord<
    ordinal r.role_ordinal -> CanonicalValue<r.value_type>
    for r in P.setup_roles>

CommitmentVerificationContext<P> =
  CanonicalRecord<
    ordinal r.role_ordinal -> CanonicalValue<r.value_type>
    for r in P.verification_context_roles>

CommitmentSetupAssignmentType<P> =
  the exact same-regime Foundation ValueType for the recursively lifted
  CommitmentSetupAssignment<P> record

CommitmentVerificationContextType<P> =
  the exact same-regime Foundation ValueType for the recursively lifted
  CommitmentVerificationContext<P> record

OpeningClaimGroupType<P> =
  the exact same-regime Foundation ValueType for the recursively lifted
  OpeningClaimGroup<P> record
```

`claim_count` is exact and positive. A Core is finite, so one exact use knows
its cardinality statically. A different cardinality is another exact profile
or profile-family instance; no runtime tuple packing can change the verifier's
ABI or security-relevant coefficient schedule.

The fixed packer ABIs are:

```text
PackSetupAssignment:
  [role value types in role order]
    -> CommitmentSetupAssignmentType<P>

PackVerificationContext:
  [context value types in role order]
    -> CommitmentVerificationContextType<P>

PackOpeningClaimGroup:
  [for each claim in claim order:
     public_commitment_type, query_type, asserted_answer_type]
    -> OpeningClaimGroupType<P>

CheckClaimGroup:
  [CommitmentSetupAssignmentType<P>,
   CommitmentVerificationContextType<P>,
   OpeningClaimGroupType<P>]
    -> RootBool

VerifyOpeningGroup:
  [CommitmentSetupAssignmentType<P>,
   CommitmentVerificationContextType<P>,
   OpeningClaimGroupType<P>,
   P.opening_evidence_type]
    -> RootBool
```

The packers are profile-owned canonical formation operations. They neither
validate a cryptographic proposition nor obtain ambient values. The group
check owns only exact runtime shape conditions such as a common commitment,
common point, distinct points, canonical member order, or supported setup
capacity. The opening check owns the exact public verifier computation. Both
checks must be true on an accepting path.

### 3.2 Profile body

```text
CommitmentOpeningVerifierBounds = {
  maximum_setup_roles: Natural,
  maximum_context_roles: Natural,
  exact_claim_count: PositiveNatural,
  maximum_setup_bytes: Natural,
  maximum_context_bytes: Natural,
  maximum_claim_group_bytes: Natural,
  maximum_evidence_bytes: Natural,
  maximum_schedule_constraints: Natural,
  maximum_group_check_steps: Natural,
  maximum_opening_check_steps: Natural,
  maximum_canonical_body_bytes: Natural
}

CommitmentOpeningVerifierBoundsType =
  the exact same-regime Foundation ValueType for the recursively lifted
  CommitmentOpeningVerifierBounds record

CommitmentOpeningVerifierStaticShape = {
  profile_name: BoundedSymbol,
  profile_version: PositiveNatural,
  static_semantic_parameter_type: ValueType,
  static_semantic_parameters:
    CanonicalValue<static_semantic_parameter_type>,
  setup_roles: CanonicalSeq<CommitmentSetupRole>,
  verification_context_roles:
    CanonicalSeq<CommitmentVerificationContextRole>,
  public_commitment_type: ValueType,
  query_type: ValueType,
  asserted_answer_type: ValueType,
  opening_evidence_type: ValueType,
  claim_count: PositiveNatural,
  schedule_constraints:
    CanonicalSortedUniqueSeq<CommitmentOpeningScheduleConstraint>,
  pack_setup_assignment: AlgorithmUse,
  pack_verification_context: AlgorithmUse,
  pack_opening_claim_group: AlgorithmUse,
  check_claim_group: AlgorithmUse,
  verify_opening_group: AlgorithmUse,
  exact_failure_catalog:
    CanonicalSortedUniqueSet<TypedFailureCoordinate>
}

CommitmentOpeningVerifierStaticShapeType =
  the exact same-regime Foundation ValueType for the recursively lifted
  CommitmentOpeningVerifierStaticShape record

CommitmentOpeningVerifierProfile = {
  profile_name: BoundedSymbol,
  profile_version: PositiveNatural,

  static_semantic_parameter_type: ValueType,
  static_semantic_parameters:
    CanonicalValue<static_semantic_parameter_type>,
  setup_roles: CanonicalSeq<CommitmentSetupRole
                            in dense role-ordinal order>,
  verification_context_roles:
    CanonicalSeq<CommitmentVerificationContextRole
                 in dense role-ordinal order>,

  public_commitment_type: ValueType,
  query_type: ValueType,
  asserted_answer_type: ValueType,
  opening_evidence_type: ValueType,
  claim_count: PositiveNatural,
  schedule_constraints:
    CanonicalSortedUniqueSeq<CommitmentOpeningScheduleConstraint>,

  pack_setup_assignment: AlgorithmUse,
  pack_verification_context: AlgorithmUse,
  pack_opening_claim_group: AlgorithmUse,
  check_claim_group: AlgorithmUse,
  verify_opening_group: AlgorithmUse,
  intrinsic_bound_law: {
    derive: AlgorithmUse,
    declared_bounds: CommitmentOpeningVerifierBounds
  },
  exact_failure_catalog:
    CanonicalSortedUniqueSet<TypedFailureCoordinate>
}

CommitmentOpeningVerifierProfileId =
  CommitmentOpeningId<"pir.commitment-opening-verifier-profile">(profile)
```

The six profile-local algorithm ABIs are exactly the five pack/check ABIs in
Section 3.1 plus:

```text
DeriveVerifierBounds:
  [CommitmentOpeningVerifierStaticShapeType]
    -> CommitmentOpeningVerifierBoundsType
```

The bound algorithm receives the exact static shape reconstructed from the
authenticated profile body. That shape excludes the bound algorithm and its
declared result, so bound derivation is finite and non-circular. Every
`AlgorithmUse` field identifies its own portable algorithm and evaluation
contract. Formation requires the referenced contract to have the written
input types, output type, total deterministic bounded disposition, and exactly
the applicable coordinates in `exact_failure_catalog`; there is no ambient
role registry or profile ordinal.

`static_semantic_parameters` is an exact typed record owned by the selected
profile. It may contain a field, group, pairing, generator, degree-bound,
domain, hash, Merkle layout, leaf codec, salt policy, coefficient rule, or
other static declaration coordinate. It may not contain a runtime SRS, salt,
blind, private polynomial, Oracle carrier, proof, challenge value, evaluator
limit, or observed resource count.

Formation authenticates every type, algorithm, evaluation contract, and
static parameter; checks dense role ordinals and the exact ABIs above; requires
every schedule atom ordinal to exist and the schedule graph to be acyclic;
derives the dependent types; reconstructs the exact
`CommitmentOpeningVerifierStaticShape`; independently reruns the intrinsic-
bound law on that value; and requires the result to equal `declared_bounds`. A
declared positive Boolean or authored test vector cannot replace any check.

Changing a static parameter, role, type, algorithm, contract, claim count,
failure coordinate, or bound rotates the profile ID. Adding an unrelated
sibling profile does not.

## 4. Exact Core use

### 4.1 Coordinates

```text
CommitmentOpeningUseBounds = {
  exact_setup_bindings: Natural,
  exact_groups: PositiveNatural,
  exact_claim_coordinates: PositiveNatural,
  exact_context_values: Natural,
  exact_derived_values: PositiveNatural,
  exact_checks: PositiveNatural,
  maximum_admission_check_steps: Natural,
  maximum_canonical_body_bytes: Natural
}

CommitmentSetupRoleBinding = {
  role_ordinal: Natural,
  public_parameter: BindingRef
}

CommitmentOpeningClaimCoordinate = {
  public_commitment: ValueRef,
  query: ValueRef,
  asserted_answer: ValueRef
}

CommitmentOpeningGroupUse = {
  context_values: CanonicalSeq<ValueRef in context-role order>,
  claims:
    CanonicalSeq<CommitmentOpeningClaimCoordinate
                 of exact profile.claim_count in authored claim order>,
  opening_evidence: ValueRef,

  packed_context: DerivedValueRef,
  packed_claim_group: DerivedValueRef,
  claim_group_check: CheckRef,
  opening_check: CheckRef
}

CommitmentOpeningUse = {
  core_id: CoreId,
  verifier_profile_id: CommitmentOpeningVerifierProfileId,
  setup_bindings:
    CanonicalSeq<CommitmentSetupRoleBinding in role order>,
  packed_setup_assignment: DerivedValueRef,
  groups: CanonicalNonEmptySeq<CommitmentOpeningGroupUse>,
  exact_bounds: CommitmentOpeningUseBounds
}

CommitmentOpeningUseId =
  CommitmentOpeningId<"pir.commitment-opening-use">(use)
```

Each setup binding resolves to a `PublicBindingDecl` whose class is exactly
`PublicParameter`; equal types at a Statement or SessionContext coordinate do
not substitute. Every setup role appears once and no other binding enters the
packed assignment.

For each group, the named `DerivedValueDecl`s use the exact profile packers and
precisely the listed input `ValueRef`s in written order. The named checks use
the exact profile check algorithms and inputs:

```text
claim_group_check.inputs =
  [packed_setup_assignment, packed_context, packed_claim_group]

opening_check.inputs =
  [packed_setup_assignment, packed_context,
   packed_claim_group, opening_evidence]
```

Both checks must occur after all their inputs and must be required true by
every reachable accepting terminal. A `ChallengeOutput` context role resolves
to the output of exactly one Core Challenge occurrence. An `AnyPublicValue`
role must be in the Core's public dependency closure at its use boundary.

Admission substitutes the exact group coordinates into every profile schedule
constraint. For a value atom, its boundary is the Core occurrence that first
makes the value available; a public binding or constant is available at the
scope-entry boundary. For a check atom, its boundary is its `InvokeCheck`
occurrence. Every predecessor boundary must strictly precede its successor
boundary in the Core order. This profile-local graph, rather than prose or an
algorithm callback, owns requirements such as `all claims < v < W` or
`all claims and proofs < u`. Evidence may carry several fields, but it is never
the authority for an asserted answer.

### 4.2 Authentication and admission

```text
CanonicalCommitmentOpeningUseCandidate
  --AuthenticateCommitmentOpeningUse-->
AuthenticatedCommitmentOpeningUseCandidate
  --AdmitCommitmentOpeningUse-->
AdmittedCommitmentOpeningUse
```

Authentication recomputes `CommitmentOpeningUseId` and every imported body in
one request-local hash-binding ledger. It grants no execution or property
authority.

Admission receives exact immutable admitted Core and verifier-profile handles
and checks, in order:

1. same basis, regime, profile import, and exact ID/body equations;
2. exact setup-role totality, class, type, and packer wiring;
3. exact group cardinality, value types, and claim order;
4. context role types and source requirements;
5. evidence type and availability;
6. exact packer algorithms, inputs, outputs, and bounds;
7. exact group and opening check algorithms and inputs;
8. every profile-local schedule constraint after exact coordinate
   substitution;
9. ordinary occurrence causality and scope;
10. every accepting terminal's closure over both checks; and
11. independently derived use bounds and canonical-body limits.

A commitment, query, answer, context, evidence, or check coordinate may appear
in several uses only when each exact use names it. Admission infers no
equivalence, reduction, or proof sharing from that overlap.

The admitted handle retains the exact Core and profile handles, authenticated
basis, body, evaluator identity, and admission result. Serialization is inert.
Cold use reauthenticates and readmits all three subjects.

### 4.3 Defects and outcomes

```text
CommitmentOpeningUseDefect =
    CoreIdentityMismatch | VerifierProfileMismatch
  | SetupRoleMapIncomplete | SetupBindingClassMismatch
  | SetupTypeMismatch | SetupPackerMismatch
  | ContextRoleMismatch | ContextSourceMismatch | ContextPackerMismatch
  | ClaimCountMismatch | ClaimTypeMismatch | ClaimOrderMismatch
  | ClaimPackerMismatch | EvidenceTypeMismatch
  | ClaimGroupCheckMismatch | OpeningCheckMismatch
  | ScheduleConstraintMismatch | CausalityViolation | AcceptingClosureFailure
  | IntrinsicBoundMismatch

CommitmentOpeningUseDefectSet =
  CanonicalNonEmptySortedUniqueSeq<
    CommitmentOpeningUseDefect in written tag order>
```

Malformed carriers are `Malformed`; wrong kind, regime, or ABI is
`KindMismatch`; unavailable exact profile support is `Unsupported`; missing
authenticated dependencies are `MissingDependency`. A well-formed candidate
failing the predicates above returns `Negative(defect_set)`. Insufficient
evaluation limits return `DeterministicLimitExceeded`; inconsistent providers
or evaluators return `CheckerFailure`. No failure emits a partial admitted
use.

## 5. Runtime setup, execution, and replay

At execution, `IssuePublicSetupInvocationView` supplies every exact
`PublicParameter` value selected by the use. The Core's ordinary derived-value
engine runs the three packers, then its checks run the exact group and opening
algorithms. The accepting terminal remains unavailable when either check is
false.

The runtime setup value is not ambient state. Every verifier algorithm receives
the packed assignment as its first explicit input. A registry lookup, process
default, private advice, setup name without content, or another invocation's
value cannot substitute.

Changing a runtime setup value changes `CoreInvocationId` and
`PublicSetupInvocationViewId`; it does not change the generic Core or verifier
profile unless the value was intentionally embedded as a Core constant.
Ceremony identity, contribution history, updateability, entropy, and trapdoor
destruction are not implied by a canonical setup value.

Public replay uses only the admitted Core invocation, complete public record,
exact setup view, and the algorithms already required by Core replay. It
reruns all packers and both checks. It needs no private polynomial, complete
logical Oracle, commitment randomness, opening randomness, setup trapdoor,
ProverPlan, prior receipt, or security theorem.

Core execution and replay are already authoritative for the check results.
This page introduces no parallel run receipt or producer-owned proof record.

## 6. Exact profile families

The definitions below constrain exact profile instances. They are not a
universal KZG or Merkle theorem.

### 6.1 Merkle-authenticated Oracle answer

A Merkle profile has one or more exact claims whose public commitments are
roots, queries are leaf coordinates, asserted answers are leaf payloads, and
evidence contains the profile-selected authentication nodes and disclosed
salts. Its static parameters own leaf encoding, framing, arity, padding, tree
or cap layout, hash algorithm, salt policy, and evidence codec.

An unsalted and a salted profile are distinct. A multiproof may cover several
claims through one evidence value if its exact claim count, incidence, and
verifier algorithm are profile identity. Evidence sharing proves no collision
resistance, binding, or zero knowledge.

The retained FRI/Merkle construction is a narrower instance: equal
`(root,index,answer)` claims may be covered by one exact evidence group and
slot under its profile-local law. That rule does not define Merkle multiproofs
generally.

### 6.2 KZG single opening

An exact single-opening profile has:

```text
claim_count = 1
setup_roles = exact public SRS capability values
verification_context_roles = []
OpeningClaimValue = (C,z,y)
opening_evidence = W
```

Static parameters identify the scalar field, groups, pairing, generators,
codecs, supported degree, and exact verifier equation. The group check enforces
the supported setup and type-level shape. The opening check executes the exact
pairing predicate for `(SRS,C,z,y,W)`.

Its schedule graph places `C`, `z`, and `y` before evidence `W`, and `W` before
the opening check. A source profile in which a proof precedes its complete
claim is a different interaction.

The point `z` may originate from a Statement, a deterministic public value, or
an enclosing Challenge. That origin belongs to the exact Core use and to any
Analysis question, not to universal KZG semantics.

### 6.3 Original KZG one-polynomial multipoint opening

An exact multipoint profile has a fixed claim count greater than one, no
verification-context challenge, one common commitment, distinct query points,
and evidence containing the remainder polynomial `r` and quotient witness
`W_B`. The group check requires the common commitment and distinct points. The
opening check requires:

```text
degree(r) < claim_count
r(z_i) = y_i for every claim i
the exact KZG multipoint pairing equation
```

The setup schema must expose enough second-group capability to evaluate the
vanishing polynomial at the hidden setup point. A minimal single-opening
`([1],[tau])` second-group basis does not satisfy that schema.

Its schedule graph places every claim field--the common commitment, each point,
and each asserted answer--before the remainder-and-witness evidence, then
places that evidence before the opening check. No verifier batching context
occurs.

This profile has no batching challenge. Adding one creates another profile and
cannot be cited as the original construction.

### 6.4 KZG same-point linear-combination opening

An exact same-point aggregation profile has a claim count greater than one,
one `ChallengeOutput` context role `v`, one common query point, ordered
commitments and asserted answers, and one aggregate witness `W`.

The group check requires all query values equal and preserves the authored
member order. The opening check uses coefficients
`1,v,...,v^(claim_count-1)` in that order and executes the exact aggregate
pairing predicate.

The exact Core use additionally requires:

1. every commitment, query point, and asserted answer available before the
   `v` occurrence;
2. `v` available before `W`;
3. `W` available before both checks; and
4. every accepting terminal closed over those checks.

These are not commentary-only obligations. The profile schedule graph contains
edges from every claim field to context role `v`, from `v` to
`OpeningEvidence`, and from the evidence to both checks.

This profile is a native verifier interaction shape. It is not an affirmative
structural rewrite from completed single-opening proofs. Any claim that a
compiler may replace individual openings with this interaction requires a
separate checked change plus an Analysis theorem and quantitative loss.

### 6.5 KZG independent-proof verification aggregation

An exact verification-aggregation profile retains every individual proof in
its evidence record. It has one coefficient challenge or a construction-
specific deterministic coefficient context, an ordered claim sequence, and
one aggregate pairing check.

For a Fresh challenge, all commitments, points, asserted answers, and proof
elements must precede it. For a Fiat--Shamir interpretation, the exact
transcript construction must protect the complete same prefix. The profile's
static parameters identify coefficient framing, domain separation, tuple
order, and aggregate equation.

The profile schedule graph therefore places every claim field and the complete
proof-bearing evidence value before the coefficient context, and places that
context before the aggregate opening check. A profile with evidence after the
coefficient is a different operation and cannot claim this classification.

This profile compresses verification work. It neither reduces the claim count
nor replaces several proof elements with one. Calling it a multipoint opening
or same-point proof aggregation is a kind error at the architecture level.

## 7. Binary-field IOPCS use

The zero-knowledge binary-field IOPCS remains an `InteractiveCore` with finite
logical Oracles. Its virtual initial word is represented at each query by:

```text
AnswerOracle(f,x)
AnswerOracle(f_prime,x)
DerivedValue(alpha * answer_f + answer_f_prime)
```

It receives no publication, commitment, or independent opening. Positive
folded words remain actual `ProverOracle`s. The same challenge occurrence may
feed both Sumcheck and FRI consumers under Core's existing typed sharing law.

A later BCS target uses exact salted Merkle verifier profiles for the actual
Oracle publications and answers. The source Core owns `f_prime`, `s_prime`,
`alpha`, Sumcheck/FRI interleaving, terminal coefficients, and query schedule;
the Oracle construction does not insert them.

Commit-time high-coefficient pads, evaluation-time auxiliary-Oracle
randomness, and BCS leaf salts retain separate Plan/construction advice roles.
The exact one-evaluation-session and query-budget scope belongs to the
selected protocol and its Analysis question. Structural execution of a salted
profile proves no zero knowledge.

## 8. Ownership and identity matrix

| Subject or fact | Owner | Identity effect |
|---|---|---|
| verifier profile schema, static parameters, algorithms, and bounds | PIR | verifier-profile ID |
| exact Core coordinates using that profile | PIR | commitment-opening-use ID |
| runtime public SRS or transparent parameter value | PIR invocation | invocation and public-setup-view IDs |
| hard-coded setup constant | PIR Core | Core ID |
| honest commit/open algorithm and private state | Plan or construction producer | Plan/construction identity, not verifier-profile ID |
| private material-to-commitment and evaluation correspondence | Relations | exact grounding/correspondence identity |
| setup distribution, binding, hiding, extraction, correctness, ZK, or quantitative loss | Analysis | exact question/judgment identity |
| ceremony, conformance, implementation, or replay observation | Evidence | evidence-record identity |

An admitted use proves only that one exact Core is wired to one exact public
verification profile. It cannot be used as a Relations or Analysis result.

## 9. Nonclaims

Profile formation, use admission, Core execution, and replay establish none of:

- commitment correctness, binding, hiding, extractability, or opening
  knowledge;
- source-polynomial or source-Oracle existence, uniqueness, or degree;
- relation satisfaction or material-to-commitment correspondence;
- honest, updateable, or trustworthy setup, or trapdoor destruction;
- collision resistance, zero knowledge, BCS applicability, FRI proximity, or
  protocol soundness;
- equivalence between individual and aggregated openings;
- Fresh-to-Fiat--Shamir theorem applicability, ROM, EPROM, or QROM security;
- concrete group, pairing, hash, codec, or provider conformance;
- OIR, backend realization, side-channel safety, deployment, or production
  support.

These are not caveats that a caller may override with a Boolean. They are
separate typed questions owned downstream.

## 10. Reversal conditions

Reopen this boundary if a source-faithful admitted case shows that:

1. a verifier algorithm necessarily consumes private producer material;
2. an exact public setup cannot be supplied through `PublicParameter`
   bindings without ambient authority;
3. separating asserted answers from evidence changes the source transcript;
4. a fixed finite Core cannot identify its claim cardinality or member order;
5. public replay needs a setup trapdoor, private polynomial, or unqueried
   Oracle carrier;
6. a necessary use cannot be expressed without a generic runtime callback;
7. the binary-field virtual word cannot be represented by paired queries and
   derived values; or
8. two constructions classified separately here prove observationally and
   theoremically identical under exact source pressure.

Implementation convenience, API unification, or the word “batch” in two
sources is not reversal evidence.

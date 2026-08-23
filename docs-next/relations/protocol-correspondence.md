# Protocol correspondence for relations

> **Document kind:** Target semantic specification
> **Document state:** Active non-normative target
> **Target status:** Stage 3.5 durable promotion
> **Provisional owner:** `relations`
> **Authority:** This document specifies the selected target for `docs-next/`.
> It is non-normative until explicit consolidation and cutover. The current
> specifications under [`docs/`](../../docs/README.md) remain authoritative.
> This document makes no implementation, migration, compatibility, or
> downstream property-establishment claim.

## 1. Scope and design center

This document defines two Relations-owned checked judgments:

1. structural correspondence between one exact admitted Protocol at one exact
   admitted `ProtocolInterface` and one exact admitted relation Interface and
   binding; and
2. value-level correspondence between one admitted relation instance and one
   decoded `ProtocolPublicAssignment<P>` after affirmative public-port
   structural correspondence.

The [relation semantic model](relation-model.md) owns relation Interfaces,
instances, bindings, value bridges, artifact comparison, committed-object
grounding, and their admitted capabilities. The
[Protocol Interface and Plan specification](../pir/interfaces-and-plans.md)
owns `ProtocolInterface`, statement decoding, and
`ProtocolPublicAssignment<P>`. The
[transition and bridge architecture](../project/transition-and-bridge-architecture.md)
owns the shared checked-result, authority, and replay discipline. The
[Relations index](README.md) remains the domain map.

Correspondence is question-scoped, field-factored, and post-admission. It does
not admit any operand, execute the Protocol, interpret raw artifact bytes,
inspect a private witness, or establish satisfaction. A binding is a proposal;
only this owner check can establish the exact agreements or disagreements
named by a `CorrespondenceQuestion`.

## 2. Imported exact subjects and reference discipline

This specification consumes, but does not redefine, the following exact
admitted subjects and capabilities:

| Input | Owning contract | Required authority |
|---|---|---|
| `AdmittedProtocol` and Relations-purpose Protocol view | PIR | Exact Protocol ID/regime, embedded Core view, and every source fact permitted by the requested clauses |
| `AdmittedProtocolInterface` | PIR Interface | Exact dependent Protocol ID, public-assignment domain and lossless statement binding, proof positions, application bindings, and terminal/reference views |
| `AdmittedRelationInterface` | Relation model | Exact definition ref, regime-qualified dependency closure, occurrence-expanded public/witness/object schemas, and accepted-result role |
| `AdmittedRelationBinding` | Relation model | Exact dependent IDs, occurrence-total maps, admitted bridge/grounding dependency views, object entries, and closed result binding |
| `CheckedArtifactInterfaceComparison` | Relation model | Exact observation, relation Interface, nonempty field question, `CorrespondenceRegime`, and completed A/N field facts |
| `CheckedCommittedObjectGrounding` | Relation model | Exact Protocol/Interface/relation/binding operands, conditional observation map, `CorrespondenceRegime`, and completed A/N grounding facts |
| `AdmittedRelationInstance` | Relation model | Exact relation Interface ID and occurrence-total public-value assignment |
| `ProtocolPublicAssignment<P>` | PIR Interface | Total same-domain map over every and only public input `Statement` occurrence of the exact Protocol `P` |

Bare `CoreRef<K>` values are structural references within one Core. Any
interpretation-sensitive read is qualified by the exact dependent
`ProtocolId`, Interface, and admitted view. Relation occurrence references are
likewise expanded from their exact Interface multiplicities. Ordinal equality,
unqualified digests, names, or equal bytes never create a cross-owner
reference.

Every algorithm executed by correspondence is selected by an admitted binding
or Interface and its exact regime-qualified dependency view. A caller cannot
select a replacement codec, bridge, adapter, fact, grounding algorithm, or
checker through an ambient registry.

## 3. Question algebra

### 3.1 Structural question

~~~text
CorrespondenceBaseClause =
    PublicPorts
  | WitnessPorts
  | ResultBindingReferenceShape
  | CommittedObjectGrounding

CorrespondenceQuestion = {
  base_clauses: CanonicalSet<CorrespondenceBaseClause>,
  artifact_question: Optional<ArtifactComparisonQuestion>
}

base_clauses is nonempty OR artifact_question is present
~~~

`ArtifactComparisonQuestion` is the nonempty canonical set of relation
Interface fields defined by the relation model. It is a separate optional
nested question, not a fifth base-clause constructor. There is at most one
artifact question.

The question is an exact operand of the check. It determines:

- every source field the checker may read;
- the exact prerequisite checked results that must be supplied;
- every result field the completed judgment must contain; and
- every field about which the result makes no claim.

An empty base set with no artifact question is malformed. A result over a
subset, superset, different nested artifact field set, or different regime
cannot answer the question.

### 3.2 Prerequisite presence rule

| Requested question member | Exact prerequisite | Absent or mismatched | Extra input when unrequested |
|---|---|---|---|
| `CommittedObjectGrounding` | `CheckedCommittedObjectGrounding` retaining the identical Protocol object view, Protocol Interface, relation Interface, binding, and `CorrespondenceRegime` | `CannotAnswer` | Refused as an undeclared read |
| `artifact_question = Some(q)` | `CheckedArtifactInterfaceComparison` retaining its exact admitted observation, the identical relation Interface and `CorrespondenceRegime`, and exactly `q` | `CannotAnswer` | Refused as an undeclared read |

A prerequisite may be an affirmative or negative completed capability. Its
affirmative result supports the requested field. Its negative result refutes
that field and contributes its retained unaffected agreements. A raw artifact
observation, adapter assertion, admitted grounding declaration, or serialized
result cannot substitute.

The admitted `CorrespondenceRegime` binds one exact authenticated capability
contract and ABI:

~~~text
RelationsCorrespondenceResultFamily =
    ArtifactInterfaceComparison
  | CommittedObjectGrounding
  | StructuralCorrespondence
  | InstanceCorrespondence

RelationsCorrespondenceCapabilityAbi = {
  exact result-family set above,
  exact operand, completed A/N result, and checked-result binding schema per
    family,
  exact RelationsOperationPurpose<R> ABI per family R,
  exact NamedConsumer and purpose indices retained by every result and
    capability,
  exact freshness, process-lifetime, and binding-equality requirements
}

RelationsCorrespondenceCapabilityAbiId = H(
  "zkc/relations-correspondence-capability-abi",
  CanonicalEncode(RelationsCorrespondenceCapabilityAbi))

RelationsCorrespondenceCapabilityContract = {
  exact Relations owner domain and contract version,
  exact RelationsCorrespondenceCapabilityAbiId,
  exact covered result-family set,
  exact result-family-, named-consumer-, and typed-purpose-indexed invocation
    and capability-use rules,
  exact result-family-, named-consumer-, and typed-purpose-indexed completed-
    result-record creation, portable stable-identity, owner-private association,
    retention, and disclosure rules,
  exact result-family-, named-consumer-, and typed-purpose-indexed attempt-audit
    creation, stable-identity, retention, and disclosure rules, separately from
    completed-result records,
  explicit no-separate-owner-operation-policy clause for every covered family,
  exact reconstruction and replay-equality contract
}

RelationsCorrespondenceCapabilityContractId = H(
  "zkc/relations-correspondence-capability-contract",
  CanonicalEncode(RelationsCorrespondenceCapabilityContract))
~~~

The contract preimage does not name the containing regime, so there is no
identity cycle. `CorrespondenceRegime` admission authenticates both canonical
preimages, recomputes both IDs, checks ABI/contract agreement and exact family
coverage, and binds them immutably; there is no separately reusable contract
capability. The contract explicitly declares that the four operations have no
separate owner operation policy. This is an affirmative owner-contract clause,
not an omitted field. The contract itself must separately authorize invocation,
capability use, completed-result construction and retention, attempt-audit
construction and disclosure, and replay for the exact family, named consumer,
and typed purpose; none of those permissions implies another. In particular,
it does not silently authorize portable attempt audits. An Analysis source-policy closure may therefore use only
`OwnerDefinesNoOperationPolicy(RelationsCorrespondenceCapabilityContractId,
RelationsCorrespondenceCapabilityAbiId)` for these capabilities. A regime whose
authenticated contract and ABI do not make that declaration is incompatible
with this seam.

## 4. Structural Protocol-at-Interface correspondence

### 4.1 Signature

This signature and the instance-correspondence signature in Section 7 are the
`Ready` forms of the closed family-indexed
[Relations checked-operation ingress](relation-model.md#8-artifactinterface-comparison).
Missing, malformed, or unauthorized partial inputs are represented by that
capability-neutral carrier and its exact U/C/R/M/F attempt outcome, never by
constructing either complete signature.

~~~text
RelationCorrespondsAtInterface(
  AdmittedProtocol,
  AdmittedProtocolInterface,
  AdmittedRelationInterface,
  AdmittedRelationBinding,
  CorrespondenceQuestion,
  Optional<CheckedArtifactInterfaceComparison>,
  Optional<CheckedCommittedObjectGrounding>,
  exact ExactSourceAuthorityBinding for every admitted root and supplied
    checked prerequisite, with separately supplied fresh capabilities,
  exact named_consumer: NamedConsumer,
  exact operation_purpose:
    RelationsOperationPurpose<StructuralCorrespondence>,
  CorrespondenceRegime)
  -> Qualified<CheckedRelationCorrespondenceJudgment,
               exact ExactCheckedResultAuthorityBinding<Relations,
                 StructuralCorrespondence>>
~~~

All four admitted roots must agree on their exact dependent identities and
regimes. The Protocol Interface names the supplied Protocol. The binding names
that Interface and the supplied relation Interface. The checked prerequisites,
when required, retain the identical operands, regime, and nested question.
Every source binding must match its fresh capability and contributes exactly
one authenticated owner-policy disposition to the canonical total transitive
source-policy closure. The checker freshly validates every bound policy or
explicit no-policy owner contract for the named correspondence purpose. It also
reauthenticates the exact correspondence capability contract and ABI preimages
bound by the regime and requires their invocation and capability-use rules to
permit this exact family, named consumer, and typed purpose.

The checker consumes owner-defined narrow views. It does not receive a
universal Protocol fact root or an ambient relation environment.

### 4.2 `PublicPorts`

When requested, `PublicPorts` compares:

- the complete multiplicity-expanded relation public occurrence domain;
- the binding's total injective public map and its exact image;
- the exact dependent Interface domain of every and only public input
  `Statement` occurrence;
- the relation and Protocol domains and ABIs of every binding-owned
  `RelationToProtocolValueBridge`;
- both admitted bridge round-trip laws; and
- the lossless Interface statement shape and decoding contract.

The clause is affirmative only when the public-map image equals the complete
`CanonicalPublicAssignmentDomain` of the dependent Interface: every and only
public input `Statement` occurrence is covered exactly once. A strict subset
is a meaningful negative. An extra target, duplicate target, or domain/position
mismatch cannot enter through an admitted binding and therefore does not
become negative correspondence.

Structural correspondence compares occurrence, role, position, domain, map,
and algorithm facts. It has no relation instance or runtime statement value,
so it does not claim equality of a particular public assignment. The exact
instance-level check in Section 7 owns that result.

An admitted binding is allowed to map only a subset of the Protocol statement
surface. Therefore `PublicPorts` can return a meaningful negative when the
question requires exact image/cardinality agreement.

### 4.3 `WitnessPorts`

When requested, `WitnessPorts` compares:

- the complete multiplicity-expanded relation witness occurrence domain;
- the binding's total injective witness map and exact image required by the
  question;
- target roles restricted to private Prover input occurrences or exact
  prover-obligation output ordinals;
- exact relation/Protocol bridge domains, ABIs, dependency views, and both
  round trips; and
- the abstract Protocol prover-obligation declarations and occurrence roles.

The clause is affirmative only when the witness-map image equals the complete
declared witness surface: every and only private Prover input occurrence and
every exact prover-obligation output ordinal is covered exactly once. A strict
subset is a valid binding proposal but a negative answer to this clause;
illegal, duplicate, or wrong-domain targets cannot enter through binding
admission.

The checker never reads a `PrivateWitnessAssignment`, secret value,
construction trace, provider, or runtime prover output. An affirmative result
is structural witness-interface agreement, not witness possession or
satisfaction.

### 4.4 `ResultBindingReferenceShape`

This clause has one deliberately narrow, directly recomputable meaning:

~~~text
ClaimPresence(claim)
  -> claim is in range and is produced

CheckTrue(check)
  -> check is in range, invoked, and Boolean-valued

AcceptingTerminals(terminals)
  -> terminals is nonempty and duplicate-free, every member is in range,
     and every member has static result Accept
~~~

The checker retains the admitted relation result role as an operand fact but
does not compare its `output_domain` or `accepted_values` with the Protocol
constructor. It does not establish that relation acceptance and Protocol
acceptance coincide, nor that a terminal subset is exhaustive for relation
acceptance. That stronger result is unavailable until a later owner supplies
an exact relation-result semantics and checked behavioral-equivalence
capability.

### 4.5 `CommittedObjectGrounding`

This clause reads only the exact checked grounding prerequisite. The
underlying binding entry remains identity-bearing context, but a declaration,
adapter, material digest, Interface-position reference, or raw observation is
not grounding authority.

An affirmative prerequisite supports the clause for every relation committed-
object occurrence. A negative prerequisite makes the clause negative and
retains its exact unaffected agreements. The structural correspondence check
does not widen grounding to Protocol objects outside the relation-total map,
infer inverse injectivity, prove opening knowledge, or prove derivation
faithfulness beyond the checked equations.

### 4.6 Optional artifact question

When `artifact_question = Some(q)`, the checker reads only the exact
`CheckedArtifactInterfaceComparison` over `q`. An affirmative prerequisite
supports every requested artifact field. A negative prerequisite refutes its
conflicting fields and preserves unaffected agreements.

The optional artifact result does not establish a base clause, relation truth,
artifact provenance, or an unrequested field. Artifact interpretation remains
expectation-free; agreement exists only at this separate comparison boundary.

## 5. Exact read closure

### 5.1 Structural checker read set

| Source | Permitted reads |
|---|---|
| Protocol Relations view | Exact Protocol/Core identities and regimes; public `Statement` and private Prover port occurrences; prover-obligation outputs; object declarations; produced claims; invoked Boolean checks; Accept terminals; events and input ordinals needed by binding-owned Interface-position chains |
| Protocol Interface | Exact dependent IDs; canonical public-assignment domain; lossless statement binding; proof-trace positions; application bindings; and only the external position facts requested by the binding/question |
| Relation Interface | Definition ref; exact dependency and occurrence schemas; public/witness/object domains and multiplicities; accepted-result role retained as a nonbehavioral fact |
| Relation binding | Exact dependent IDs; public/witness maps; value-bridge specs and retained dependency views; committed-object entries; per-object artifact selectors; position chains; and closed result binding |
| Question and regime | Exact canonical base-clause set, optional nested artifact question, `CorrespondenceRegime`, and its declared assumptions/checker identity |
| Checked prerequisites | Exact same-subject grounding result iff grounding is requested; exact same-question artifact comparison iff the artifact question is present |

The read closure excludes private witness values, relation-instance public
values, Protocol execution traces, Plan internals, raw artifact bytes, raw
observations, unselected facts, caller labels, ambient registries, and any
unrequested clause. Supplying an otherwise valid extra capability does not
expand the read set; it is refused.

### 5.2 Adequacy

The Relations-purpose Protocol and Interface views must contain every source
fact required by the exact question and no authority to infer omitted facts.
View adequacy is checked before correspondence. If a requested fact is absent
from an otherwise exact owner view, the operation is `CannotAnswer`, not a
negative judgment and not permission to inspect the producer's carrier.

No view acquires a new semantic identity merely by attenuation. The completed
result retains the exact admitted source views so a consumer cannot widen it
to a larger Protocol, Interface, relation, binding, or question.

## 6. Structural result and capability

### 6.1 Completed A/N result

For a well-formed, supported, authorized invocation with complete named inputs,
the checker produces one total field result for every and only requested base
clause and, when present, every field in the nested artifact question.

- `Affirmative` means every requested field agrees.
- `Negative` names every refuted requested field and retains all unaffected
  agreements.

Either completed result atomically creates the exact
`RelationCheckedResultCoordinate<StructuralCorrespondence>` and mints the
opaque process-local `CheckedRelationCorrespondenceJudgment` capability. It
retains:

- the exact admitted Protocol, Protocol Interface, relation Interface, and
  binding views;
- the exact `CorrespondenceQuestion` and `CorrespondenceRegime`;
- the exact named consumer and
  `RelationsOperationPurpose<StructuralCorrespondence>`;
- the exact `RelationsCorrespondenceCapabilityContractId` and
  `RelationsCorrespondenceCapabilityAbiId` declaring the no-owner-operation-
  policy disposition;
- the complete `ExactSourceAuthorityBinding`, including its exact
  `OwnerCapabilityRequirement` and canonical total transitive source-policy
  closure over every direct or transitive admitted-subject and checked-result
  source binding;
- the exact conditionally required checked prerequisites;
- the field-factored A/N result;
- the checker identity and complete dependency/read closure; and
- the qualified residual-trust basis.

The result coordinate is the domain-separated portable record ID only when its
complete preimage is portable, the correspondence contract permits completed-
result creation, portable stable identity, retention, and disclosure for the
exact family, named consumer, and typed purpose, and every disposition in the
complete transitive source-policy closure permits that construction and
retention. Otherwise, if the same contract and source closure permit an owner-
local completed result, it is the typed owner-local premise-record reference; a
denial prevents `Completed` entirely. Attempt-audit permission cannot substitute
for either branch. Serialized result bytes carry no live authority and cannot
be widened across operands, regimes, questions, or artifact field sets.

### 6.2 Non-completed outcomes

~~~text
Unsupported(exact unsupported question or dependency)
CannotAnswer(missing named semantic input or view fact, or an absent or
  mismatched required checked-result prerequisite)
Refused(missing live authority, prohibited invocation, or undeclared extra
  input or read)
Malformed(exact framing, question, assignment, or reference defect)
CheckerFailure(operational failure with no semantic conclusion)
~~~

U/C/R/M/F mint no checked capability and are never negative correspondence.
A prerequisite negative is different: it is a completed semantic result and
therefore makes the exact requested field negative.
A mismatched live admission, checker, or execution capability is missing
authority and therefore refused; only the required checked-result prerequisite
uses the `CannotAnswer` rule above.

### 6.3 Affirmative-only authority

Only an affirmative structural capability may feed an affirmative-only
consumer. A negative capability retains exact refutation facts for a consumer
that explicitly requests them, but it cannot authorize instance
correspondence. Neither A nor N establishes an unrequested field.

## 7. Public-instance correspondence

### 7.1 Signature

~~~text
RelationInstanceCorrespondsAtInterface(
  affirmative CheckedRelationCorrespondenceJudgment
    whose exact CorrespondenceQuestion.base_clauses contains PublicPorts,
  AdmittedProtocolInterface,
  AdmittedRelationBinding,
  AdmittedRelationInstance,
  ProtocolPublicAssignment<the exact dependent ProtocolId>,
  exact admitted value-bridge dependency views attenuated from the binding,
  ExactRelationValueBridgeExecutionCapabilities,
  exact ExactSourceAuthorityBinding for the structural result, every admitted
    semantic operand, and every authority-bearing attenuated value-bridge
    dependency view, with separately supplied fresh capabilities,
  exact named_consumer: NamedConsumer,
  exact operation_purpose:
    RelationsOperationPurpose<InstanceCorrespondence>,
  CorrespondenceRegime)
  -> Qualified<CheckedInstanceCorrespondenceJudgment,
               exact ExactCheckedResultAuthorityBinding<Relations,
                 InstanceCorrespondence>>
~~~

The structural capability must be affirmative, must select `PublicPorts`, and
must retain the identical Protocol, Interface, relation Interface, binding,
and regime. An affirmative result whose question omitted `PublicPorts` cannot
be widened.
Every exact source binding must match its fresh capability. The instance result
retains the canonical total transitive source-policy closure over the
structural result, all admitted semantic operands, and every authority-bearing
attenuated dependency view, and the checker freshly validates every disposition
for the named instance-correspondence purpose. It separately reauthenticates the
regime-bound correspondence contract and ABI and requires exact invocation and
capability-use permission for `InstanceCorrespondence`, the named consumer, and
the typed purpose.

`ProtocolPublicAssignment<P>` is the pure semantic result of successful
Interface statement decoding. It contains one same-domain value for every and
only public input `Statement` occurrence of that exact Protocol. Partial,
extra-key, wrong-Protocol, wrong-occurrence, or wrong-domain maps are malformed.
It is not an invocation, deployment, or capability.

### 7.2 Exact value comparison

The checker requires identity agreement among the structural capability,
Interface, binding, relation Interface, instance, assignment Protocol, and
`CorrespondenceRegime`. For every relation public occurrence it:

1. reads the canonical relation value from the admitted instance;
2. resolves the exact occurrence target in the admitted binding;
3. executes the binding-owned `to_protocol` bridge through an
   identity-and-ABI-matched `ExactRelationValueBridgeExecutionCapabilities`
   entry and retained dependency view;
4. reads the same target value from the decoded
   `ProtocolPublicAssignment<P>`; and
5. compares the two canonical Protocol-domain values.

No raw-byte, unqualified-value, or mnemonic equality is used. A binding law
checker is not retained as executable bridge authority. The operation does not
decode a second statement container, execute the Protocol or verifier, inspect
a witness, or derive a post-statement value.

### 7.3 Instance read closure and result

The instance checker reads every and only the affirmative structural
capability, the dependent Interface assignment domain, the binding's public
occurrence map and retained `to_protocol` bridge views, the admitted
instance's public values, the exact `ProtocolPublicAssignment<P>`, the matching
bridge-execution capabilities, and `CorrespondenceRegime`. It reads no private
witness, raw statement or artifact bytes, Protocol trace, verifier state,
Plan, grounding entry, or unrequested structural field, and it does not
execute `to_relation`.

A completed affirmative result records equality at every relation public
occurrence after exact bridge conversion. A completed negative names every
value mismatch and retains all unaffected agreements. Either A/N result mints
`CheckedInstanceCorrespondenceJudgment` together with the exact
`RelationCheckedResultCoordinate<InstanceCorrespondence>`, retaining the exact
structural source binding and separately supplied capability, Interface,
binding, instance, dependent assignment, bridge
dependency/execution basis, regime, checker identity, read closure, and
field-factored result, together with its qualified residual-trust basis and the
exact `RelationsCorrespondenceCapabilityContractId` and
`RelationsCorrespondenceCapabilityAbiId` declaring the no-owner-operation-
policy disposition, exact named consumer, and exact
`RelationsOperationPurpose<InstanceCorrespondence>`.
It also retains the complete `ExactSourceAuthorityBinding`, including the exact
`OwnerCapabilityRequirement` and transitive source-policy closure.

It records the exact bridge contract identities and ABIs but retains no live
bridge-execution capability.

U/C/R/M/F mint neither a result coordinate nor checked capability. The result is scoped to this one exact
assignment and cannot be reused for another invocation, Interface, codec,
binding, instance, bridge, or regime.

The portable/local result-coordinate and completed-result authorization rule is
identical to structural correspondence. Serialized result bytes convey no live
authority.

## 8. Authentication, checking, and replay

Correspondence never authenticates or admits its operands implicitly. Every
operand must arrive through its owner lifecycle. A source ID, stored
capability, normalization audit, package-membership proof, or producer report
is insufficient.

### 8.1 Structural cold replay

Exact cold replay exists only when the complete source-binding and structural-
result-binding preimages are portable. Under that condition, a new process
must:

1. reconstruct and re-admit the exact Protocol and its Relations-purpose view;
2. reauthenticate and re-admit the exact Protocol Interface;
3. reauthenticate and re-admit the exact relation Interface and binding,
   including every bridge/grounding dependency and conditional adapter view;
4. reconstruct the exact named consumer,
   `RelationsOperationPurpose<StructuralCorrespondence>`,
   `CorrespondenceQuestion`, and `CorrespondenceRegime`, including the regime's
   exact authenticated
   `RelationsCorrespondenceCapabilityContractId`, exact
   `RelationsCorrespondenceCapabilityAbiId`, and explicit no-policy declaration;
   reauthenticate both preimages and require their invocation, capability-use,
   completed-result-record, and replay rules to permit this exact family,
   consumer, and purpose;
5. iff requested, rerun artifact interpretation/admission and exact
   artifact/interface comparison over the same nested question;
6. iff requested, rerun committed-object grounding with the exact conditional
   observation map and execution capabilities; and
7. reauthenticate every disposition in the complete transitive source-policy
   closure and require it to permit reconstruction, result-record creation, and
   retention for the identical use; then rerun
   `RelationCorrespondsAtInterface`, recreate the exact portable source binding
   and result record, require complete equality with the recorded binding, and
   mint a fresh A/N capability.

Replaying a negative prerequisite preserves its exact refutation role. It does
not become missing authority or an affirmative result. Prior result bytes may
be compared diagnostically but never authorize the new check.

If any identity-bearing structural source or the structural result coordinate
is owner-local, exact cold replay is impossible. An authorized local rerun must
obtain fresh owner-local source references and matching capabilities, rerun the
same check, and create a fresh structural premise-record reference, downstream
local handles where applicable, and complete checked-result binding. None is
equal to or authorized by the prior local reference, binding, capability, or
serialized result.

### 8.2 Instance cold replay

When the structural result and every additional instance source are portable,
instance replay additionally must:

1. first recreate an affirmative structural capability whose exact question
   contains `PublicPorts`;
2. reauthenticate and re-admit the exact relation instance;
3. reconstruct the exact `ProtocolPublicAssignment<P>` through the admitted
   Interface's successful statement-decoding semantics or supply its exact
   already typed semantic preimage;
4. reconstruct fresh matching bridge execution capabilities; and
5. reconstruct the exact instance named consumer and
   `RelationsOperationPurpose<InstanceCorrespondence>`, rerun every bridge
   conversion and canonical value comparison, recreate the exact portable
   instance source binding, and require complete binding equality before
   minting a fresh capability.

Instance replay also reauthenticates the identical correspondence capability
contract and ABI retained by the recreated structural and instance
capabilities; requires their invocation, capability-use, completed-result-
record, and replay rules for the exact family, consumer, and purpose; and
reauthenticates every source-policy disposition before recreating either result
coordinate. Attempt-audit permission is irrelevant to this replay gate.

If the structural prerequisite, any additional identity-bearing instance
source, or the instance result coordinate is owner-local, exact instance cold
replay is impossible. An authorized local rerun creates fresh affected source
references, structural and instance premise-record references, downstream local
handles, complete checked-result bindings, and live capabilities. Matching old
bytes or fields neither restores the prior local coordinates nor grants
authority.

A serialized assignment or checked result conveys no authority. If external
bytes are used to reconstruct the assignment, the Interface decoder must be
reestablished independently; correspondence does not absorb byte-decoding
authority.

## 9. Consumer seams

### 9.1 Analysis

The [Analysis domain](../analysis/README.md) may consume a checked structural
or instance result only when its question names the identical operands,
`CorrespondenceQuestion`, nested artifact field set, assignment where
applicable, regime, model, and assumptions. Analysis may use an affirmative as
an exact premise or a negative as an exact refutation fact. It may not:

- widen the result to an unrequested clause or field;
- turn `ResultBindingReferenceShape` into acceptance equivalence;
- infer satisfaction, soundness, completeness, knowledge, zero knowledge, or
  another property without a separately owned judgment; or
- treat checker execution or an observation as evidence of a broader claim.

The exact source binding and separately supplied checked correspondence
capability supply a bounded semantic premise, not a theorem or evidence
appraisal. Analysis retains the binding's exact result coordinate, origin,
capability requirement, capability-contract identity, and capability ABI and
binds the explicit
`OwnerDefinesNoOperationPolicy(RelationsCorrespondenceCapabilityContractId,
RelationsCorrespondenceCapabilityAbiId)` disposition; it never infers no policy
from absence.

### 9.2 OIR

The [OIR domain](../oir/README.md) owns projection, occurrence placement,
endpoint behavior, and `LocalOirValid`. Correspondence may supply exact
relation-facing facts to an explicitly named OIR transition, but it does not:

- create an OIR;
- place an Interface output on a path;
- classify a Plan or prove prover realization;
- establish endpoint support or verifier execution; or
- imply `LocalOirValid`, projection coverage, or recursive realization.

OIR may consume an admitted relation Interface or affirmative correspondence
only through a future transition that takes the exact source value plus its
complete `ExactAdmittedSubjectAuthorityBinding` or
`ExactCheckedResultAuthorityBinding`, including the inert
`OwnerCapabilityRequirement`, authenticated `OwnerOperationPolicyDisposition`,
and canonical total transitive source-policy closure; receives the separately
fresh binding-matched capability; and fixes an exact OIR `NamedConsumer` and
typed operation purpose. The transition must freshly authorize every `BoundTo`
policy and every explicit no-policy contract/ABI branch for that exact use. A
source ID, capability name, or declared read set is insufficient. Stage 4A does
not activate this transition or select its OIR-owned purpose, operation
contract, result, or admission rule. Nothing flows backward into Protocol,
Interface, relation, binding, or correspondence identity.

## 10. Nonclaims

Neither structural nor instance correspondence establishes:

- relation-definition truth, satisfiability, or faithful formalization;
- public-instance truth independently of the exact bridge-converted equality;
- witness existence, possession, validity, secrecy, or satisfaction;
- equivalence of relation acceptance and Protocol acceptance;
- Protocol admission, verifier execution, proof production, termination, or
  transcript behavior;
- artifact provenance, parser correctness beyond its named contract, or
  agreement on an unrequested artifact field;
- committed-object derivation faithfulness beyond the checked contract
  equations, inverse injectivity, or opening knowledge;
- soundness, completeness, knowledge, zero knowledge, Fiat--Shamir security,
  or another cryptographic property;
- compiler preservation, OIR validity, endpoint support, realization, or
  evidence sufficiency; or
- implementation correspondence, migration safety, compatibility, or
  production readiness.

`RelationSatisfies` remains a separate Relations-owned operation over the
external definition, exact admitted semantic model and instance,
occurrence-local private witness, assumptions, and exact checking basis, as
defined by the sibling [Relation model](relation-model.md). No correspondence
capability may be substituted for it.

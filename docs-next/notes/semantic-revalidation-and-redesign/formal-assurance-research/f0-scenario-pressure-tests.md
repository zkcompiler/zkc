# F0 Scenario and Counterexample Pressure Tests

> **Kind:** Temporary falsification dossier
> **State:** Paper execution complete for the first architecture pass; machine
> mutations and F1 implementation remain open
> **Authority:** None. “Required refusal” below is a proposed checker contract,
> not a claim that the current implementation performs the check.

## 1. Test method

Each case asks four separate questions:

1. Does the selected target own the needed source fact?
2. Can an exact owner read manifest force the fact into the source closure?
3. Can a portable package preserve the fact without becoming a second owner?
4. Can a provider adapter and theorem state the same observation and
   quantifiers?

Passing the first three questions establishes only reification feasibility.
Passing the fourth establishes only a candidate correspondence. Property truth
and compiler/endpoint transport remain later judgments.

## 2. Case S1 — bounded relation-bound Schnorr

### Required source

- one exact Fresh Protocol/Core and occurrence order;
- public statement and private-witness relation roles;
- commitment message, public challenge, response message, and verifier check;
- challenge domain/law and independence/correlation declaration;
- accepted/rejected terminal routes;
- relation definition/model correspondence; and
- when modeling an honest prover, exact strategy and Plan witness roles.

### Mutation set

| Mutation | Theorem-relevant change | Required result |
|---|---|---|
| omit the response producer coordinate | the verifier equation reads an ungrounded value | package formation or correspondence refuses missing dependency |
| swap statement and witness relation roles | changes public quantification and witness secrecy | relation correspondence is Negative/Refused according to formedness; never accepted by type resemblance |
| replace Fresh challenge with an equal constant | destroys public-coin sampling | Protocol ID/profile and challenge interpretation disagree; refuse |
| omit Reject terminal | changes completed behavior | source-read closure or total observation map fails |
| use a replay-qualified trace to establish honest nonanticipation | provenance premise is absent | `CannotAnswer` or `Refused`; replay match cannot mint causal authority |

### Result

The current target exposes every static fact through PIR and Relations views.
Plan remains conditional: it is needed for a theorem about the selected honest
prover, not for the bare verifier relation or an adversarial soundness
experiment. This case supports Candidate A and gives F1 a tractable positive
fixture, but it does not discriminate a local P adapter from a portable S
package.

F2-P now pins VCVio's concrete `Schnorr.sigma_complete` theorem for this case.
That makes perfect completeness with acceptance probability `1` the exact
property target, but does not pre-establish the required zkc-to-VCVio
correspondence or applicability map.

## 3. Case S2 — standard sequential RandomQuery or Sumcheck

### Required source

- exact reduction occurrence and contract;
- ordered input/output claims and side inputs;
- required challenge occurrences and domains;
- publication and next-challenge requirements;
- relation instance/model roles; and
- exact experiment, adversary, resource, and quantitative-loss coordinates.

### ArkLib comparison

A strict sequential case may map naturally to an ArkLib `OracleReduction` or
`OracleVerifier` subject. Applicability still requires exact maps for input and
output statements/witnesses, Oracle statements, prover/verifier algorithms,
challenge schedule, and security notion. An ArkLib declaration's printed type
and axiom set are theorem-environment evidence, not these maps.

### Mutation set

| Mutation | Required result |
|---|---|
| drop `required_publications.next_challenge` | package checker refuses incomplete reduction/publication closure |
| reverse two claim outputs that share a type | exact ordered map disagreement; shape equality is insufficient |
| apply a completeness theorem to a soundness proposition | theorem-applicability refusal by property/quantifier mismatch |
| use the old ArkLib environment ID with a refreshed dependency lock | validation-basis/environment mismatch |
| report a theorem hole as a target-property counterexample | malformed or checker failure; proof incompleteness has no property polarity |

### Result

The case favors a partial ArkLib adapter layered above the provider-neutral
source package. It rejects the idea that current `covers` text can become a
checked adapter through more detailed prose. It also supports separating
theorem truth from applicability: a fully proved theorem can be inapplicable,
and an exactly applicable statement can remain proof-incomplete.

## 4. Case S3 — interleaved reductions with one shared challenge

Consider a schedule of the form:

```text
A.message_1
B.message_1
joint_challenge
A.message_2
B.message_2
A.check
B.check
terminal
```

The one challenge occurrence is declared `Shared` and both reductions name it
under the exact sharing/correlation contract.

### Critical observations

- occurrence order is one global sequence, not `A` followed by `B`;
- the challenge is one draw with one identity, not two equal draws;
- both required-challenge backlinks and reduction-use coordinates are visible;
- transcript prefix and public conditions are those before the one draw;
- failure or inactivity of a guarded branch must not fabricate a second
  challenge; and
- theorem quantifiers must cover the combined adversary/schedule.

### Mutation set

| Mutation | Why equal values do not save it | Required result |
|---|---|---|
| duplicate the shared challenge into `c_A` and `c_B` with equal sampled values | independence/correlation and rewinding experiments differ | source/package map is non-bijective or provider correspondence disagrees |
| serialize all A events before all B events | transcript prefixes and adversarial adaptivity differ | occurrence-order mismatch |
| retain one challenge but drop B's required-challenge backlink | B's theorem premises no longer name the draw | missing dependency/total-map failure |
| map to a strict alternating sequential-composition theorem | theorem subject and quantifier schedule differ | ArkLib adapter or applicability checker refuses |
| compare only terminal decisions | erases transcript and challenge observations | proposed relation is too weak and cannot satisfy the interpretation contract |

### Result

This is the first decisive discriminator. The selected target appears to own
the needed facts through `EffectView`, `PublicCoinView`,
`ClaimReductionView`, and `ExecutionView`; no Core redesign is indicated.
Candidate P can model it only if its adapter reads all four views correctly.
Candidate S makes omission and challenge duplication independently testable.
Candidate R can express the case, but gains no unique semantic capability that
justifies replacing the current center.

Current ArkLib high-level composition must be treated as partial here unless an
exact matching theorem subject is found. Direct VCVio interpretation is the
leading F2 path because the schedule can be represented as one typed oracle
computation rather than forced into a sequential-reduction ontology.

## 5. Case S4 — Fiat--Shamir runner, state, and failure

### Required source

- exact Fresh Core reused by one identified FS Protocol;
- exact transcript-construction ID/profile and family-specific views;
- visible-history and absorb/squeeze/resolver coordinates;
- codecs, domains, framing, retries or atomic transitions;
- challenge receipts and family-specific interpretation-failure schema;
- terminal/failure precedence; and
- the experiment's random-oracle, state-restoration, rewind, or QROM regime.

### Mutation set

| Mutation | Bug class | Required result |
|---|---|---|
| omit a public statement or domain-separation input from the absorbed prefix | weak binding / Frozen-Heart-style omitted context | package or provider correspondence fails exact transcript influence |
| absorb a message after squeezing the challenge that should depend on it | schedule/prefix bug | occurrence and transcript-state transition mismatch |
| merge two domain tags with equal bytes under one test fixture | typed framing collision | profile law/reference or typed transition mismatch; fixture equality is irrelevant |
| turn canonical framed sampling exhaustion into Reject | failure-lane collapse | execution correspondence fails: interpretation failure is not a Core terminal |
| turn deterministic evaluator-limit exhaustion into sampling failure | operational/semantic collapse | qualified-outcome mismatch |
| reuse a proof against a different construction profile with the same Core | environment/subject replay | Protocol, profile, package, and proposition IDs disagree |
| prove deterministic replay and infer cryptographic rewindability | replay-regime confusion | applicability refusal; PIR replay and crypto rewind are separate propositions |

### Result

The target's separation of Core from challenge interpretation is beneficial:
the formal subject must include the Protocol and construction views rather
than treating a challenge capability as a hash execution. The exact
family-specific failure schema prevents a generic transcript model from
silently inventing or erasing failures.

The case also shows why “formally verify the verifier” is insufficient by
itself. A verifier implementation theorem can preserve the written endpoint
while the theorem's source semantics omits an absorbed field, uses the wrong
random-oracle experiment, or applies an FS theorem with mismatched quantifiers.
The source/transcript/game correspondence is a prior obligation.

## 6. Case S5 — Oracle commitment extent

### Required distinction

An Oracle declaration may expose a public binding, logical access, or another
exact mode. Publicly fixing selected values does not necessarily commit an
entire mathematical carrier. A theorem about a committed polynomial/table or
about adaptive query consistency needs the exact Oracle origin, lifecycle,
mode, publication, query/answer visibility, and commitment premise.

### Mutation set

| Mutation | Required result |
|---|---|
| map `LogicalAccess` to a fully committed immutable table | provider correspondence or theorem applicability refuses missing commitment premise |
| omit an adaptive query from a run view | run-manifest completeness fails |
| replay public answers without the required confidential Oracle witness | `CannotAnswer`/refusal, never causal or full-carrier affirmation |
| treat an inactive Oracle branch as missing evidence | run-status mismatch; `Inactive` is a semantic fact |

### Result

The target owns the declaration and run facts, but the theorem may need a
separate commitment construction or assumption that the Protocol does not
provide. This is an honest support/applicability gap, not a reason to strengthen
Oracle meaning globally. A formal package must preserve the weaker exact mode
and let the theorem refuse.

## 7. Case S6 — property-specific compiler transition

Take an untrusted rewrite that preserves types, checks, messages, and terminal
decisions on the existing fixtures but changes one challenge from `Shared` to
two `Independent` draws.

### Candidate relations

| Relation checked | Expected outcome |
|---|---|
| target PIR admission | may be Affirmative: both source and target can be valid Protocols |
| structural event-shape equality | may be Affirmative under an intentionally weak shape observer |
| terminal-decision equality on fixtures | bounded Evidence only |
| exact schedule/challenge-correlation preservation | Negative with a concrete mismatch |
| source soundness property transport | cannot proceed without a theorem for the changed experiment or an exact refinement result |

### Result

No generic `equivalent` bit is adequate. `TransformIntent` must name the
observer, relation direction, protected observations, maps, and permitted
deltas. The practical architecture is untrusted transformation plus a small
property-specific validator/certificate checker. A CompCert-style universal
pass proof may later replace repeated validation for a stable pass, but it is
not required to detect this bug.

## 8. Case S7 — future OIR/backend boundary

Even an affirmative static Protocol-to-VCVio correspondence and a proved
cryptographic theorem leave these edges open:

```text
Protocol -> OIR projection -> backend artifact -> deployed invocation
```

The target already reserves projection/conformance tiers and a target-specific
`RealizesOir` check. A source package can supply stable input to such a checker,
and proof-carrying output may help, but no F0 package should claim endpoint
coverage before OIR/Realization activation.

This case rejects Candidate R's superficial end-to-end advantage: a formal
source center still needs verified or validated projection, lowering,
cryptographic primitive, ABI, assembler/linker, and deployment boundaries.

## 9. Cross-case falsifier table

| Falsifier | Existing target defense | Missing F1/F2 mechanism |
|---|---|---|
| omitted source field | owner-defined manifest fixed point and exact realized-read equality | portable package checker and mutation corpus |
| phantom or extra read | exact manifest equality and closed field coordinates | package decoder/checker |
| equal-value aliasing | typed references, occurrence IDs, producer coordinates, profile IDs | total source-to-formal coordinate map |
| shared challenge duplicated | exact challenge occurrence, correlation, reduction-use backlinks | provider adapter correspondence theorem/check |
| schedule reordered | exact occurrence schedule and execution law | formal trace/step relation |
| failure collapsed into Reject | typed terminals, interpretation failure, strategy stop, and qualified noncompletion | provider result-algebra correspondence |
| replay presented as causality | nonserializable causal capability and explicit run qualification | Analysis proposition that requires the exact capability |
| theorem applied by shape | separate theorem-applicability question and support | instantiated provider maps and checker |
| proof replayed under another pin/profile | profile, package, validation-basis, theorem-source, and support identities | complete environment/package identity implementation |
| transform preserves fixtures but not property | separate target admission, transition, property transport, and Evidence | one property-specific transition validator |

## 10. Candidate outcome after paper execution

- **P:** passes S1/S2 as a disposable local prototype but fails the independent
  replay and shared-source requirements across providers.
- **A:** passes source selection and authority locality in every case examined.
- **S:** is justified by the independent consumer and makes the decisive S3/S4
  mutations portable; it remains acceptable only as a question-relative
  source package.
- **C:** is the preferred production discipline for S3/S4/S6, but depends on A
  and S for proposition and source meaning.
- **R:** can model the cases but does not remove downstream correspondence and
  has no demonstrated capability advantage large enough to justify its
  authority and migration cost.

The A/S/C convergence survives this first pressure test. The two most
important machine falsifiers for F1 are:

1. duplicate one shared challenge into two equal provider draws; and
2. omit one FS transcript input while preserving every terminal fixture.

If either mutation passes the proposed package/correspondence checker, F0's
architecture or observation contract is wrong.

## 11. Non-claims

These cases were executed against the written target on paper. No package,
checker, VCVio model, ArkLib adapter, mutation runner, or compiler validator was
implemented or run. Existing target defenses describe specified source
structure, not current C++ implementation of the new formal bridge.

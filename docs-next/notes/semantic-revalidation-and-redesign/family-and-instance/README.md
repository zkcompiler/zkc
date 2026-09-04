# Protocol families and their finite instances

**Status:** bounded research recommendation; no design is adopted and no owner
page is changed.

## Question and answer

How should a theorem stated for a protocol family relate to the one finite,
explicit schedule authenticated by a PIR Core?

The evidence supports **Design A, instances only**: keep PIR Core finite and
exact; let a front end or Compiler transition emit one admitted Core per
parameter value; let Analysis bind one family theorem once and specialize it to
each concrete Core through an exact family/member correspondence judgment.
The executable aggregate is
`Affirmative/FAMILYINSTANCE-A-INSTANCES-OUTSIDE-CORE`.

This is a recommendation about owner placement and evidence cost. It is not a
theorem, a family-wide generator proof, an adoption decision, or a change to
the target architecture.

## Evidence boundary

The current PIR source fixes these facts:

- `InteractiveCore` is a finite collection with one nonempty exact occurrence
  schedule; its `CoreId` authenticates the Interaction profile and exact Core
  body ([interactive-core.md, Section 3.2](../../../pir/interactive-core.md)).
- static parameters belong in the Core or construction body, while runtime
  public parameters are explicit public bindings
  ([interactive-core.md, Section 4.3](../../../pir/interactive-core.md)).
- finite recurrence is unrolled before authentication, and symbolic recurrence
  is a reopening pressure only when finite lowering is infeasible or
  semantically lossy
  ([interactive-core.md, Sections 14 and 15](../../../pir/interactive-core.md)).
- Fiat--Shamir changes challenge interpretation while retaining the same exact
  Core; theorem applicability remains outside PIR
  ([fiat-shamir.md, Sections 1--3 and 9](../../../pir/fiat-shamir.md)).
- Relations binds exact Protocol and relation identities; it neither invents a
  generic protocol object nor establishes satisfaction
  ([relation-model.md, Sections 1--4 and 7](../../../relations/relation-model.md)).
- Analysis already has distinct family applicability, concrete family/member
  correspondence, and pointwise specialization boundaries
  ([cryptographic-properties.md, Sections 4, 7, and 8](../../../analysis/cryptographic-properties.md)).

The executable reuses the retained indexed authoring grammar rather than
introducing a second generator. That grammar unfolds finite FRI-like and
sumcheck-like programs and delegates every result to the unchanged retained
fixture's Core admission and identity routines. That carrier expressly does not model
the target's complete `PCNode`/module graph, first-class reduction effects, or
claim semantics. Accordingly, target graph equivalence remains
`CannotAnswer`; only the fixture-representable graph counts are affirmative.

## The three designs

### Design A — instances only

Exact statement: PIR continues to admit only finite concrete Cores. A generator
outside PIR—either a front end or an exact Compiler transition—takes a family
description and parameter value and emits one candidate Core. The ordinary PIR
path authenticates and admits that Core. Analysis binds a family theorem to the
family definition once, then carries an instance-indexed premise relating each
logical family member to the exact Core, Protocol, Relations, and experiment
coordinates used by the concrete judgment.

Parameter identity is not ambient metadata. If changing the parameter changes
any identity-bearing body field, it changes `CoreId`, then every `ProtocolId`
formed over that Core and every exact downstream subject that includes those
identities. The generator or family-definition identity can remain stable. If
two parameter values intentionally elaborate to the same exact Core body, PIR
gives them the same Core identity; Analysis must distinguish their logical
indices in the family/member premise rather than ask PIR to distinguish equal
semantics.

Admission cost is generation outside PIR plus ordinary authentication and full
finite Core admission per member. A checked Compiler route may additionally
prove or test the exact source-to-Core transition. Nothing amortizes the Core
admission predicate across members.

The theorem binds to one Analysis family definition, family read manifests,
experiment profiles, role/parameter maps, side conditions, and quantitative
transform. Each member specialization additionally binds the logical parameter
literal to exact native subject identities and correspondence premises.

A verifier-derived query plan and an endpoint contract see the admitted Core or
Protocol and its fully unfolded schedule, query, effect, claim, reduction, and
terminal coordinates. They do not see the external generator or logical family
index unless their own exact source contract deliberately includes a separate
Analysis or Compiler result.

No Section 15 Core reopening condition is triggered by the six measured
members. If an actual family later shows that symbolic recurrence cannot be
lowered finitely without infeasibility or semantic loss, the seventh reopening
condition is the exact route back to this decision. If the loss concerns an
acceptance-relevant effect whose transition, visibility, influence, replay, or
bounds cannot be stated, the eighth condition also applies.

### Design B — a template Core inside PIR

Exact statement: PIR gains a bounded parametric Core constructor, an admitted
parameter domain, and a total admission-time unfolding law. A member is usable
only after the law unfolds the template at one parameter into an ordinary
finite Core and that result passes concrete Core admission.

The template identity can remain stable while the parameter changes, but every
distinct unfolded Core body has a distinct `CoreId`, with the same downstream
rotations as Design A. Adding the constructor, parameter language, totality and
boundedness checks, and unfolding semantics changes the Interaction kernel and
therefore rotates the Interaction profile. Because the current `CoreId`
directly selects that profile, even unchanged old Core bodies acquire new typed
identities under a replacement Interaction profile.

Admission now has two layers: authenticate and admit the template plus its
bounded parameter domain and unfolding law, then unfold and admit each concrete
Core. An all-parameter claim requires evidence that the law is total, bounded,
and semantics-preserving on the whole admitted domain; checking only selected
members does not supply that evidence.

The family theorem binds to the same Analysis family coordinates as Design A,
plus the exact template identity, parameter domain, and unfolding law. Each
member still needs `Unfold(template, parameter) = CoreId` and the ordinary
family/member correspondence to Protocol and Relations coordinates. Template
admission does not establish theorem applicability or the mathematical family
denotation.

After unfolding, verifier-derived query plans and endpoint contracts see the
same exact finite Core as in Design A. If template identity is intended to be
visible downstream, the query-plan or endpoint source contracts must add it as
an identity-bearing coordinate; that is an additional downstream rotation, not
an automatic consequence of unfolding.

Regular finite repetition does not itself trigger any Section 15 reopening
condition. This design becomes responsive to the seventh condition only after
evidence shows that external finite lowering is infeasible or semantically
lossy. No such evidence exists in the measured fibers, so necessity of an
internal template is
`CannotAnswer/FAMILYINSTANCE-C-TEMPLATE-NECESSITY`.

### Design C — a family as a semantic profile

Exact statement: a parametrized semantic profile owns a family description and
an unfolding law; importing one member fixes the parameter and yields one
ordinary finite Core, without adding a Core constructor.

There are two materially different attachment choices, and the proposed design
does not select one:

1. A companion profile outside Core can authenticate the family description,
   fixed parameter, and unfolding law. Parameter changes rotate that profile or
   member identity and normally rotate the unfolded `CoreId` through changed
   Core body bytes. The current query-plan and endpoint contracts see only the
   unfolded Core/Protocol, not the companion profile.
2. If the family profile is meant to select Core semantics, the current Core
   identity law must change. `interactive-core.md` Section 3.2, lines 387--392,
   hardwires `PIRInteractionProfileId`; Sections 2 and 3, lines 296--355, require
   one exact selected root and exact import closure. A profile import alone is
   not a Core-body field and cannot silently alter Core meaning.

The first choice leaves PIR unchanged but duplicates the role already assigned
to an Analysis family definition or an external typed generator profile. The
second avoids a new body constructor but still changes Interaction profile
selection and rotates Core identities and dependent consumers. The attachment
is therefore
`CannotAnswer/FAMILYINSTANCE-C-PROFILE-ATTACHMENT` at the exact sections above.

Admission for the companion choice consists of profile publication and closure
authentication, parameter-fixing import validation, unfolding, and ordinary
Core admission per member. The Core-selecting choice additionally needs a new
Core profile-selection and evaluator-dispatch law. Neither choice removes the
pointwise Analysis correspondence.

The theorem binds to the same family-wide Analysis record plus the exact family
profile, selected parameter import, and unfolding equality for each member. A
query plan or endpoint contract sees the profile only if its owner explicitly
adds that source coordinate; otherwise it sees the unfolded finite Core just as
in Designs A and B.

The companion choice triggers no Core reopening condition. The Core-selecting
choice is an Interaction identity change, but none of Section 15's listed
pressure observations has been demonstrated by these regular finite instances.
As with Design B, only infeasible/lossy finite lowering or an inexpressible
acceptance-relevant effect would supply the relevant seventh or eighth
condition.

## Side-by-side consequences

| Design | What changes with a parameter | Admission evidence | Family theorem binds to | Query-plan and endpoint view | Section 15 pressure |
|---|---|---|---|---|---|
| Instances only | concrete Core body and identity, Protocol identity, exact dependents; generator/family identity may stay fixed | generate, authenticate, and fully admit every Core; optional checked Compiler transition | one family applicability record plus one logical-index-to-native-member correspondence per Core | fully unfolded Core/Protocol only | none in measured cases; reverse on condition 7, and condition 8 if effect semantics are lost |
| Template Core | template may stay fixed; unfolded Core and dependents rotate; adding the constructor rotates the Interaction profile and all profile-selected Core identities | template/domain/law admission plus unfold and full Core admission per member | family record plus template/domain/law and per-member unfolding equality and correspondence | unfolded Core unless template identity is explicitly added | condition 7 is the only measured-task-relevant justification, but it was not observed |
| Family semantic profile | companion/member profile rotates and unfolded Core normally rotates; Core-selected form also changes Interaction profile selection | profile publication/import, unfolding, and full Core admission; Core-selected form adds dispatch law | family record plus profile/import/law and per-member unfolding equality and correspondence | unfolded Core unless profile coordinate is explicitly added | none for companion form; conditions 7 or 8 only if future pressure demonstrates them |

## Executable measurements

The package
[`evaluation/family-instance-probe/`](../../../../evaluation/family-instance-probe/README.md)
measures three parameter values for each of two family shapes.

| Family shape | Parameter | Core body bytes | Core identity digest | Admission median in one run | Fixture graph nodes/edges | Declarations | Different declarations |
|---|---:|---:|---|---:|---:|---:|---:|
| FRI-like folding | folds `2` | 7,625 | `8c158862bb8e...38d0c` | 133,673 ns | 42 / 58 | 19 | 0 |
| FRI-like folding | folds `3` | 8,815 | `298ea61f2db1...9be61` | 148,674 ns | 48 / 67 | 21 | 5 |
| FRI-like folding | folds `4` | 10,005 | `332a7b9cb17f...3f269` | 168,355 ns | 54 / 76 | 23 | 5 |
| Sumcheck-like rounds | variables `1` | 4,190 | `aef62014b432...3cfef` | 76,062 ns | 24 / 31 | 12 | 0 |
| Sumcheck-like rounds | variables `2` | 7,003 | `7820272d0c8d...0c9c7` | 122,913 ns | 35 / 51 | 17 | 6 |
| Sumcheck-like rounds | variables `4` | 12,629 | `79ed21123a33...ffffd` | 208,206 ns | 57 / 91 | 27 | 11 |

Every timing is the median of 21 warm calls to the unchanged bare Core
admission routine. Exact times are reported on every run; the frozen finding is
the host-tolerant class at or below 250,000,000 ns per member.

For folds `r`, the measured body fields are exactly `schedule` and
`reductions`, with:

```text
body bytes = 5,245 + 1,190 r
fixture graph nodes = 30 + 6 r
fixture graph edges = 40 + 9 r
declarations = 15 + 2 r
```

An extra fold adds a challenge and an Oracle publication. It also changes the
single reduction's challenge/publication lists and the fixed query and answer
declarations' selected layer, for five differing declarations between each
adjacent measured member.

For variables `v`, the measured body fields are exactly `schedule`,
`reductions`, and `claim_uses`, with:

```text
body bytes = 1,377 + 2,813 v
fixture graph nodes = 13 + 11 v
fixture graph edges = 11 + 20 v
declarations = 7 + 5 v
```

Each variable contributes one message, challenge, check, reduction, and
reduction claim use. The terminal claim use changes too, so members separated
by `delta` variables have `5 * delta + 1` differing declarations.

This regularity is the exact finite law a template or unfolding rule would
need to reproduce for these fixtures. It is not evidence that the same affine
byte law survives multi-digit names, canonical-natural width changes, larger
domains, or all indices.

The target `PCGraph` count remains
`CannotAnswer/FAMILYINSTANCE-C-TARGET-PCGRAPH`. The exact missing measurement
is the same six members represented and admitted by the target Appendix-A Core
carrier, followed by the target Section 11 graph constructor, or a checked
correspondence showing that the fixture graph has exactly the same target
nodes and edges.

## Theorem binding: sumcheck family soundness

The selected theorem schema is the familiar conditional family statement:

```text
for every variable count v, degree bound d, and finite field F,
under the theorem's exact sumcheck, challenge-distribution, degree,
and verifier-correspondence premises,
soundness error <= d * v / |F|.
```

No theorem source or proof artifact is selected by this lane. The expression is
used only to expose where the family parameter occurs.

### Family-wide applicability coordinates

One theorem-applicability judgment carries:

- exact `theorem_schema_id` and `family_definition_id`;
- source and target family read-manifest schema IDs;
- source and target family experiment-profile IDs;
- exact source/target provider subjects and semantic role maps;
- exact quantifier and local binding substitution for `v`, `d`, and `|F|`;
- side-condition schemas for finite-field cardinality, degree bounds, public
  independent challenge sampling, verifier/acceptance correspondence, and
  required resource measures;
- the typed quantitative transform whose conclusion is
  `d * v / |F|`;
- the complete hypothesis-context ID; and
- exact support-instantiation and validation-basis IDs.

Here `v` remains a quantified logical family coordinate. It is not a field of
one finite Core.

### Pointwise member coordinates

Specializing that family result to one executable member carries:

- the same `family_definition_id`;
- an authenticated logical-natural literal for this exact `v`;
- the concrete `CoreId` and `ProtocolId`;
- exact relation instance and protocol/relation binding IDs;
- statement, witness, verifier, acceptance, challenge-model, and resource-role
  coordinates;
- a checked map requiring `CoreRoundCount = v` and binding the native degree
  limit and field cardinality to `d` and `|F|`;
- every retained conditional premise needed by those maps; and
- the exact family/member correspondence judgment ID consumed by pointwise
  specialization.

Changing `v` changes the logical literal and, in the measured instances, the
Core/Protocol and dependent relation coordinates. It does not change the
theorem schema or require re-authoring its source.

### Design-specific additions

| Design | Additional coordinates beyond the common family and member records |
|---|---|
| Instances only | optional generator or Compiler-transition result proving that this parameter emitted this exact Core; no extra PIR family subject |
| Template Core | template identity, admitted parameter domain, total bounded unfolding law, and `Unfold(template, v) = CoreId` |
| Family semantic profile | family-profile ID, exact parameter-fixing import, unfolding-law coordinate, profile closure/dispatch as applicable, and resulting-Core equality |

The same theorem source can bind to all members under every design because the
public Analysis architecture already separates theorem environment and truth,
family applicability, pointwise correspondence, and member specialization.
Design A saves no theorem proof. It saves the additional template/profile
formation, totality, unfolding, profile-publication, and dispatch evidence that
Designs B and C introduce; all designs still pay for concrete correspondence.

## Recommendation and reversal condition

Retain the finite exact Core and place family authoring outside PIR. Reuse an
existing front-end or Compiler ownership boundary for the generator; use the
Analysis family definition, applicability, family/member correspondence, and
pointwise specialization sequence for theorem consumption. Do not add a PIR
template constructor or use semantic-profile publication as a parallel family
authority on the evidence currently available.

Reverse this recommendation and reopen the internal-template option only when
one named real protocol family supplies all of the following evidence:

1. at least one target Appendix-A member whose exact acceptance-relevant
   schedule cannot be finitely lowered by the external generator within the
   published bounds, or whose finite lowering loses a named dependency,
   transition, visibility, influence, replay, or bound coordinate;
2. the resulting failure is classified under Section 15's symbolic-recurrence
   or acceptance-relevant-effect condition rather than as front-end
   inconvenience;
3. a bounded internal template admits the same parameter domain with an
   authenticated total unfolding law; and
4. for at least three parameters, unfolding reproduces byte-identical concrete
   Core bodies, target `PCGraph`s, verifier-derived query plans, and endpoint
   contracts, while an all-domain argument accounts for parameters outside the
   finite sample.

The current probe measures none of the failure in item 1 and cannot supply the
all-domain evidence in item 4. That is why internal-template necessity remains
`CannotAnswer`, while the lower-authority-cost instances-only recommendation is
affirmative at bounded research resolution.

## Owner-page status

No owner-page change is proposed. The current Core and Analysis texts already
provide the selected ownership split. The unresolved family-profile attachment
and target-graph correspondence are recorded as `CannotAnswer` findings rather
than silently repaired here, so there is no Proposed delta block.

## Non-claims

This record proves no theorem and establishes no FRI or sumcheck soundness. It
does not prove generator correctness for a whole family, target graph
equivalence, admission complexity, query-plan correctness, endpoint
realization, Compiler correctness, implementation conformance, or security. It
does not adopt a design, publish a semantic profile, rotate any owner identity,
or authorize an owner-page edit. Six admitted fixtures and affine observations
are bounded evidence only.

## Handoff

Files changed:

- `docs-next/notes/semantic-revalidation-and-redesign/family-and-instance/README.md`
  records the evidence, three designs, theorem/member coordinates,
  recommendation, reversal condition, exact `CannotAnswer` boundaries, and
  this handoff;
- `evaluation/family-instance-probe/README.md`, `model.py`, `run.py`, and
  `expected-findings.json` define and freeze the executable package;
- `checks/manifest.json` registers `research.family-instance-probe`;
- `evaluation/lifecycle.json` retains it under
  `retained-bounded-instruments`;
- `evaluation/README.md` adds the package row; and
- `checks/tests/test_evaluation_lifecycle.py` advances the pins to 54 research
  checks, 56 packages, and 16 retained packages.

Final validation used a clone-local alternate index and clone-local alternate
Git object store because `.git/objects` is read-only. The index included every
file above. Commands and results:

- `python3 -B -m unittest checks.tests.test_evaluation_lifecycle` with the
  alternate index: exit `0`; four tests passed in `0.032s` (`0.044s` tool wall);
- `python3 -B checks/run.py validate` with the alternate index: exit `0`;
  manifest valid with 71 checks; `0.04s` wall;
- `UV_NO_SYNC=1 UV_OFFLINE=1 UV_CACHE_DIR=<clone-local-cache> python3 -B
  checks/run.py run --tier developer` with the alternate index: exit `0`;
  8 of 8 checks passed; `0.99s` wall; and
- `UV_NO_SYNC=1 UV_OFFLINE=1 UV_CACHE_DIR=<clone-local-cache> python3 -B
  checks/run.py run --check research.family-instance-probe` with the alternate
  index: exit `0`; 1 of 1 check passed in `0.337s`; `0.40s` wall.

The aggregate is
`Affirmative/FAMILYINSTANCE-A-INSTANCES-OUTSIDE-CORE`: for the six bounded
members, parameters elaborate to separately admitted finite Cores with distinct
identities and regular measured size changes, while the same family theorem
source can be reused through pointwise Analysis correspondence. Full target
graph equivalence, internal-template necessity, family-profile attachment,
theorem truth or soundness, and target adoption remain `CannotAnswer`.

Non-claims: no theorem was proved; no FRI or sumcheck soundness or other
security property was established; no all-index generator law, target graph
correspondence, implementation conformance, query-plan or endpoint correctness,
or admission complexity was established; and no design, profile, owner-page
change, staging action, commit, push, or pull request was adopted or performed.

Surprises and places where the brief did not match the live checkout:

- `AGENTS.md` and `.claude/CLAUDE.md` are absent from this dedicated clone, so
  their mandated read used the read-only primary checkout; no external file was
  changed.
- The retained indexed authoring package already supplies the two requested
  family shapes and unchanged concrete admission, so this package measures and
  binds those results instead of creating another generator.
- The retained finite Protocol carrier explicitly lacks the target's complete
  graph and first-class reduction semantics. Fixture-representable graph counts
  are frozen, but exact target graph counts cannot honestly be affirmative.
- Section 15 lists observed semantic pressures, not one reopening condition per
  candidate design. Regular finite repetition triggers none; the relevant
  reversal condition is infeasible or lossy finite lowering, with the
  acceptance-relevant-effect condition applicable only if exact effect
  semantics are lost.
- A family semantic profile has no specified attachment to current Core
  identity: the current formula selects the one fixed Interaction profile. A
  companion profile is external metadata; a Core-selecting profile requires an
  identity/profile-selection change.
- The first alternate-index attempt could not write new blob objects into the
  sandbox's read-only `.git/objects`; it exited `1` before producing a usable
  inventory. A clone-local alternate object store resolved this without
  touching `.git`. One failed temporary index was moved to `/tmp` during that
  recovery and removed during cleanup; it contained only the alternate index,
  not repository content or private material.

Main should commit the complete working tree with subject
`docs: probe protocol families against their instances`. This lane must not
stage in the primary index, commit, push, or open a pull request.

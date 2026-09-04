# Migration Text Freeze Review

> **State:** `Affirmative/F0V2C1-A-MIGRATION-TEXT-CLOSED` after round nine;
> all seventeen questions close, including the three round-eight blockers and
> the newly added checker-contract question
> **Authority:** None. This verification lane changes no owner page, source
> profile manifest, or published identity.
> **Executable evidence:**
> [`evaluation/formal-source-migration-text-review-f0v2c1`](../../../../evaluation/formal-source-migration-text-review-f0v2c1/README.md)

## 1. Exact question and aggregate

Does the current migrated PIR owner text close all seventeen verification
questions: the ten questions frozen in round seven, plus Interface completion
derivability, source-authority preimage equations, heterogeneous
challenge-transition representability, required-influence exactness, the
Analysis owner-read join, public-setup view totality, and the exact
checked-construction checker contract?

Round nine answers yes for the exact current sources. All seventeen questions
are affirmative, so the current aggregate is
`Affirmative/F0V2C1-A-MIGRATION-TEXT-CLOSED`.

The audit pins the six migrated owner pages and eight migrated manifests. It
does not treat a resolved selector, a passing source compiler, or a finite
oracle as proof that the represented semantics are correct.

Sections 2 through 10 preserve the first-round evidence and proposed repairs
as history. The numbered round sections record each later recheck; `Round
nine` is the current result and supersedes the earlier aggregates without
rewriting their historical evidence.

## 2. Answer one: decision fidelity

**Finding:** `Negative/F0V2C1-N-DECISION-FIDELITY`.

Seven of the eight recorded selections are visibly applied. The migration
applies the authority-envelope choice, the no-nominal-law rule, the stopped
outcome lane, the completed-record shape, the public-coin graph clarifications,
the manifest revision migration, and the owner-page scope restriction. It does
not apply the selected exact family-view body packets.

The incomplete text is at:

- `docs-next/pir/fiat-shamir.md`, Section 13, lines 1255-1305;
- `docs-next/pir/duplex-sponge-fiat-shamir.md`, Sections 11.1-11.4, lines
  967-1052; and
- the corresponding static-view schema declarations at canonical lines
  1345-1403 and duplex lines 866-930.

Those locations contain field-name displays and schema references, but not the
selected closed finite descriptions or family-local body compilers. The exact
field census is in answer seven. Missing body text is not converted into an
affirmative fidelity result.

## 3. Answer two: Terminal contract

**Finding:** `Negative/F0V2C1-N-TERMINAL-CONTRACT`.

The contract is not executable as written:

- `docs-next/pir/interactive-core.md`, Section 10.2, lines 1428-1445, adds
  `Guard(s)` for a scope opening, but `ScopeDecl` at Section 4.4, lines 572-575,
  has only `parent` and `opening`; openings are deterministic boundaries at
  lines 590-601, not guarded occurrences.
- Section 10.2, lines 1470-1472, uses `GuardInputs` and `GuardTerm`, neither of
  which is defined in the six migrated pages or executable Foundation.
- Section 10.2, lines 1453-1454, specifies `let` by prose substitution rather
  than by the exact de Bruijn environment operation used by the selected
  structural analyzer.
- Lines 1432-1436 reverse the liveness explanation. If a later occurrence is
  live, an earlier terminal did **not** stop execution; it is not enough to say
  that it could have stopped both occurrences.

After deleting the nonexistent scope-opening guards, the intended implication
is sound for the opaque-guard abstraction:

```text
o_earlier < o_later
and AttemptGuards(o_earlier) subset AttemptGuards(o_later)
and o_later is attempted
implies o_earlier was attempted.
```

The executable oracle exhausts both subsets of two independent guard atoms and
all valuations: 16 applicable implication cases and zero counterexamples. The
reason is direct. Later liveness means no earlier terminal stopped the run;
the earlier occurrence's deterministic scope boundary has already been
processed; and every guard needed by the earlier occurrence is included among
the true later guards.

The migration deliberately omits the predecessor's impossible-region
exemption. That makes the rule stricter: an authored unreachable terminal can
be refused rather than discharged vacuously. It rejects none of the committed
positive predecessor regions. Their first-active region counts are `2/3/3`
over eight baseline valuations and `2/1/1` over four logical-control
valuations, with no impossible positive terminal region. This is finite fixture
evidence, not a theorem for arbitrary Core values.

The predecessor executables cannot currently re-establish more against this
migration. The terminal contract gate stops because its pinned target source
no longer equals the migrated source; the terminal projection and integrated
graph gates stop earlier because their temporary overlays now duplicate a
definition that the migration made live. These are stale-gate failures, not
counterexamples to the migrated contract and not successful revalidation.

## 4. Answer three: public-coin graph transfer and sinks

**Finding:** `Affirmative/F0V2C1-A-PCGRAPH-TRANSFER`.

The migrated Section 11 wording applies the selected graph clarifications:

- deterministic outputs join occurrence activity with all input producers
  after the exact ABI check;
- a logical-access publication effect is explicitly `Publish(activity)` and
  has no output node;
- a public Query effect joins activity with the index producer, while the
  publication-effect edge is explicitly excluded from that join;
- Challenge failure precedence is `Invalid`, then `VerifierPrivate`, then the
  ordinary semantic-validity case;
- public Query sinks include the effect, its activity through the public
  observation rule, and the index producer; and
- acceptance sinks include every accepting Terminal state and the producers of
  its public outputs.

The exact migrated locations are `docs-next/pir/interactive-core.md`, Section
11, lines 1582-1662. They agree with the selected transfer and sink coordinates
and with the independent mechanized wording review. This affirmative is only a
source-text correspondence result. It does not prove graph construction for an
arbitrary Core or any cryptographic property.

## 5. Answer four: internal owner-view closure

**Finding:** `Negative/F0V2C1-N-OWNER-CLOSURE`.

All sixteen `StaticViewSchema` declarations point to a body display that occurs
exactly once on the same owner page. The Interaction, canonical-framed, and
duplex execution views consistently distinguish Fresh and the two transformed
interpretations; the Claim and Terminal rows use the migrated derived
disposition and required-reduction fields; and each split source envelope has
the selected arm count.

That local reference success is not complete name closure. Five expressions
remain unresolved or non-exact:

| Location | Unclosed expression |
|---|---|
| `docs-next/pir/interactive-core.md`, Section 10.2, lines 1428-1445 | `Guard(s)` for a deterministic scope opening |
| same section, lines 1453-1454 | prose-only `let` substitution in `Must` |
| same section, lines 1470-1472 | `GuardInputs`, `GuardTerm` |
| `docs-next/pir/interactive-core.md`, Section 12.5, line 2464 | `AdmittedModuleEffectAtom` |

`AdmittedModuleEffectAtom` is discussed by a research note, but it is not
defined by the migrated owner text, executable Foundation, or the Interaction
atomic-boundary grammar at lines 2173-2181 and 2726-2728. A research-note
description cannot silently become owner authority.

## 6. Answer five: manifest closure

**Finding:** `Affirmative/F0V2C1-A-MANIFEST-CLOSURE`.

The eight migrated manifests are syntactically closed under profile references:
all 107 definitions resolve their direct dependencies, all 55 subjects resolve
their compiler and law names, each profile revision moves from zero to one,
fourteen existing definitions move from zero to one, and 47 new definitions
start at zero. The source-envelope compiler arm counts are:

| Profile | binding | capability | no policy | closure |
|---|---:|---:|---:|---:|
| Interaction | 2 | 2 | 1 | 2 |
| public setup | 1 | 1 | 1 | 1 |
| canonical framed | 2 | 2 | 2 | 2 |
| duplex sponge | 2 | 2 | 2 | 2 |
| interface plan | 2 | 2 | 1 | 2 |
| endpoint source view | 1 | 1 | 1 | 1 |

The local reference graph contains two finite strongly connected components:
the canonical and duplex source-view laws each reference five static-view
schemas, and those schemas reference the source-view law. Together they contain
twelve declarations and twenty internal edges. This is not a profile-import
cycle. The publication specification assigns declaration ordinals before
encoding references, permits exact `self` references, and computes local
reachability with a visited set; both independent compilers accept and agree on
these components. No source rule found in this review requires this local
reference relation to be acyclic, so the observation is not converted into a
negative.

Both family schemas currently cite the generic Interaction static-view body
compiler. That is a resolved declaration and is consistent with the migrated
source as written. Selecting the missing family-local finite descriptions and
compiler text remains the distinct negative in answer seven and will require a
manifest rotation when repaired; it does not make the present manifest
references malformed.

## 7. Answer six: publication reconstruction

**Finding:** `Affirmative/F0V2C1-A-PUBLICATION-COMPILERS`.

The two existing publication compilers independently reconstruct the same
complete eighteen-profile table from the migrated source. Direct identity
printing exits successfully.

The checked publication package still exits nonzero because the committed
publication controls have not been written for this migration. Its 34 tests
contain seven expected stale-control failures: one for each of six changed
legacy rows (`interaction`, `canonical-framed-fiat-shamir`,
`duplex-sponge-fiat-shamir`, `public-setup`, `commitment-opening`, and
`oracle-commitment`) and one published-table comparison. There is no compiler
disagreement. Therefore the exact answer to the reconstruction question is
affirmative, while publication itself remains false.

## 8. Answer seven: remaining family-body fields

**Finding:** `Negative/F0V2C1-N-FS-BODY-CLOSURE`.

The eight displayed family bodies contain 95 fields. The migrated generic
closed-name and law-reference conventions close 50. Forty remain prose
placeholders and five remain undefined symbols, spanning eleven owner-selection
families:

| Owner location | Status | Fields |
|---|---|---|
| `docs-next/pir/fiat-shamir.md`, Section 13, lines 1255-1268 | prose | `fixed_initial_state_and_derived_initialization_schedule`, `exact_frame_schedule_coordinates` |
| same section, lines 1271-1278 | prose | `scope_binding_requirements`, `per_challenge_ordered_required_influence_sets`, `reduction_and_module_additions`, `exact_prefix_law` |
| same section, lines 1281-1292 | prose | `challenge_namespace_derivation`, `acceptance_abi`, `decoder_abi`, `draw_bounds`, `exact_length_law`, `state_update_before_decode_law`, `retry_law`, `sampling_failure_law`, `challenge_decoding_coordinates` |
| same section, lines 1295-1305 | prose | `result_schema` |
| `docs-next/pir/duplex-sponge-fiat-shamir.md`, Section 11.1, lines 967-987 | prose | `state_carrier_and_invariant`, `binary_instance_carrier_and_bit_convention`, `exact_instance_binding_projection`, `fixed_start_absorb_squeeze_laws`, `exact_edge_case_laws`, `exact_construction_material_schema`, `prover_required_schedule`, `verifier_complete_schedule` |
| same section and lines | undefined | `semantic_argument_shape`, `exact_operational_resource_projection` |
| Section 11.2, lines 994-1004 | prose | `exact_instance_binding_sequence`, `salt_coordinate`, `per_challenge_ordered_encoded_input_coverage`, `exact_message_coverage`, `exact_challenge_coverage`, `prover_required_prefix_law`, `verifier_complete_schedule_law` |
| same section and lines | undefined | `prohibited_additions` |
| Section 11.3, lines 1018-1029 | prose | `per_challenge_squeeze_and_decoder_map`, `decode_after_state_transition_law`, `prover_execution_domain`, `verifier_execution_domain` |
| same section and lines | undefined | `decoder_totality_contracts`, `exact_squeeze_event_projection` |
| Section 11.4, lines 1036-1051 | prose | `result_schema`, `instance_projection`, `construction_material_map`, `prover_schedule_correspondence`, `verifier_schedule_correspondence` |

The current displays correctly omit the old owner-local result reference and
correctly treat identity-map names as nullary tags. Those improvements do not
supply finite descriptions for the 45 fields above.

## 9. Proposed delta

This section proposes owner changes; it does not apply them. Each proposal is
guarded by the finding code that motivates it. Main and the relevant owner must
review the identity rotation before adoption.

### 9.1 Exact Terminal replacement

**Owner page and section:** `docs-next/pir/interactive-core.md`, Section 10.2,
replace lines 1427-1475.

**Gate:** `F0V2C1-N-TERMINAL-CONTRACT` and
`F0V2C1-N-OWNER-CLOSURE`.

**Exact replacement text:**

```text
The Terminal contract is decided by two further closed laws of the same kind.
Scope openings are deterministic and unguarded. `AttemptGuards(o)` therefore
contains only the structurally identified `EvaluateBoolean` body of occurrence
`o`; `Always` contributes nothing. Two occurrences with structurally identical
guard bodies read the same values and evaluate alike on every path. If a later
occurrence is live, no earlier terminal stopped the run. If its attempt guards
include an earlier occurrence's guards, that earlier guard was true after its
deterministic scope boundary and the earlier occurrence was attempted.

AttemptGuards(o) := { Guard(o) } minus { Always }

AttemptedWhenever(o_later, o_earlier) :=
  o_earlier < o_later
  and AttemptGuards(o_earlier) subset AttemptGuards(o_later)

InputMust(i) = { when_true: {Positive(i)},
                 when_false: {Negative(i)} }

Must(term with n inputs) :=
  MustEnv(term, [InputMust(0), ..., InputMust(n - 1)])

MustEnv(variable i, environment) = environment[i]
MustEnv(constant true, environment) =
  { when_true: {}, when_false: Impossible }
MustEnv(constant false, environment) =
  { when_true: Impossible, when_false: {} }
MustEnv(let x = e1 in e2, environment) =
  MustEnv(e2, [MustEnv(e1, environment)] ++ environment)
MustEnv(if c then a else b, environment) =
  let C = MustEnv(c, environment),
      A = MustEnv(a, environment),
      B = MustEnv(b, environment) in {
    when_true:  Meet(C.when_true union A.when_true,
                     C.when_false union B.when_true),
    when_false: Meet(C.when_true union A.when_false,
                     C.when_false union B.when_false) }
MustEnv(primitive call, environment) =
  { when_true: {}, when_false: {} }
a union with Impossible is Impossible;
Meet(X, Y) = X when Y is Impossible, Y when X is Impossible,
             X intersect Y otherwise
MustWhenTrue(term) := Must(term).when_true

GuardInputs(o) = [] and GuardTerm(o) = None
  when Guard(o) is Always;
GuardInputs(o) = inputs and GuardTerm(o) = the authenticated term of algorithm
  when Guard(o) is EvaluateBoolean { algorithm, evaluation_contract, inputs }.

TerminalContract(t), with o_t the occurrence of ReachTerminal(t) :=
  for every c in t.required_true_checks,
      with o_c the occurrence of InvokeCheck(c):
    AttemptedWhenever(o_t, o_c)
    and GuardTerm(o_t) is not None
    and MustWhenTrue(GuardTerm(o_t)) is not Impossible
    and there is an input ordinal i of Guard(o_t) with
          GuardInputs(o_t)[i] = OccurrenceOutput(o_c, 0)
          and Positive(i) in MustWhenTrue(GuardTerm(o_t));
  for every r in t.required_applied_reductions,
      with o_r the occurrence of ApplyReduction(r):
    AttemptedWhenever(o_t, o_r);
  on every schedule path on which o_t is active,
    LiveClaims(o_t) = t.terminal_claims
```

Immediately after that block add this exact sentence:

> An impossible `MustWhenTrue` region is refused rather than discharged
> vacuously; this is the selected strict behavior and not an affirmative claim
> that the authored terminal is reachable.

**Identity effect:** the Interaction source law and every dependent profile
identity rotate. The published table must not be written until the corrected
source and all dependent checks agree.

**Evidence:** the executable review's 16-case implication oracle and positive
region census, under `F0V2C1-N-TERMINAL-CONTRACT`.

**Reversal condition:** withdraw this text if the owner selects vacuous
discharge for impossible terminal regions, or if Foundation's authenticated
term binder convention differs from the displayed head-prepending de Bruijn
environment.

**Non-claims:** this replacement is not a general implication solver, a
reachability proof, arbitrary-Core validation, or implementation
correspondence.

### 9.2 Exact admitted-module atom replacement

**Owner page and section:** `docs-next/pir/interactive-core.md`, Sections 12.3,
12.5, and Appendix A; current lines 2173-2181, 2462-2465, and 2726-2728.

**Gate:** `F0V2C1-N-OWNER-CLOSURE`.

**Exact replacement text:** add the following definition before
`PIRStaticViewFieldCoordinate`:

```text
AdmittedModuleEffectAtom(x) =
  require x is the complete ModuleEffectRef admitted under Section 8;
  require x.module and x.declaration agree exactly;
  require x.declaration resolves in the authenticated module closure;
  require the evaluator supports that exact effect declaration;
  require x.payload validates strictly under the declaration's owner schema;
  return ModuleEffectRefBody(x) as one opaque leaf.
```

Replace the final line of `PIRViewAtomicBoundary` with:

```text
  | PIRReference | PIRProfileLawReference | AdmittedModuleEffect
```

Replace `PIRViewAtomicBoundaryBody` with:

```text
PIRViewAtomicBoundaryBody =
  V(0,Unit) | V(1,Unit) | V(2,Unit) | V(3,Unit) | V(4,Unit)
| V(5,Unit) | V(6,ValueTypeBody(value_type)) | V(7,Unit) | V(8,Unit)
| V(9,AdmittedModuleEffectAtom(effect))
```

The existing `EffectViewBody.supported_extensions[].effect` line remains
`effect: AdmittedModuleEffectAtom`.

**Identity effect:** the Interaction static-view grammar and dependent profile
identities rotate.

**Evidence:** exact unresolved-name and atomic-boundary census under
`F0V2C1-N-OWNER-CLOSURE`.

**Reversal condition:** replace this proposal if the owner chooses an
effect-specific structural projection instead of the selected opaque admitted
leaf. Such a projection requires its own owner schema and derivation law.

**Non-claims:** the atom authenticates a declaration and payload; it does not
prove that host code implements the module declaration.

### 9.3 Exact family-body replacement

**Owner pages and sections:** `docs-next/pir/fiat-shamir.md`, Section 13, lines
1255-1305 and 1345-1403, plus Appendix A before the body-grammar end marker at
line 1834; `docs-next/pir/duplex-sponge-fiat-shamir.md`, Section 11, lines
866-930 and 967-1052, plus Appendix A before the body-grammar end marker at
line 1321.

**Gates:** `F0V2C1-N-DECISION-FIDELITY` and
`F0V2C1-N-FS-BODY-CLOSURE`.

The exact replacement text is already content-addressed in the repository and
is too large to duplicate safely in this note. Apply this deterministic textual
recipe; it identifies one byte sequence after normalization:

1. For the canonical-framed page, replace the four compact body displays with
   the JSON text at
   `evaluation/formal-source-fs-view-determinacy-f0v3/proposed/fiat-shamir-section-13.md`
   lines 50-843, whose complete file SHA-256 is
   `53eeadb5fe8e6eb29dc7115001adbfde80a7565c212f3d2832b32cc5b68a1f17`.
   In that copied byte sequence make exactly these substitutions:
   `CanonicalTranscriptDeclarationViewBody` to
   `TranscriptDeclarationViewBody`, `CanonicalRequiredInfluenceViewBody` to
   `RequiredInfluenceViewBody`, `CanonicalChallengeTransitionViewBody` to
   `ChallengeTransitionViewBody`, `CanonicalFSConstructionViewBody` to
   `FSConstructionViewBody`, and
   `zkc.f0v3b.proposed-family-view-schema.v0` to
   `zkc.pir.canonical-framed.family-view-schema.v0`. Apply the corresponding
   four view-name substitutions in the final `views` object. Do not copy the
   proposal-only schema declaration lines 34-45 or marker comments.
2. Immediately before the canonical page's
   `zkc-profile-source:canonical-framed-fs-body-grammar:end` marker, insert
   exactly the body-compiler text at the same proposal file's lines 854-858,
   without marker comments.
3. For the duplex page, replace the four compact body displays with the JSON
   text at
   `evaluation/formal-source-fs-view-determinacy-f0v3/proposed/duplex-section-11.md`
   lines 52-1249, whose complete file SHA-256 is
   `372460721e1176def0a0e17da5c4bc20f3bbfa1e12b6b9e77653f878575c6897`.
   In that copied byte sequence replace only
   `zkc.f0v3b.proposed-family-view-schema.v0` with
   `zkc.pir.duplex-sponge.family-view-schema.v0`. Do not copy the proposal-only
   schema declaration lines 37-48 or marker comments.
4. Immediately before the duplex page's
   `zkc-profile-source:duplex-sponge-fs-body-grammar:end` marker, insert exactly
   the body-compiler text at the same proposal file's lines 1260-1264, without
   marker comments.

This recipe removes proposal-only package identifiers from shipped source,
retains the current owner-facing schema declarations, and supplies the exact
finite descriptions for all 45 currently unclosed fields.

**Identity effect:** both family profiles and their dependent identity cones
rotate. The compiler declarations and schema dependencies must be added before
reconstructing the publication table.

**Evidence:** the 95-field classification under
`F0V2C1-N-FS-BODY-CLOSURE`; the source packets cited above are candidate
evidence, not current owner authority.

**Reversal condition:** do not adopt either packet if the relevant owner
selects a different field carrier, law binding, sequence bound, or result-body
omission. Missing owner selection remains nonaffirmative.

**Non-claims:** finite body determinacy does not establish transcript
correctness, implementation correspondence, theorem applicability, or
Fiat--Shamir security.

## 10. Result boundary

This review is pinned source inspection, finite enumeration, dependency-graph
analysis, and differential publication reconstruction. It is not owner-page
authority, publication, a semantic identity blessing, a live compiler or
runtime result, backend or host-module correspondence, relation satisfaction,
theorem truth, protocol soundness, random-oracle or concrete-sponge evidence,
endpoint validity, deployment authorization, or production readiness.

## Round two

Round two reruns the same seven questions against the repaired migration head.
All four former negatives close; none remains.

| Question | Round one | Round two | Current evidence location |
|---|---|---|---|
| decision fidelity | `Negative/F0V2C1-N-DECISION-FIDELITY` | `Affirmative/F0V2C1-A-DECISION-FIDELITY` | the Terminal, owner-boundary, and family-body repairs below complete all eight recorded selections |
| Terminal contract | `Negative/F0V2C1-N-TERMINAL-CONTRACT` | `Affirmative/F0V2C1-A-TERMINAL-CONTRACT` | `interactive-core.md` Section 10, lines 1427-1509 |
| public-coin graph | `Affirmative/F0V2C1-A-PCGRAPH-TRANSFER` | unchanged | `interactive-core.md` Section 11, lines 1582-1662 |
| owner-name closure | `Negative/F0V2C1-N-OWNER-CLOSURE` | `Affirmative/F0V2C1-A-OWNER-CLOSURE` | `interactive-core.md` lines 2191-2202 and 2752-2755 |
| manifest closure | `Affirmative/F0V2C1-A-MANIFEST-CLOSURE` | unchanged | eight migrated manifests, 107 definitions and 55 subjects |
| publication compilers | `Affirmative/F0V2C1-A-PUBLICATION-COMPILERS` | unchanged | both compilers agree at the migration base and current source |
| family-body closure | `Negative/F0V2C1-N-FS-BODY-CLOSURE` | `Affirmative/F0V2C1-A-FS-BODY-CLOSURE` | `fiat-shamir.md` lines 1255-1364 and `duplex-sponge-fiat-shamir.md` lines 967-1147 |

The Terminal repair removes scope-opening guards, defines `GuardInputs` and
`GuardTerm`, gives `MustEnv` its de Bruijn environment and exact `let`
operation, corrects the later-occurrence explanation, and explicitly refuses
an impossible `MustWhenTrue` region. The same 16-case finite implication
fixture has zero counterexamples. The atomic-boundary repair adds
`AdmittedModuleEffect`, defines its opaque atom, and gives it body arm 9; the
boundary now has ten arms.

### Family-body census

Every top-level field is now an exact identity, value, natural, closed tag, law
reference, record, or sequence of those. No prose-only or undefined field
remains:

| Body | Fields | Non-exact fields |
|---|---:|---|
| `TranscriptDeclarationViewBody` | 13 | none |
| `RequiredInfluenceViewBody` | 7 | none |
| `ChallengeTransitionViewBody` | 11 | none |
| `FSConstructionViewBody` | 9 | none |
| `DuplexTranscriptDeclarationViewBody` | 20 | none |
| `DuplexEncodedInputCoverageViewBody` | 10 | none |
| `DuplexChallengeTransitionViewBody` | 11 | none |
| `DuplexFSConstructionViewBody` | 14 | none |

The normalized owner bodies have exactly five semantic deviations from the
earlier candidate packet descriptions:

| Body and field | Candidate packet | Current owner | Judgment |
|---|---|---|---|
| transcript declaration, `application_domain` | opaque canonical value | declaration reference to `pir.fs-application-domain` | current owner is right: the source field is declaration authority, not an untyped value |
| transcript declaration, `frame_body_law` | source-view law | body-grammar law | current owner is right: frame-body encoding is fixed by the body grammar |
| challenge transition, `draw_bounds` | anonymous ordinal-0/ordinal-1 natural record | named `squeeze_length` and `maximum_draws` naturals | current owner is right: the same finite pair gains stable owner-native names |
| canonical checked result, `result_schema` | omitted | `PIRRuntimeSchema` | current owner is right: the result description is an exact PIR field while the owner-local result reference remains outside the body |
| duplex checked result, `result_schema` | omitted | `PIRRuntimeSchema` | current owner is right for the same reason |

Named record fields versus numeric packet ordinals, `PortableAlgorithmRef`
versus the packet-local `AlgorithmRef` alias, and named helper records versus
their packet-local inline encodings are presentation differences in the
pages' own finite grammar, not further semantic deviations. The checker pins
both packet files and asserts the five differences above.

### Publication cone

Direct identity printing and an independent baseline/current reconstruction
agree. Relative to the pre-migration base, seventeen profiles rotate:
`interaction`, `canonical-framed-fiat-shamir`,
`duplex-sponge-fiat-shamir`, `public-setup`, `commitment-opening`,
`oracle-commitment`, `verifier-derived-query-plan`, `interface-plan`,
`oir-endpoint-graph`, `endpoint-source-view`, `oir-projection-relation`,
`relations`, `analysis-cryptographic-property`, `analysis-afk-transport`,
`analysis-afk-theorem-source-validation`,
`analysis-incremental-composition`, and
`analysis-incremental-composition-source-validation`. Only
`analysis-kernel` is stable, and the Foundation identity is unchanged.

### Current owner-page disposition

No repaired owner section is underdetermined or wrong for these seven
questions, so round two proposes no owner-page delta. The affirmative aggregate
is a bounded source-text closure result, not publication, implementation
correspondence, theorem evidence, or a security claim.

## Round-one handoff (historical)

Main should commit this working tree with subject:

```text
test: review the migrated owner text for closure and decision fidelity
```

Files changed:

- `evaluation/formal-source-migration-text-review-f0v2c1/run.py`: independent
  pinned source, name-closure, finite implication, manifest-graph, revision,
  source-envelope, and publication-agreement checks;
- `evaluation/formal-source-migration-text-review-f0v2c1/expected-findings.json`:
  frozen seven-finding result and evidence metrics;
- `evaluation/formal-source-migration-text-review-f0v2c1/README.md`: exact
  question and pass/non-claim boundary;
- this note: seven answers and owner-routed proposed deltas;
- `checks/manifest.json`: `research.migration-text-review` registration;
- `evaluation/lifecycle.json`: active source-definition sequence registration;
- `evaluation/README.md`: one package row; and
- `checks/tests/test_evaluation_lifecycle.py`: count pins moved to 54 research
  checks, 56 packages, and 31 active-sequence entries.

No owner page, source profile manifest, directory README, publication table,
or target-owner page was edited.

Commands and outcomes:

| Command | Exit | Wall time | Outcome |
|---|---:|---:|---|
| `git diff b82ce5e..1a906ee --stat` and complete per-file migration diffs | 0 | under 0.1 s each | migration range inspected before package work |
| `python3 -B evaluation/formal-source-migration-text-review-f0v2c1/run.py --check` | 0 | 0.26 s | seven of seven frozen findings reproduced; four blockers |
| `python3 -B evaluation/semantic-profile-publication/run.py --print-identities` | 0 | 0.34 s | both compilers reconstructed the eighteen-profile table |
| `python3 -B evaluation/semantic-profile-publication/run.py --check` | 1 | 3.50 s | 34 tests ran; seven stale publication-control failures, no compiler disagreement |
| terminal owner-contract predecessor `run.py --check` | 1 | 0.09 s | pinned source-gap assertion no longer matches migrated source |
| terminal owner-projection predecessor `run.py --check` | 1 | 0.31 s | temporary overlay duplicates the now-live source-purpose-role definition |
| integrated graph predecessor `run.py --check` | 1 | 0.32 s | reaches the same duplicate-definition stop through the projection dependency |
| `python3 -B checks/run.py validate` with alternate index and offline local cache | 0 | 0.04 s | manifest valid: 71 checks, six tiers |
| `python3 -B checks/run.py run --tier developer` with alternate index and offline local cache | 0 | 1.06 s | eight of eight developer checks passed, including lifecycle inventory |
| `python3 -B checks/run.py run --check research.migration-text-review` with alternate index and offline local cache | 0 | 0.45 s | selected check passed |

The first `GIT_INDEX_FILE=.lane-index git add -A` attempt exited 128 because
the mounted Git object database is read-only. The successful retry used the
clone-local `.lane-objects` directory as the write object store, the real
object directory as a read-only alternate, and excluded both temporary paths
from the index. The real index was never changed. The temporary index, object
store, and local cache are removed after final inspection.

Aggregate outcome: `Negative/F0V2C1-N-MIGRATION-TEXT-NOT-CLOSED`.
Public-coin graph wording and publication-compiler agreement are affirmative;
manifest closure is also affirmative; decision fidelity, Terminal closure,
owner-name closure, and family-body closure are negative.

Non-claims: a passing package reproduces this bounded source review. It does
not close or repair the owner text, publish an identity, prove arbitrary-Core
behavior, establish compiler/runtime/backend correspondence, prove relation or
theorem truth, establish protocol security, or authorize deployment.

Surprises: the family manifests have two finite local reference components,
which the publication mechanism permits and both compilers reconstruct; the
selected family-body packets were not migrated; and three predecessor gates
abort on migration staleness before they can retest their old positive
carriers. Those aborts are not regressions or affirmatives.

Where the brief was wrong: `AGENTS.md` is absent from this dedicated clone, so
the read-only primary-copy file was used; `.claude/CLAUDE.md` is absent from
both the clone and the read-only primary checkout; and the example alternate
index command is insufficient under the read-only object mount without a
clone-local writable object directory.


## Round-two handoff (historical)

Main should commit this working tree with subject:

```text
test: rerun the migration text review and correct the holdout carrier
```

Files changed:

- `evaluation/formal-source-migration-text-review-f0v2c1/run.py`,
  `expected-findings.json`, and `README.md`;
- `evaluation/formal-source-holdout-readjudication-f0v2c2/run.py`,
  `adjudication.json`, `expected-findings.json`, and `README.md`;
- `evaluation/expressibility-axes/axes.json`, `run.py`, and `README.md`;
- `docs-next/notes/semantic-revalidation-and-redesign/formal-assurance-research/f0v2c1-migration-text-review.md`;
- `docs-next/notes/semantic-revalidation-and-redesign/formal-assurance-research/f0v2c2-holdout-readjudication.md`;
- `checks/manifest.json`; and
- `evaluation/README.md`.

No owner page, profile manifest, publication table, directory README,
lifecycle entry, lifecycle count pin, real Git index, or private ledger was edited.
No lifecycle count moves because this lane adds no package.

Validation and evidence:

| Command | Exit | Wall time | Result |
|---|---:|---:|---|
| `git log --oneline -12` and the migration commit diffs | 0 | under 0.1 s each | migration and repair history inspected before editing |
| `python3 -B evaluation/formal-source-migration-text-review-f0v2c1/run.py --check` | 0 | 0.64 s | seven affirmative findings, no blocker |
| `python3 -B evaluation/formal-source-holdout-readjudication-f0v2c2/run.py --check` | 0 | 0.04 s | 25 findings, five fits, three breaks, no verdict disagreement |
| `python3 -B evaluation/expressibility-axes/run.py --check` | 0 | 0.12 s | 18 frozen findings; aggregate unchanged |
| `python3 -B evaluation/semantic-profile-publication/run.py --print-identities` | 0 | 0.31 s | both compilers reconstructed 18 identities; the review derives the 17-profile cone |
| `python3 -B checks/run.py validate` with the alternate index | 0 | 0.04 s | 74-check manifest valid |
| `python3 -B checks/run.py run --tier developer` with the alternate index and clone-local offline cache | 0 | 1.11 s | eight of eight developer checks passed |
| `python3 -B checks/run.py run --check research.migration-text-review` with the same environment | 0 | 0.69 s | focused review check passed |
| `python3 -B checks/run.py run --check research.holdout-readjudication` with the same environment | 0 | 0.10 s | focused holdout check passed |
| `python3 -B checks/run.py run --check research.expressibility-axes` with the same environment | 0 | 0.19 s | focused axis check passed |
| `git diff --check` | 0 | 0.06 s | no whitespace errors |

The temporary alternate index, object store, and clone-local cache were removed
after validation; the real index was never changed.

Aggregate outcome: the migration review is
`Affirmative/F0V2C1-A-MIGRATION-TEXT-CLOSED`; all four former negatives close.
The holdout aggregate remains
`Affirmative/F0V2C2-A-HOLDOUTS-READJUDICATED`; the WHIR and axis corrections
change no verdict. Four source-specialized fitting carriers remain
`CannotAnswer` for exact references.

Nonclaims: these passes establish bounded, byte-pinned source-text and
instrument consistency only. They do not publish identities, establish
implementation or backend correspondence, prove relation satisfaction or
theorem truth, establish any security property, validate endpoints or
deployment, or show that delaying the WHIR fold preserves a selected source
semantics.

Surprises: the first developer-tier attempt exited 1 in 0.35 s because listing
the candidate packet files as manifest sources made one check route to two
evaluation packages. Removing those cross-package manifest routes preserved
the runner's direct byte pins and the rerun passed. The alternate index also
needed a clone-local object directory and explicit removal of its transient
lockfile from the index inventory.

Where the brief was wrong: `AGENTS.md` and `.claude/CLAUDE.md` are absent
from this clone, so their read-only primary-checkout copies were used. The
workflow's private status-ledger append conflicts with this lane's express
outside-clone write prohibition and the read-only mount, so status is recorded
here. The example alternate-index command also needs a writable object store
under this mount.

## Round three

Round three reruns the same seven questions after the forward abstract state
was added to Interaction Core Section 10. Five answers remain affirmative.
The Terminal-contract and owner-name questions are `CannotAnswer` because the
new `ClaimStatus` law does not define the region of either `ClaimSource` arm.

| Question | Round two | Round three | Current finding |
|---|---|---|---|
| decision fidelity | affirmative | unchanged | `Affirmative/F0V2C1-A-DECISION-FIDELITY` |
| Terminal contract | affirmative | cannot answer | `CannotAnswer/F0V2C1-C-TERMINAL-CLAIM-SOURCE-REGION` |
| public-coin graph | affirmative | unchanged | `Affirmative/F0V2C1-A-PCGRAPH-TRANSFER` |
| owner-name closure | affirmative | cannot answer | `CannotAnswer/F0V2C1-C-OWNER-CLAIM-SOURCE-REGION` |
| manifest closure | affirmative | unchanged | `Affirmative/F0V2C1-A-MANIFEST-CLOSURE` |
| publication compilers | affirmative | unchanged | `Affirmative/F0V2C1-A-PUBLICATION-COMPILERS` |
| family-body closure | affirmative | unchanged | `Affirmative/F0V2C1-A-FS-BODY-CLOSURE` |

The aggregate is therefore
`CannotAnswer/F0V2C1-C-MIGRATION-TEXT-NOT-CLOSED`. The affirmative aggregate
is reserved for a state in which all seven questions close.

### Executable results for the new laws

The independent schedule oracle uses two structurally identified guard atoms,
all ordinary/terminal and `Always`/guarded occurrence forms through length
four, and both no-opening and deterministic-opening variants. Across 3,108
schedules, 11,820 occurrence regions, and 47,280 valuation comparisons,
`Region(o)` is true exactly when `o` is attempted. Its 3,868 impossible
regions are exactly its 3,868 unreachable regions. A further 23,640 comparisons
show that the candidate boundary region is true exactly when its deterministic
unguarded scope opening is processed.

The path reference evaluates 18,282 claim/source/linear-consumer cases: 4,134
with occurrence sources and 14,148 with candidate scope-boundary sources.
Every abstract `Live` verdict is live on every path reaching the target
occurrence, and every `Dead` verdict is live on none; both counterexample
counts are zero. The generic corpus exercises 3,320 `Unknown` outcomes,
confirming that refusal is reachable rather than dead text. The candidate
boundary results support the proposed repair below; they do not fill the
missing owner definition.

The must-fact oracle evaluates 238 typed Boolean term shapes over all four
two-input valuations. It checks 476 true/false branch obligations, including
all ten catch-all portable-term constructors, a non-Boolean input environment,
and a nested conditional whose true branch requires both polarities of one
input. No literal is invented; forty unreachable branches are classified
`Impossible`, and the contradiction discriminator is one of them. This also
checks that the standalone impossible-region clause refuses a terminal even
when it names no required Check.

### Frozen carrier outcomes

No `Unknown` verdict arises in the represented frozen carriers:

- the exact terminal projection has terminal live-Claim sets `[1]`, `[2]`,
  and `[2]`;
- each of the five integrated carriers has `[0, 1, 2]` at all three terminal
  frontiers; reusable claim 0 is therefore `Live` at fifteen of fifteen
  frontiers, so the existing five-carrier refusal remains sound; and
- the represented WHIR shape has no live Claim at Accept and only the initial
  Claim at fallback, while the represented WARPfold shape has empty sets at
  both frontiers.

Four fitting boundary-analysis holdout rows still lack exact source-profile
carrier coordinates. Their existing `CannotAnswer` remains; this review does
not turn the represented-shape result into an exact Circle STARK, WARPfold,
virtual Sumcheck, or interactive Galois-ring Core. Reapplying the closed state
changes none of the eight holdout verdicts: five still fit, three still break,
and there are no bends or disagreements.

### Mechanization-finding reassessment

The five owner-text underdeterminations recorded by the Terminal-contract
mechanization would close under the current text, without changing that
package:

| Frozen finding | Current closure |
|---|---|
| `TERMINAL-C-MUST-ENV-CONSTRUCTORS-UNDEFINED` | lines 1472-1473 give every other term constructor empty facts |
| `TERMINAL-C-NONBOOLEAN-INPUT-MUST-UNDEFINED` | lines 1449-1450 give non-Boolean inputs empty facts in both branches |
| `TERMINAL-C-CONTRADICTION-NORMALIZATION-UNDEFINED` | lines 1474-1477 normalize opposite polarities to `Impossible` |
| `TERMINAL-C-IMPOSSIBLE-GUARD-PLACEMENT` | lines 1505-1507 make the test the first standalone Terminal-contract clause |
| `TERMINAL-C-FORWARD-STATE-TRANSFER-NOT-CLOSED-HERE` | lines 1480-1503 and 1534-1546 state `Region`, `Implies`, `Disjoint`, `ClaimStatus`, and reusable retention |

This is a source reassessment, not a refreeze of the mechanization package.
Its committed finding sequence and source pins remain owned by its follow-up
lane.

### Remaining source defect

`ClaimSource` is the sum `InitialClaim(BindingRef) |
ReductionOutput(ReductionRef, output_ordinal)` at Interaction Core lines
792-800. `Region(o)` is defined only for an occurrence at lines 1480-1486, but
`ClaimStatus(c, o)` applies it to `Source(c)` at lines 1495-1501. No helper
maps an initial binding's `Initially | BeforeOccurrence` opening or a Reduction
output to a region.

This is not a cosmetic missing name. A child scope can open before a guarded
occurrence. Its initial Claim then exists even if that occurrence's guard is
false. In the executable discriminator, the correct binding-boundary region
makes the Claim `Live` at the following fallback; coercing the source to the
guarded occurrence's region yields `Unknown`. Missing evidence therefore
cannot be converted into an affirmative Terminal result.

### Publication reconstruction

Both independent publication compilers still reconstruct the same eighteen
profiles. Relative to the pinned migration base, seventeen rotate:
`interaction`, both Fiat--Shamir families, `public-setup`,
`commitment-opening`, `oracle-commitment`, `verifier-derived-query-plan`,
`interface-plan`, all three endpoint/projection profiles, `relations`, and the
five dependent Analysis profiles. `analysis-kernel` remains the sole stable
profile. The published identity table is not written.

## Proposed delta

**Owner page and section:** `docs-next/pir/interactive-core.md`, Section 10,
immediately before `ClaimStatus`, replacing both uses of
`Region(Source(c))`.

**Exact change:** add one boundary-region helper and one typed claim-source
helper:

```text
BoundaryRegion(Initially) := {
  required_true: {}, required_false: {}, impossible: false
}
BoundaryRegion(BeforeOccurrence(o)) := {
  required_true: {},
  required_false: { Guard(t') | t' a terminal occurrence earlier than o
                                with Guard(t') not Always },
  impossible: an earlier terminal occurrence has Guard Always
}

ClaimSourceRegion(c) :=
    BoundaryRegion(ScopeDecl(PublicBindingDecl(binding).scope).opening)
      when c.source is InitialClaim(binding)
  | Region(o_r)
      when c.source is ReductionOutput(r, output_ordinal), with o_r the unique
      occurrence of ApplyReduction(r)

ClaimStatus(c, o) :=
    Live     when Implies(Region(o), ClaimSourceRegion(c))
             and Disjoint(Region(o), Region(u)) for every earlier linear
             consumer u of c
  | Dead     when Disjoint(Region(o), ClaimSourceRegion(c))
             or Implies(Region(o), Region(u)) for some earlier linear
             consumer u of c
  | Unknown  otherwise
```

Here `PublicBindingDecl(binding)` and `ScopeDecl(scope)` are exact dense-table
lookups;
the second arm retains the already validated Reduction/output backlink. The
boundary helper deliberately omits the named occurrence's own guard because
the scope opens before that guard is evaluated.

**Identity effect:** this changes the source of the Interaction core-admission
law and therefore rotates the Interaction profile and its current
seventeen-profile dependent cone; Foundation and `analysis-kernel` remain
stable if no other source changes. The Interaction manifest's law and profile
revisions require an owner audit, and both publication compilers must confirm
the final cone before publication.

**Evidence with gate identifiers:**
`F0V2C1-C-TERMINAL-CLAIM-SOURCE-REGION` and
`F0V2C1-C-OWNER-CLAIM-SOURCE-REGION`, including the binding-opening
discriminator above. The surrounding finite results have zero Region,
`Live`, or `Dead` counterexamples but do not choose the missing source map.

**Reversal condition:** withdraw this delta if the owner identifies an
existing total definition of `Source(c)` that maps both `ClaimSource` arms to
exactly these execution boundaries and the discriminator agrees. No such
definition occurs in the six migrated owner pages or executable Foundation at
this cutoff.

**Nonclaims:** this replacement is not a general reachability proof, does not
admit any exact holdout Core, does not refreeze the mechanization package, and
does not establish implementation correspondence, relation satisfaction,
theorem truth or applicability, protocol security, endpoint validity,
deployment validity, or production readiness.

## Handoff

Main should commit this working tree with subject:

```text
test: review the closed forward state and re-pin the holdouts
```

Files changed:

- `evaluation/formal-source-migration-text-review-f0v2c1/run.py`,
  `expected-findings.json`, and `README.md` extend and refreeze the seven-question
  review;
- `evaluation/formal-source-holdout-readjudication-f0v2c2/run.py`,
  `adjudication.json`, `expected-findings.json`, and `README.md` re-pin and
  re-adjudicate the holdouts;
- this note and `f0v2c2-holdout-readjudication.md` record round three; and
- `evaluation/README.md` updates the two existing inventory rows.

No owner page, check or profile manifest, lifecycle file or count pin,
publication table, directory README, real Git index, or private ledger was
edited. No package was added. The existing check-manifest claim for the
migration review still says that all seven answers are affirmative; it was
left untouched under the brief's express prohibition on manifest edits and
must be reconciled by Main or the check owner.

Validation used a clone-local alternate index and writable object store, with
this clone's read-only objects as alternates, plus a clone-local offline
dependency cache.

| Command | Exit | Wall time | Result |
|---|---:|---:|---|
| `python3 -B evaluation/formal-source-migration-text-review-f0v2c1/run.py --check` | 0 | 0.90 s | seven findings reproduced; two blocking `CannotAnswer` findings |
| `python3 -B evaluation/formal-source-holdout-readjudication-f0v2c2/run.py --check` | 0 | 0.04 s | 26 findings reproduced; five fits, three breaks, no changed verdict |
| `python3 -B evaluation/semantic-profile-publication/run.py --print-identities` | 0 | 0.35 s | both compilers reconstructed 18 profiles and the review measured the 17-profile cone |
| `python3 -B checks/run.py validate` with the alternate index | 0 | 0.05 s | 75-check, 6-tier manifest valid |
| `UV_NO_SYNC=1 UV_OFFLINE=1 UV_CACHE_DIR=$PWD/.lane-uv-cache python3 -B checks/run.py run --tier developer` with the alternate index | 0 | 1.80 s | 9 of 9 developer checks passed, including lifecycle inventory |
| `python3 -B checks/run.py run --check research.migration-text-review` with the same environment | 0 | 0.95 s | focused review check passed |
| `python3 -B checks/run.py run --check research.holdout-readjudication` with the same environment | 0 | 0.10 s | focused holdout check passed |
| `git diff --check` | 0 | under 0.1 s | no whitespace errors |

Aggregate outcome: the migration review is
`CannotAnswer/F0V2C1-C-MIGRATION-TEXT-NOT-CLOSED`; five questions are
affirmative, while Terminal-contract and owner-name closure cannot answer
until both `ClaimSource` arms have typed regions. The holdout package remains
`Affirmative/F0V2C2-A-HOLDOUTS-READJUDICATED`; five rows fit, three break,
none bend or disagree, and no represented holdout verdict changes. Four
source-specialized rows still lack exact carriers.

The five underdetermination findings from the mechanization note would close
against the current owner bytes, but that package was not edited or refrozen.
The integrated five-carrier refusal stands because reusable claim 0 is `Live`
at all fifteen terminal frontiers and is absent from the authored terminal
sets.

Nonclaims: these passes are finite, byte-pinned source-level evidence. They do
not publish an identity, prove the laws for arbitrary Core values, establish
implementation or backend correspondence, establish relation satisfaction or
theorem truth, prove a cryptographic or protocol-security property, validate
an endpoint or deployment, admit an exact holdout Core, or establish
production readiness.

Surprises: the newly closed forward state exposes a type gap not among the
five mechanization findings: `ClaimSource` is a binding-or-reduction sum while
`Region` accepts only occurrences. A guarded scope-opening discriminator makes
this semantically observable (`Live` at the boundary versus `Unknown` after
an occurrence coercion). The pre-refreeze review and holdout probes therefore
failed on stale frozen bytes before the new findings and pins were accepted;
the refrozen checks pass. One setup attempt mistakenly placed the temporary
object store under `/tmp`; it was removed, and final validation was repeated
with all temporary validation state inside this clone.

Where the brief was wrong: `AGENTS.md` and `.claude/CLAUDE.md` are absent from
this clone, so their read-only primary-checkout copies were used. The workflow
ledger append conflicts with the explicit outside-clone write prohibition and
the read-only mount, so no private ledger was changed. The sample alternate-
index procedure also requires a writable object store because this clone's
Git object directory is read-only. Finally, closing the five listed
mechanization choices does not close the seven-question review because the
new `ClaimStatus` expression introduces the separate source-region gap above.

## Round four

Round four pins the repaired Interaction Core source and reruns the same seven
questions. All seven are affirmative:

| Question | Round-three finding | Round-four finding |
|---|---|---|
| decision fidelity | `Affirmative/F0V2C1-A-DECISION-FIDELITY` | `Affirmative/F0V2C1-A-DECISION-FIDELITY` |
| Terminal contract | `CannotAnswer/F0V2C1-C-TERMINAL-CLAIM-SOURCE-REGION` | `Affirmative/F0V2C1-A-TERMINAL-CONTRACT` |
| public-coin graph | `Affirmative/F0V2C1-A-PCGRAPH-TRANSFER` | `Affirmative/F0V2C1-A-PCGRAPH-TRANSFER` |
| owner-name closure | `CannotAnswer/F0V2C1-C-OWNER-CLAIM-SOURCE-REGION` | `Affirmative/F0V2C1-A-OWNER-CLOSURE` |
| manifest closure | `Affirmative/F0V2C1-A-MANIFEST-CLOSURE` | `Affirmative/F0V2C1-A-MANIFEST-CLOSURE` |
| publication compilers | `Affirmative/F0V2C1-A-PUBLICATION-COMPILERS` | `Affirmative/F0V2C1-A-PUBLICATION-COMPILERS` |
| family-body closure | `Affirmative/F0V2C1-A-FS-BODY-CLOSURE` | `Affirmative/F0V2C1-A-FS-BODY-CLOSURE` |

The aggregate is `Affirmative/F0V2C1-A-MIGRATION-TEXT-CLOSED`.

### Claim-source repair and executable result

Interaction Core Section 10 now defines `BoundaryRegion(Initially)`,
`BoundaryRegion(BeforeOccurrence(o))`, and `ClaimSourceRegion(c)`. The initial
Claim arm follows the opening of the binding's scope. The Reduction-output arm
follows the occurrence of `ApplyReduction(r)`. Both the `Live` and `Dead` arms
of `ClaimStatus` use `ClaimSourceRegion(c)`, and the old
`Region(Source(c))` expression is absent.

The generic path oracle remains unchanged in size: 3,108 schedule/opening
variants, 11,820 occurrence regions, 47,280 attemptedness comparisons, 23,640
scope-boundary comparisons, and 18,282 claim/source/consumer cases. It reports
zero unsound `Live` or `Dead` verdicts. Its 3,320 `Unknown` cases remain useful
refusal evidence for the bounded generic corpus.

Four direct discriminators exercise every opening form and both source arms:

| Source case | Abstract result | Path reference | Pre-repair contrast |
|---|---|---|---|
| initial Claim, scope opens `Initially` | `Live` | live on 1 of 1 reaching paths | -- |
| initial Claim, scope opens before an earlier unguarded occurrence | `Live` | live on 1 of 1 reaching paths | -- |
| initial Claim, scope opens before an earlier guarded occurrence | `Live` | live on 2 of 2 reaching paths | occurrence coercion is `Unknown` |
| Reduction output at a later identically guarded terminal | `Live` | live on 1 of 1 reaching paths | -- |

The repaired boundary deliberately omits the named occurrence's own guard.
The guarded occurrence can be inactive after its deterministic scope boundary
has opened; that is exactly the case the previous formula lost.

### Frozen carriers and holdouts

The path reference separately checks 58 claim/frontier pairs across the exact
terminal projection, five integrated carriers, and represented WHIR and
WARPfold shapes. Forty-nine are `Live`, nine are `Dead`, none are `Unknown`,
and neither affirmative classification has a counterexample. The exact live
sets remain `[1]`, `[2]`, `[2]` for the terminal projection; `[0, 1, 2]` at
all fifteen integrated frontiers; WHIR has no live Claim at Accept and only
the initial Claim at fallback; WARPfold has no live Claims.

Re-pinning the holdout package changes no judgment: five rows fit, three break,
none bend, and all eight agree with the adjudication record and structural-axis
matrix. Four fitting rows still have no exact source-profile carrier, so their
exact-reference finding remains `CannotAnswer`; missing source evidence is not
turned into an owner-page defect.

### Terminal mechanization impact

The checked-in `M0.Terminal` module does **not** transcribe either the
pre-repair or repaired `Region`/`ClaimStatus` formula. It defines no Lean names
`Region`, `BoundaryRegion`, `ClaimSourceRegion`, `Implies`, `Disjoint`, or
`ClaimStatus`, and it has no theorem named as Region exactness or ClaimStatus
soundness. Instead, it enumerates abstract paths through the exact definitions
`ScheduledOccurrence`, `OpeningBefore`, `ClaimTransfer`, `ClaimEffect`,
`AbstractClaimPath`, `ForwardClaimState`, `guardBranches`,
`applyClaimTransfer`, `advanceClaimBranch`, `advanceClaimOccurrence`,
`forwardClaimsFrom`, `forwardClaims`, and `ForwardClaimState.claimsAt`, then
places the resulting lists in `TerminalView.activePathLiveClaims` for
`TerminalContract` and `terminalContractDecision`; the decision-equivalence
theorem is `terminalContractDecision_correct`.

The parallel forward-state extension is not present in this clone. If that
extension transcribed the pre-repair formula from the owner text before this
repair, it must add Lean counterparts of both `BoundaryRegion` and
`ClaimSourceRegion`, change its `ClaimStatus` definition to use the latter for
both outcomes, and restate its Region-exactness and ClaimStatus-soundness
theorems over the typed source map. No exact names for those parallel-only
definitions or theorems are visible here, so this review does not invent them
or edit the mechanization package.

### Publication reconstruction

Both publication compilers reconstruct the same eighteen-profile table.
Relative to the pinned migration base, the seventeen-profile rotated cone is:
`interaction`, `canonical-framed-fiat-shamir`,
`duplex-sponge-fiat-shamir`, `public-setup`, `commitment-opening`,
`oracle-commitment`, `verifier-derived-query-plan`, `interface-plan`,
`oir-endpoint-graph`, `endpoint-source-view`, `oir-projection-relation`,
`relations`, `analysis-cryptographic-property`, `analysis-afk-transport`,
`analysis-afk-theorem-source-validation`,
`analysis-incremental-composition`, and
`analysis-incremental-composition-source-validation`. `analysis-kernel` is the
sole stable profile, Foundation is unchanged, and the publication table is not
written.

### Proposed delta

None. The repaired owner text answers the two round-three findings. This review
does not propose another owner-page change.

## Handoff

Main should commit this working tree with subject:

```text
test: review the claim-source regions and re-pin the holdouts
```

Files changed, validation, aggregate outcome, nonclaims, surprises, and brief
corrections follow.

### Files changed

- `evaluation/formal-source-migration-text-review-f0v2c1/run.py`,
  `expected-findings.json`, and `README.md`: exercise all four Claim-source
  discriminators, compare the frozen carriers to the path-enumerating
  reference, enforce the repaired owner wording, and freeze seven affirmative
  findings.
- `evaluation/formal-source-holdout-readjudication-f0v2c2/run.py`,
  `adjudication.json`, `expected-findings.json`, and `README.md`: re-pin the
  current owner and support pages and freeze all eight holdout verdicts without
  changing any verdict.
- `evaluation/README.md`: update the two existing package rows to their
  round-four summaries.
- This note and `f0v2c2-holdout-readjudication.md`: record the fourth-round
  evidence, mechanization impact, publication cone, and holdout
  re-adjudication.

No owner page, package manifest, lifecycle inventory, lifecycle count pin, or
mechanization file changed. No package was added. Main still owns the manifest
description update and note registration.

### Validation

The lifecycle-sensitive checks used a clone-local alternate index and writable
object store containing all ten changed tracked files. The global cache was not
used.

| Command | Exit | Wall time | Result |
|---|---:|---:|---|
| `python3 -B checks/run.py validate` | 0 | 0.04 s | manifest valid: 76 checks, 6 tiers |
| `python3 -B checks/run.py run --tier developer` with offline, no-sync, clone-local cache settings | 0 | 1.84 s | 9 of 9 checks passed, including lifecycle inventory |
| `python3 -B checks/run.py run --check research.migration-text-review` | 0 | 0.96 s | focused wrapper passed |
| `python3 -B checks/run.py run --check research.holdout-readjudication` | 0 | 0.10 s | focused wrapper passed |
| `python3 -B evaluation/formal-source-migration-text-review-f0v2c1/run.py --check` | 0 | 0.90 s | seven frozen findings matched |
| `python3 -B evaluation/formal-source-holdout-readjudication-f0v2c2/run.py --check` | 0 | 0.04 s | twenty-six frozen findings matched |
| `python3 -B evaluation/semantic-profile-publication/run.py --print-identities` | 0 | 0.35 s | both compilers agreed on all 18 identities |
| `git diff --check` | 0 | 0.08 s | no whitespace errors |

The two focused wrappers were also started once concurrently; both exited 0,
but their timestamp-based result paths collided. The sequential wrapper runs
reported above produced distinct result artifacts.

### Aggregate outcome

- Migration review: `Affirmative / F0V2C1-A-MIGRATION-TEXT-CLOSED`; all seven
  exact questions close under `ClaimSourceRegion`.
- Holdout re-adjudication: `Affirmative /
  F0V2C2-A-HOLDOUTS-READJUDICATED`; every row has a frozen verdict and no
  verdict changes.
- Publication reconstruction: both compilers agree; 17 profiles rotate and
  `analysis-kernel` alone remains stable.

### Nonclaims

These finite path enumerations and frozen carriers establish neither universal
PIR semantics nor theorem truth, cryptographic security, backend correctness,
or production readiness. An affirmative holdout aggregate means that every row
was re-adjudicated, not that every protocol fits: three rows still break, and
four fitting rows still lack exact source-profile carriers. The mechanization
assessment covers only the checked-in module in this clone, not unseen parallel
work.

### Surprises and corrections to the brief

- This clone does not contain `AGENTS.md` or `.claude/CLAUDE.md`; their
  read-only primary-checkout copies supplied the required instructions.
- The checked-in Terminal-contract mechanization does not transcribe the
  pre-repair `ClaimStatus` formula and names no Region-exactness or
  ClaimStatus-soundness theorem. The requested transcription warning therefore
  applies conditionally to the unseen parallel extension, not to the current
  package.
- The holdout package's migration-record support pin had also rotated after
  round three; it was re-pinned along with the repaired owner page.
- The alternate index needed a clone-local writable object directory because
  every `.git` directory is read-only.
- The brief intentionally leaves the round-three manifest claim to Main; this
  lane did not edit it. The workflow's private-status append was also not made
  because the brief expressly forbids writes outside this clone.

## Round five

Round five re-runs the seven round-four questions and adds reference-leaf
closure and static-view law-field selection. The frozen result is eight
affirmative findings and one `CannotAnswer`:

| Question | Round-five finding |
|---|---|
| decision fidelity | `Affirmative/F0V2C1-A-DECISION-FIDELITY` |
| Terminal contract | `Affirmative/F0V2C1-A-TERMINAL-CONTRACT` |
| public-coin graph | `Affirmative/F0V2C1-A-PCGRAPH-TRANSFER` |
| owner-name closure | `Affirmative/F0V2C1-A-OWNER-CLOSURE` |
| manifest closure | `Affirmative/F0V2C1-A-MANIFEST-CLOSURE` |
| publication compilers | `Affirmative/F0V2C1-A-PUBLICATION-COMPILERS` |
| family-body closure | `Affirmative/F0V2C1-A-FS-BODY-CLOSURE` |
| reference-leaf closure | `CannotAnswer/F0V2C1-C-PIR-REFERENCE-CLOSURE` |
| static-view law-field selection | `Affirmative/F0V2C1-A-STATIC-VIEW-LAW-SELECTION` |

The aggregate is
`CannotAnswer/F0V2C1-C-MIGRATION-TEXT-NOT-CLOSED`, with only
`pir-reference-closure` blocking. The round-four answers do not change.

### Reference-leaf closure

The common union at `docs-next/pir/interactive-core.md:2251-2256` contains all
fourteen Core-local dense-ordinal reference types, `ValueRef`, and
`ProtocolDeclarationRef<K>` only for the nine declaration kinds listed at
lines 111-118. Its body at lines 2258-2262 delegates those three classes to
the dense ordinal, `ValueRefBody`, and `ModuleDeclarationRefBody` encodings.
`PIRProfileLawReference` and `AdmittedModuleEffect` have separate atomic arms,
and a portable algorithm identity closes to its exact byte identity.

One family-view leaf is outside that closed union. The canonical-framed page
recognizes `ProtocolDeclarationRef<"pir.fs-application-domain">` at lines
68-71 and uses it as `TranscriptDeclarationViewBody.application_domain` at
line 1276. The kind is not among the nine Interaction Section 2 kinds, so the
value is not a `PIRReference`; it is also neither a
`PIRProfileLawReference` nor an `AdmittedModuleEffect`. It therefore falls
outside every arm of `PIRViewAtomicBoundary` displayed at Interaction line
2264-2267. `ModuleDeclarationRefBody` could encode the reference, but the
declared boundary never reaches that delegation. No second uncovered leaf was
found.

### Static-view law-field selection

All law-valued fields in the three profiles have exactly one table entry:

| Profile | Displayed fields | Table entries | Imported entries | New declarations | Pre-existing ordinals checked |
|---|---:|---:|---:|---:|---:|
| Interaction | 5 | 5 | 0 | 3 | 10 |
| canonical-framed Fiat--Shamir | 13 | 13 | 2 | 2 | 5 |
| duplex-sponge Fiat--Shamir | 17 | 17 | 2 | 4 | 5 |
| total | 35 | 35 | 4 | 9 | 20 |

Every selected coordinate names one `pir.semantic-law` declaration at a
determinate catalog ordinal. Each of the four imported Interaction laws has a
matching declaration dependency on the consuming execution-view schema. No
pre-existing law moved from its prior ordinal.

The nine new selectors occur exactly once inside their selected fragments:

| Owner page | Declaration selectors and lines |
|---|---|
| `interactive-core.md` | `VisibleHistory` 1232; `ProverView` 1274; `ReplayRun` 2102 |
| `fiat-shamir.md` | protocol execution 998; replay 1023 |
| `duplex-sponge-fiat-shamir.md` | protocol execution 644; replay 657; prover-required prefix 675; same-Core construction 729 |

The three manifests are at profile revision 2. Their new law declarations
remain at declaration revision 0; the schemas and schema-resolution law whose
selected source changed are at declaration revision 1. Across all eight
migrated manifests, 116 declarations and 55 subjects resolve, the two
family-local declaration components remain twelve nodes and twenty internal
edges, and the selected revision census is 21 transitions plus 49 new
revision-zero declarations.

### Holdout re-adjudication

The holdout package is re-pinned to the three changed owner pages and the
current migration record, and its owner-section citations are refreshed. All
eight rows agree with both comparison sources: five fit, three break, none
bend, and none disagree. The represented WHIR and WARPfold frontiers still
produce no `Unknown` claim state and no verdict change. The aggregate remains
`Affirmative/F0V2C2-A-HOLDOUTS-READJUDICATED` because every row has a frozen
verdict.

The canonical family-view reference defect is also recorded in that package
as `CannotAnswer/F0V2C2-C-FAMILY-VIEW-REFERENCE-BOUNDARY`. It limits complete
family-view transport, but it neither supplies nor removes a protocol
coordinate and therefore does not alter any holdout verdict. The four
source-specialized fitting rows separately remain `CannotAnswer` for exact
terminal carriers.

### Publication reconstruction

The reference and independent publication compilers both accept all eighteen
profiles, including the three revision-2 manifests and their nine new law
declarations, and reproduce the same identity table. Relative to the pinned
migration base, the cone still rotates seventeen profiles:
`interaction`, `canonical-framed-fiat-shamir`,
`duplex-sponge-fiat-shamir`, `public-setup`, `commitment-opening`,
`oracle-commitment`, `verifier-derived-query-plan`, `interface-plan`,
`oir-endpoint-graph`, `endpoint-source-view`, `oir-projection-relation`,
`relations`, `analysis-cryptographic-property`, `analysis-afk-transport`,
`analysis-afk-theorem-source-validation`,
`analysis-incremental-composition`, and
`analysis-incremental-composition-source-validation`. `analysis-kernel` alone
is stable, Foundation is unchanged, and no publication table is written.

### Proposed delta

- Owner page and section: `docs-next/pir/interactive-core.md`, Section 13.1,
  lines 2251-2267.
- Exact change: after the existing Section 2 declaration-kind arm in
  `PIRReference`, add the disjoint arm
  `ProtocolDeclarationRef<"pir.fs-application-domain">`. Leave
  `PIRReferenceBody` unchanged because its `ModuleDeclarationRefBody`
  delegation already covers the added reference body.
- Identity effect: an in-memory candidate compiled by both publication
  compilers rotates `interaction` and its fifteen current dependents. The
  sixteen-profile cone is `interaction`, both Fiat--Shamir profiles,
  `public-setup`, `commitment-opening`, `oracle-commitment`,
  `verifier-derived-query-plan`, `interface-plan`, `endpoint-source-view`,
  `oir-projection-relation`, `relations`, the four AFK/incremental Analysis
  consumers, and `analysis-cryptographic-property`;
  `oir-endpoint-graph` and `analysis-kernel` remain stable. This is the
  incremental effect against the current head, not the seventeen-profile
  migration-base cone above.
- Evidence: `research.migration-text-review` isolates the uncovered leaf and
  `research.profile-publication` supplies the two compiler implementations;
  the candidate probe reports identical sixteen-profile cones.
- Reversal condition: withdraw this delta if the canonical transcript view no
  longer uses the application-domain declaration reference, or if an owner
  defines another exact atomic arm and body delegation that carries this same
  leaf without broadening consumer authority.
- Nonclaims: the delta does not select application-domain semantics, prove any
  Fiat--Shamir theorem or security property, publish an identity, establish
  implementation correspondence, or authorize deployment.

## Handoff

Main should commit this working tree with subject:

```text
test: review the static-view law selection and re-pin the holdouts
```

### Files changed

- `evaluation/formal-source-migration-text-review-f0v2c1/run.py`,
  `expected-findings.json`, and `README.md` add the two round-five questions,
  freeze the 35-field selection audit, and retain the reference defect as
  `CannotAnswer`.
- `evaluation/formal-source-holdout-readjudication-f0v2c2/run.py`,
  `adjudication.json`, `expected-findings.json`, and `README.md` re-pin the
  sources, refresh line citations, retain all eight verdicts, and record the
  bounded family-view reference limitation.
- `checks/manifest.json` and `evaluation/README.md` update the two existing
  package registrations without adding a package.
- This note and `f0v2c2-holdout-readjudication.md` record round five and the
  handoff.

No owner page, profile manifest, directory README, lifecycle inventory,
lifecycle count pin, publication table, real Git index, private ledger, or
mechanization file was edited. No package was added.

### Validation

The lifecycle-sensitive commands used `.lane-index`, a clone-local writable
object store, the read-only checkout objects as alternates, and a clone-local
offline dependency cache.

| Command | Exit | Wall time | Result |
|---|---:|---:|---|
| pre-edit migration review | 1 | 0.27 s | stale manifest revision pin detected |
| pre-edit holdout `--check` | 1 | 0.04 s | stale owner and support pins detected; verdict aggregate already unchanged |
| `python3 -B evaluation/formal-source-migration-text-review-f0v2c1/run.py --check` | 0 | 0.93 s | nine frozen findings reproduced; one blocking `CannotAnswer` |
| `python3 -B evaluation/formal-source-holdout-readjudication-f0v2c2/run.py --check` | 0 | 0.04 s | twenty-six findings reproduced; five fits, three breaks, zero verdict changes |
| `python3 -B evaluation/semantic-profile-publication/run.py --print-identities` | 0 | 0.36 s | both compilers accepted all eighteen manifests and emitted one identity table |
| in-memory proposed-delta compilation with both publication compilers | 0 | 0.55 s | both measured the same sixteen-profile incremental cone |
| `python3 -B checks/run.py validate` with the alternate index | 0 | 0.04 s | 76-check, 6-tier manifest valid |
| first developer-tier attempt | 1 | 0.35 s | control-plane check exposed the temporarily overwritten holdout expected findings; later checks did not run |
| `python3 -B checks/run.py run --tier developer` with the final alternate index and offline cache | 0 | 1.78 s | 9 of 9 developer checks passed, including lifecycle inventory |
| `python3 -B checks/run.py run --check research.migration-text-review` with the same environment | 0 | 1.01 s | focused review wrapper passed |
| `python3 -B checks/run.py run --check research.holdout-readjudication` with the same environment | 0 | 0.10 s | focused holdout wrapper passed |
| `git diff --check` | 0 | 0.01 s | no whitespace errors |

### Aggregate outcome

- Migration review: `CannotAnswer/F0V2C1-C-MIGRATION-TEXT-NOT-CLOSED`; eight
  questions are affirmative and only the application-domain reference leaf is
  outside the atomic boundary.
- Holdout readjudication:
  `Affirmative/F0V2C2-A-HOLDOUTS-READJUDICATED`; all eight verdicts are frozen
  and none changes.
- Publication reconstruction: both compilers agree on all eighteen profiles;
  the migration-base cone contains seventeen profiles and the current-head
  proposed-delta cone contains sixteen.

### Nonclaims

These byte-pinned source checks do not repair or publish owner text, prove the
owner laws for arbitrary values, establish implementation or backend
correspondence, establish relation satisfaction or theorem truth, prove a
cryptographic or protocol-security property, validate an endpoint or
deployment, admit an exact holdout Core, or establish production readiness.
An affirmative holdout aggregate says every row was re-adjudicated, not that
every protocol fits or every family-view leaf closes.

### Surprises and corrections to the brief

- The two repair commits close all 35 law-field selections but do not close the
  application-domain reference leaf introduced by the already normalized
  canonical transcript view.
- The proposed one-arm owner change has a sixteen-profile incremental cone;
  `oir-endpoint-graph` is stable. The seventeen-profile cone in the brief is
  the larger migration-base comparison, not this candidate's current-head
  effect.
- This clone does not contain `AGENTS.md` or `.claude/CLAUDE.md`; their
  read-only primary-checkout copies supplied the required instructions.
- The workflow's private status-ledger append conflicts with the express
  outside-clone write prohibition and read-only mount, so no private ledger was
  changed. The alternate index also needs a clone-local writable object store
  because this clone's Git object directory is read-only.
- A preliminary JSON-format validation accidentally supplied two input paths
  to `json.tool`; the second path was treated as an output and temporarily
  overwrote the holdout expected-findings file. It was regenerated through
  `apply_patch` before the successful developer-tier run. Three transient JSON
  and log files were also mistakenly written under `/tmp`; all three were
  removed, and no outside-clone artifact remains.

## Round six

### Exact question and result

Does the migrated PIR owner text close the nine independent freeze-review
questions for decision fidelity, the Terminal contract, public-coin graph
transfers and sinks, owner-view closure, manifest closure, publication
reconstruction, family-view body closure, reference-leaf closure, and
static-view law-field selection?

Yes, for the exact pinned pages and manifests. All nine findings are now
affirmative, so the aggregate is
`Affirmative/F0V2C1-A-MIGRATION-TEXT-CLOSED`.

| Finding | Outcome and stable code |
|---|---|
| decision fidelity | `Affirmative/F0V2C1-A-DECISION-FIDELITY` |
| Terminal contract | `Affirmative/F0V2C1-A-TERMINAL-CONTRACT` |
| public-coin graph | `Affirmative/F0V2C1-A-PCGRAPH-TRANSFER` |
| owner-name closure | `Affirmative/F0V2C1-A-OWNER-CLOSURE` |
| manifest closure | `Affirmative/F0V2C1-A-MANIFEST-CLOSURE` |
| publication compilers | `Affirmative/F0V2C1-A-PUBLICATION-COMPILERS` |
| family-body closure | `Affirmative/F0V2C1-A-FS-BODY-CLOSURE` |
| reference-leaf closure | `Affirmative/F0V2C1-A-PIR-REFERENCE-CLOSURE` |
| static-view law selection | `Affirmative/F0V2C1-A-STATIC-VIEW-LAW-SELECTION` |

### Profile-relative reference closure

The repaired arm at `docs-next/pir/interactive-core.md:2256-2259` admits a
`ProtocolDeclarationRef<K>` exactly when the selected profile's exact-used
owner-module closure recognizes `K`. `PIRReferenceBody` remains closed under
the selected profile at lines 2261-2266, and `PIRViewAtomicBoundary` displays
the `PIRReference` arm at lines 2268-2271.

The recognized declaration-kind set is determinate for each selected profile
from the owner pages alone:

| Profile | Recognized declaration kinds | Declaring page lines |
|---|---|---|
| Interaction | `pir.message-channel`, `pir.challenge-domain`, `pir.public-coin-law`, `pir.coin-correlation-group`, `pir.challenge-sharing-contract`, `pir.claim-contract`, `pir.reduction-contract`, `pir.oracle-binding-contract`, `pir.oracle-domain-law` | `docs-next/pir/interactive-core.md:111-118` |
| canonical-framed Fiat--Shamir | the nine Interaction kinds plus `pir.fs-application-domain` | the family kind is declared at `docs-next/pir/fiat-shamir.md:68-71`; the exact Interaction import is at lines 73-74 |
| duplex-sponge Fiat--Shamir | the nine Interaction kinds, with no family-added declaration kind | the exact Interaction import is at `docs-next/pir/duplex-sponge-fiat-shamir.md:58`; the declaration catalog is listed at lines 68-71 and the no-extra closure at lines 73-76 |

The checker now parses the text-code definitions, recursively follows every
owner-defined type alias reachable from all sixteen static-view bodies, and
classifies every reference-typed leaf occurrence. Exact Message and Oracle
declarations are expanded through their owner aliases; runtime-schema prose is
kept atomic rather than mistaken for an embedded static-view value.

| Profile | Static views | Reference-leaf occurrences | Uncovered or multi-arm leaves |
|---|---:|---:|---:|
| Interaction | 6 | 279 | 0 |
| canonical-framed Fiat--Shamir | 5 | 36 | 0 |
| duplex-sponge Fiat--Shamir | 5 | 71 | 0 |
| total | 16 | 386 | 0 |

The arm census is 332 `PIRReference` occurrences, 35
`PIRProfileLawReference` occurrences, two `AdmittedModuleEffect` occurrences,
and seventeen `Bytes` occurrences reached through exact portable-algorithm
identity bodies. The ten declaration-reference kinds reached by the views are
the nine Interaction kinds and the canonical family kind. Every such leaf is
recognized by its selected profile and takes exactly the `PIRReference` arm.
No declaration kind is used without a page-level recognition statement.

The complete ordered census is frozen by SHA-256
`58ea5d029502ca5c01d784dbb0cdfe1769129f928d49c089f4019195c891dd7e`;
the complete review metrics, including the census preimage, source hashes, and
all prior bounded experiments, are frozen by SHA-256
`59a5c7fb539dfc8ea60c28e4e3a256002a9e0b8e9b43b1180cd6ed69cc43778b`.

### Holdout re-adjudication

The holdout package is re-pinned to the current owner pages and migration
record, and its owner-section citations move with the four added lines. All
eight rows agree again with the adjudication record and structural-axes
matrix: five fit, three break, none bend, and none disagree. No verdict
changes. The verdict aggregate remains
`Affirmative/F0V2C2-A-HOLDOUTS-READJUDICATED`.

The canonical family-view boundary changes from `CannotAnswer` to
`Affirmative/F0V2C2-A-FAMILY-VIEW-REFERENCE-BOUNDARY`: the application-domain
leaf at `docs-next/pir/fiat-shamir.md:1276` is recognized by that family page
at line 69 and is carried by the repaired generic arm. The four
source-specialized fitting rows separately remain
`CannotAnswer/F0V2C2-C-EXACT-TERMINAL-CARRIERS`; no exact source profile was
invented for them, and that bounded source gap does not change a verdict.

### Publication reconstruction

The reference and independent publication compilers agree on all eighteen
profiles and emit one identity table without writing the publication table.
Relative to the pinned migration base, the exact rotation cone remains these
seventeen profiles: `interaction`, `canonical-framed-fiat-shamir`,
`duplex-sponge-fiat-shamir`, `public-setup`, `commitment-opening`,
`oracle-commitment`, `verifier-derived-query-plan`, `interface-plan`,
`oir-endpoint-graph`, `endpoint-source-view`, `oir-projection-relation`,
`relations`, `analysis-cryptographic-property`, `analysis-afk-transport`,
`analysis-afk-theorem-source-validation`,
`analysis-incremental-composition`, and
`analysis-incremental-composition-source-validation`. `analysis-kernel` alone
is stable, and Foundation is unchanged.

### Owner-page delta status

The round-five proposed delta is satisfied by the current generic,
profile-relative arm and is no longer a live proposal. This lane proposes no
new owner-page change and edits no owner page.

## Handoff

Main should commit this working tree with subject:

```text
test: review the reference atom's profile closure and re-pin the holdouts
```

### Files changed

- `evaluation/formal-source-migration-text-review-f0v2c1/run.py`,
  `expected-findings.json`, and `README.md` replace the direct-leaf spot check
  with a recursive sixteen-view census, freeze all nine affirmative findings,
  and document the three determinate recognized-kind sets.
- `evaluation/formal-source-holdout-readjudication-f0v2c2/run.py`,
  `adjudication.json`, `expected-findings.json`, and `README.md` re-pin the
  current pages, refresh shifted citations, and change only the family-view
  reference-boundary finding to affirmative. The eight verdicts do not change.
- `evaluation/README.md` refreshes the two existing package rows.
- This note and `f0v2c2-holdout-readjudication.md` record round six.

No owner page, profile manifest, check manifest, directory README, lifecycle
inventory, lifecycle count pin, publication table, real Git index, private
ledger, or mechanization file was edited. No package was added. No commit,
push, or pull request was attempted.

### Validation

The lifecycle-sensitive commands used `.lane-index`, a clone-local writable
object store, the checkout objects as read-only alternates, and a clone-local
offline dependency cache. The alternate index and temporary object/cache
directories were removed after the checks.

| Command | Exit | Wall time | Result |
|---|---:|---:|---|
| required owner diff inspection | 0 | under 0.1 s | confirmed only the profile-relative declaration arm and its closure wording changed |
| pre-edit migration review `--check` | 1 | 0.06 s | old arm-shape expectation refused the repaired owner text |
| pre-edit holdout `--check` | 1 | 0.04 s | old owner/support pins and frozen boundary finding drifted |
| `python3 -B evaluation/formal-source-migration-text-review-f0v2c1/run.py --check` | 0 | 0.97 s | nine of nine findings affirmative; no blocker |
| `python3 -B evaluation/formal-source-holdout-readjudication-f0v2c2/run.py --check` | 0 | 0.04 s | twenty-six findings reproduced; five fits, three breaks, zero verdict changes |
| `python3 -B evaluation/semantic-profile-publication/run.py --print-identities` | 0 | 0.36 s | both compilers agreed on eighteen profiles and one table without writing it |
| `python3 -B checks/run.py validate` with the alternate index | 0 | 0.05 s | 76-check, 6-tier manifest valid |
| `python3 -B checks/run.py run --tier developer` with the final alternate index and offline cache | 0 | 1.81 s | 9 of 9 developer checks passed, including lifecycle inventory |
| `python3 -B checks/run.py run --check research.migration-text-review` with the same environment | 0 | 1.04 s | focused review wrapper passed |
| `python3 -B checks/run.py run --check research.holdout-readjudication` with the same environment | 0 | 0.10 s | focused holdout wrapper passed |
| `git diff --check` | 0 | under 0.1 s | no whitespace errors |

### Aggregate outcome

- Migration review: `Affirmative/F0V2C1-A-MIGRATION-TEXT-CLOSED`; all nine
  questions close. All 386 recursively reached reference-leaf occurrences
  take exactly one atomic-boundary arm.
- Holdout readjudication:
  `Affirmative/F0V2C2-A-HOLDOUTS-READJUDICATED`; all eight verdicts remain
  frozen and none changes. The canonical family-view reference-boundary
  finding is now affirmative. Four exact source-specialized terminal carriers
  remain `CannotAnswer` without affecting the verdict aggregate.
- Publication reconstruction: both compilers agree on all eighteen profiles;
  the migration-base cone contains seventeen profiles and only
  `analysis-kernel` is stable.

### Nonclaims

These byte-pinned source checks do not publish owner text or identities, prove
the owner laws for arbitrary values, establish implementation or backend
correspondence, establish relation satisfaction or theorem truth, prove a
cryptographic or protocol-security property, validate an endpoint or
deployment, admit an exact holdout Core, or establish production readiness.
The reference result does not choose the semantics of a nominal declaration or
cover an unlisted future profile. The affirmative holdout aggregate says every
row was re-adjudicated with a frozen verdict, not that every protocol fits.

### Surprises and corrections to the brief

- This clone does not contain `AGENTS.md` or `.claude/CLAUDE.md`; their
  read-only primary-checkout copies supplied the required instructions.
- The general package discipline requests a manifest entry, while the
  task-specific instruction forbids manifest edits. No package was added, so
  the existing entries were retained. Their human-readable claims still state
  the round-five result and must not be read as round-six metadata.
- The workflow's private status-ledger append conflicts with the express
  outside-clone write prohibition and read-only mount, so no private ledger was
  changed.
- Under this read-only Git mount, the example alternate-index command also
  needs a clone-local writable object store. Because the index itself sits
  inside the worktree, the first `git add -A` staged `.lane-index` and its
  transient lock; an initial cached removal exited 1, and the explicit forced
  cached removal succeeded without touching the real index or worktree files.
- The command sandbox rejected the first explicit `rm -f` cleanup command
  before execution. A nonrecursive `unlink` for the index and depth-first
  deletion of the two exact temporary directories completed the cleanup.
- The lifecycle count pins do not move: this round updates two existing
  packages and adds none.

## Round seven

### Exact question and result

Does the current migrated PIR text close the nine round-six questions and a
tenth declaration-body question: for every declaration kind recognized by the
Interaction page or added by a family page, does exactly one owner page state
its body, and does the owner corpus classify a malformed body shape, with the
recognition and body lines identified exactly?

Yes, for the exact pinned pages and manifests. All ten findings are
affirmative, so the aggregate remains
`Affirmative/F0V2C1-A-MIGRATION-TEXT-CLOSED`.

| Finding | Outcome and stable code |
|---|---|
| decision fidelity | `Affirmative/F0V2C1-A-DECISION-FIDELITY` |
| Terminal contract | `Affirmative/F0V2C1-A-TERMINAL-CONTRACT` |
| public-coin graph | `Affirmative/F0V2C1-A-PCGRAPH-TRANSFER` |
| owner-name closure | `Affirmative/F0V2C1-A-OWNER-CLOSURE` |
| manifest closure | `Affirmative/F0V2C1-A-MANIFEST-CLOSURE` |
| publication compilers | `Affirmative/F0V2C1-A-PUBLICATION-COMPILERS` |
| family-body closure | `Affirmative/F0V2C1-A-FS-BODY-CLOSURE` |
| reference-leaf closure | `Affirmative/F0V2C1-A-PIR-REFERENCE-CLOSURE` |
| static-view law selection | `Affirmative/F0V2C1-A-STATIC-VIEW-LAW-SELECTION` |
| declaration-body closure | `Affirmative/F0V2C1-A-DECLARATION-BODY-CLOSURE` |

### Declaration-body closure

The three profiles have 28 inherited-or-local kind instances but ten unique
declaration kinds. Each unique kind resolves to exactly one body-owner page:

| Declaration kind | Recognition | Exact body and admission | Malformed shape |
|---|---|---|---|
| `pir.message-channel` | `docs-next/pir/interactive-core.md:113` | `NominalProtocolDeclarationBody`, lines 106-108; association lines 111-116 | common Foundation formation law, `docs-next/foundation/executable-foundations.md:2042` |
| `pir.challenge-domain` | `docs-next/pir/interactive-core.md:113` | `NominalProtocolDeclarationBody`, lines 106-108; association lines 111-116 | common Foundation formation law, line 2042 |
| `pir.public-coin-law` | `docs-next/pir/interactive-core.md:114` | `NominalProtocolDeclarationBody`, lines 106-108; association lines 111-116 | common Foundation formation law, line 2042 |
| `pir.coin-correlation-group` | `docs-next/pir/interactive-core.md:114` | `NominalProtocolDeclarationBody`, lines 106-108; association lines 111-116 | common Foundation formation law, line 2042 |
| `pir.challenge-sharing-contract` | `docs-next/pir/interactive-core.md:115` | `NominalProtocolDeclarationBody`, lines 106-108; association lines 111-116 | common Foundation formation law, line 2042 |
| `pir.claim-contract` | `docs-next/pir/interactive-core.md:115` | `NominalProtocolDeclarationBody`, lines 106-108; association lines 111-116 | common Foundation formation law, line 2042 |
| `pir.reduction-contract` | `docs-next/pir/interactive-core.md:116` | `NominalProtocolDeclarationBody`, lines 106-108; association lines 111-116 | common Foundation formation law, line 2042 |
| `pir.oracle-binding-contract` | `docs-next/pir/interactive-core.md:116` | `NominalProtocolDeclarationBody`, lines 106-108; association lines 111-116 | common Foundation formation law, line 2042 |
| `pir.oracle-domain-law` | `docs-next/pir/interactive-core.md:117-118` | exact body and owner admission at lines 1011-1038; canonical body at lines 3807-3810 | common Foundation formation law, line 2042 |
| `pir.fs-application-domain` | `docs-next/pir/fiat-shamir.md:68-69` | exact nominal body and reference treatment at lines 70-76 | kind-local classification at line 73, plus the common Foundation formation law at line 2042 |

The common Foundation rule is the constitutional formation owner for every
recognized declaration kind: strict decoding into the kind's exact body
grammar precedes owner admission, and a wrong constructor, tag, record field
set or order, or field carrier is `Malformed`. The review pins that shared
owner line rather than demanding that each PIR body repeat it. The
canonical-framed page additionally states the classification locally.

The checker records an absent body as a missing row carrying the exact
recognition page and line, and a missing or multiply owned body makes this
finding `CannotAnswer`. No such row exists in the current census. The new
canonical-framed paragraph closes the gap that the finite executor had exposed:
its application-domain kind now uses one nonempty semantic symbol and no other
field, and the reference continues to use `ModuleDeclarationRefBody`.

### Prior questions, holdouts, and publication cone

The nine prior questions remain affirmative. The recursive static-view census
still contains 386 reference leaves across sixteen views, all classified under
exactly one atomic arm. The inserted canonical paragraph only shifts source
coordinates: the census preimage digest is now
`3facfabc9e00dfb3eea54baf11ca30aae987b89e08cdef640ad22ecfa5850298`.
The complete review metrics are frozen at
`6c432a5a75c25556aded439aa70acb853da0735d2a890705e18ec8b06de3c817`.

The holdout package is re-pinned to the current five owner pages and migration
record. All eight rows retain their verdicts: five fit, three break, none bend,
and none disagree. The represented WHIR and WARPfold frontiers still produce
zero `Unknown` claim states and zero verdict changes. The aggregate remains
`Affirmative/F0V2C2-A-HOLDOUTS-READJUDICATED`; the four source-specialized
fitting rows separately retain
`CannotAnswer/F0V2C2-C-EXACT-TERMINAL-CARRIERS`.

The reference and independently implemented publication compilers agree on
all eighteen current profiles and on the migration-base comparison. The cone
still rotates `interaction`, `canonical-framed-fiat-shamir`,
`duplex-sponge-fiat-shamir`, `public-setup`, `commitment-opening`,
`oracle-commitment`, `verifier-derived-query-plan`, `interface-plan`,
`oir-endpoint-graph`, `endpoint-source-view`, `oir-projection-relation`,
`relations`, `analysis-cryptographic-property`, `analysis-afk-transport`,
`analysis-afk-theorem-source-validation`,
`analysis-incremental-composition`, and
`analysis-incremental-composition-source-validation`. `analysis-kernel` alone
is stable, Foundation is unchanged, and no publication table is written.

### Proposed delta

None. The current owner text closes the declaration-body question, so this
lane proposes no owner-page change and edits no owner page.

## Handoff

Main should commit this complete working tree with subject:

```text
test: review the declaration bodies and re-pin the holdouts
```

### Files changed

- `evaluation/formal-source-migration-text-review-f0v2c1/run.py`,
  `expected-findings.json`, and `README.md` add and freeze the tenth question,
  pin the common declaration-formation owner, and refresh shifted family-page
  coordinates.
- `evaluation/formal-source-holdout-readjudication-f0v2c2/run.py`,
  `adjudication.json`, `expected-findings.json`, and `README.md` re-pin the
  current owner and support bytes, require the newly fixed declaration body,
  and refresh exact citations without changing any verdict finding.
- `evaluation/README.md` refreshes the two current package rows.
- This note and `f0v2c2-holdout-readjudication.md` record round seven.

No owner page, profile manifest, check manifest, directory README, lifecycle
catalog, lifecycle count pin, publication table, real Git index, private
ledger, or mechanization file was edited. No package was added. No commit,
push, or pull request was attempted.

### Validation

The lifecycle-sensitive commands used `.lane-index`, a clone-local writable
object store, the checkout objects as read-only alternates, and a clone-local
offline dependency cache. The alternate index and temporary object/cache
directories were removed after the checks.

| Command | Exit | Wall time | Result |
|---|---:|---:|---|
| required owner diff inspection | 0 | under 0.1 s | confirmed that the canonical-framed page now fixes the exact nominal body, rejects every other shape as malformed, and retains the existing reference body |
| pre-edit migration review `--check` | 1 | 0.07 s | the round-six import-line expectation refused the shifted current page |
| pre-edit holdout `--check` | 1 | 0.04 s | the old owner/support pins and frozen projection drifted while all eight verdict comparisons still agreed |
| pre-edit publication identity print | 0 | 0.34 s | both compilers agreed on eighteen current profiles without writing the table |
| final migration review package `--check` | 0 | 1.05 s | reproduced ten findings, all affirmative, with no blocker |
| final holdout package `--check` | 0 | 0.04 s | reproduced all 26 frozen findings and the affirmative verdict aggregate |
| publication identity print | 0 | 0.35 s | reference and independent compilers agreed on all eighteen current identities |
| diagnostic publication package `--check` | 1 | 3.59 s | both compilers agreed, then seven legacy-publication assertions correctly detected that the current rotation cone is not the published table |
| `python3 -B checks/run.py validate` with the alternate index | 0 | 0.04 s | validated 77 checks across six tiers; manifest digest `7416551c402f3c60e88e5b3704f762c80a466c6a0b95614eeef19667bb7c3587` |
| `python3 -B checks/run.py run --tier developer` with the alternate index and offline cache | 0 | 1.76 s | all nine developer checks passed |
| focused review wrapper with the same environment | 0 | 1.12 s | `research.migration-text-review` passed |
| focused holdout wrapper with the same environment | 0 | 0.10 s | `research.holdout-readjudication` passed |
| Python/JSON parse and `git diff --check` | 0 | 0.04 s and 0.06 s | compiled both changed Python files, parsed all three changed JSON files, and found no whitespace errors |

### Aggregate outcome

- Migration review: `Affirmative/F0V2C1-A-MIGRATION-TEXT-CLOSED`; all ten
  questions close, including ten unique recognized declaration kinds with one
  body-owner page each and a malformed-shape admission.
- Holdout readjudication:
  `Affirmative/F0V2C2-A-HOLDOUTS-READJUDICATED`; all eight verdicts remain
  frozen, with five fits, three breaks, zero bends, zero disagreements, and no
  verdict change.
- Publication reconstruction: both compilers agree on all eighteen profiles;
  the migration-base cone contains seventeen profiles, `analysis-kernel` is
  the only stable profile, Foundation is unchanged, and nothing is published.

### Nonclaims

These byte-pinned source checks do not publish owner text or identities, prove
the owner laws for arbitrary values, establish implementation, runtime,
provider, or backend correspondence, establish relation satisfaction or
theorem truth, prove a cryptographic or protocol-security property, validate
an endpoint or deployment, admit an exact holdout Core, or establish production
readiness. Declaration-body closure covers only the kinds recognized by these
three pinned profiles; it does not cover an unlisted future profile or prove
meaning beyond each stated declaration body. The affirmative holdout aggregate
says every row was re-adjudicated with a frozen verdict, not that every
protocol fits.

### Surprises and corrections to the brief

- This clone does not contain `AGENTS.md` or `.claude/CLAUDE.md`; their
  read-only primary-checkout copies supplied the required instructions.
- The common malformed-shape classification is owned once by Foundation's
  recognized-declaration formation law, while the canonical-framed page also
  restates it locally for the application-domain body. Requiring duplicate PIR
  copies would conflict with the existing owner split; the checker instead
  requires one exact body-owner page per kind and the common formation law.
- The general package discipline requests manifest and lifecycle edits, while
  the task-specific instruction forbids manifest edits. Both packages and all
  inventory entries already exist, so no manifest, lifecycle catalog, or count
  pin changes are needed.
- The workflow's private status-ledger append conflicts with the express
  outside-clone write prohibition and read-only mount, so no private ledger was
  changed.
- The lifecycle count pins do not move because this round updates existing
  packages and adds none.
- The full publication package's legacy-table assertions fail after both
  compilers agree on the current identities: six frozen upstream rows and the
  complete published table still describe the pre-migration publication.
  This is the expected no-publication boundary, not a compiler disagreement;
  the required direct identity reconstruction exits zero and this lane does
  not edit the publication table.

The real Git index remains untouched. No commit, push, pull request,
owner-page edit, profile-manifest edit, directory-README edit, publication, or
private-ledger write was attempted.

## Round eight

### Exact question and result

Does the current migrated PIR owner text close all sixteen verification
questions: the ten questions frozen in round seven, plus Interface completion
derivability, source-authority preimage equations, heterogeneous
challenge-transition representability, required-influence exactness, the
Analysis owner-read join, and public-setup view totality?

No, for the exact sources at migration head `16eed00f`. The ten round-seven
questions remain affirmative. Three of the six repaired-countermodel questions
are affirmative and three remain `CannotAnswer`, so the aggregate is
`CannotAnswer/F0V2C1-C-MIGRATION-TEXT-NOT-CLOSED`.

| Finding | Outcome and stable code |
|---|---|
| decision fidelity | `Affirmative/F0V2C1-A-DECISION-FIDELITY` |
| Terminal contract | `Affirmative/F0V2C1-A-TERMINAL-CONTRACT` |
| public-coin graph | `Affirmative/F0V2C1-A-PCGRAPH-TRANSFER` |
| owner-name closure | `Affirmative/F0V2C1-A-OWNER-CLOSURE` |
| manifest closure | `Affirmative/F0V2C1-A-MANIFEST-CLOSURE` |
| publication compilers | `Affirmative/F0V2C1-A-PUBLICATION-COMPILERS` |
| family-body closure | `Affirmative/F0V2C1-A-FS-BODY-CLOSURE` |
| reference-leaf closure | `Affirmative/F0V2C1-A-PIR-REFERENCE-CLOSURE` |
| static-view law selection | `Affirmative/F0V2C1-A-STATIC-VIEW-LAW-SELECTION` |
| declaration-body closure | `Affirmative/F0V2C1-A-DECLARATION-BODY-CLOSURE` |
| Interface completion derivability | `CannotAnswer/F0V2C1-C-INTERFACE-COMPLETION-DERIVATION` |
| source-authority preimage equations | `CannotAnswer/F0V2C1-C-CANONICAL-BINDING-PREIMAGE` |
| challenge-transition representability | `Affirmative/F0V2C1-A-CHALLENGE-TRANSITION-REPRESENTABLE` |
| influence-view exactness | `Affirmative/F0V2C1-A-INFLUENCE-VIEW-EXACT` |
| Analysis read-catalog join | `Affirmative/F0V2C1-A-ANALYSIS-READ-CATALOG-JOIN` |
| public-setup view totality | `CannotAnswer/F0V2C1-C-PUBLIC-SETUP-VIEW-TOTALITY` |

The retained checks rerun their bounded schedule, terminal, region,
claim-status, view-body, reference-leaf, law-selection, declaration-body,
manifest, and publication oracles against the current source pins. The current
family-view census has 91 exact fields in the eight construction/result
bodies. Nothing in this round converts one of those finite controls into a
general semantic proof.

### Interface completion derivability

The repair removes the unformable draw-sequence coordinate. Its replacement
claim is not derivable from the owner transition. The Interface presents the
construction, failed challenge, prefix receipt count, prefix state, and final
state at `docs-next/pir/interfaces-and-plans.md:497-555`. From the transition
at `docs-next/pir/fiat-shamir.md:850-889`:

- every squeeze output, intermediate state, and final state is a function of
  the construction, challenge, and prefix state;
- every draw receipt also contains the acceptance result; and
- acceptance and successful decoding consume the exact public-condition values
  and exact prior joint-member challenge values at lines 863-866 and 878-881.

Those last two input classes are absent from the completion payload. They
cannot be recovered from `prefix_state`: the owner expressly permits
noninjective absorb and advance algorithms at lines 679-682. The first missing
inputs therefore occur at lines 865-866, and the exact draw sequence is not a
function of the five presented coordinates. `final_state` alone is derivable,
but that does not make every draw derivable as the Interface claims.

The type-formation half of the repair does close. Applying the Foundation
Appendix A.2 `Worst` equations gives `(11,1,0,0)` for the failed-challenge
natural, `(12,1,0,0)` for the receipt-count natural, and `(64,3,2,1)` for the
two-natural failure payload. State values inherit the construction's stricter
tagged-completion preflight, and terminal public outputs are already owner
admitted. Thus every current completion coordinate type is admissible for
every admitted canonical-framed construction. The six
`CompletionPayloadCoordinate` constructors at Interface lines 497-503 also
match exactly the six body arms at lines 2007-2010.

The deep review's former type obstruction is reversed, but the replacement's
derivation premise fails on the review method's own smallest construction.
The finding remains `CannotAnswer` at the exact missing owner inputs rather
than treating a passing state replay as a draw replay.

### Source-authority preimage equations

The owner-text repair closes. A recursive audit of all thirteen top-level PIR
Markdown pages finds fourteen source-authority identity constructors: ten
direct constructors apply their same-page family compiler to a tagged family
value, and four generic static-view constructors dispatch through the selected
owner profile's bound compiler. The audit also resolves twenty-four compiler
definitions over the four `pir.source-*` subject kinds. The canonical-framed
and duplex family pages each enumerate both `StaticView` and
`CheckedConstruction` arms for binding payload, capability requirement,
no-policy declaration, and policy closure. This supplies the explicit wrapper
that the deep review's reversal condition required.

The executable Analysis route does not implement that equation. The call at
`evaluation/k3-analysis-closure/reference_model.py:16521-16529` requests the
canonical-framed execution view. Its protocol-model callee selects the transcript profile
at `evaluation/k2-protocol-fiat-shamir/reference_model.py:3185-3189`, but the
common authority helper forms this untagged payload at lines 2262-2270:

```text
R {
  0: owner_domain,
  1: family,
  2: source_body,
  3: manifest_body,
  4: consumer_ref,
  5: purpose_ref
}
```

It forms and authenticates the payload identity directly at lines 2272-2283.
It never applies the owner-required arm-0
`CanonicalFramedSourceBindingPayloadBody(StaticView(y))`, whose local body is
the view coordinate plus the ordered field-coordinate sequence. The model does
not call the current Interaction compiler either: it selects the transcript
profile and bypasses both current family compilers. The textual repair is
therefore affirmative, but the requested text-to-model correspondence remains
`CannotAnswer/F0V2C1-C-CANONICAL-BINDING-PREIMAGE`.

### Challenge-transition representability

The review's two-rule Core now projects to one exact construction-wide body.
Writing the symbolic algorithm and evaluation-contract coordinates explicitly,
the derived body is:

```text
ChallengeTransitionViewBody {
  transcript_construction_id: two-rule-construction,
  core_id: two-rule-core,
  namespace_derivation_law: canonical-framed-prefix-and-domain-v0,
  exact_length_law: canonical-framed-body-grammar-v0,
  state_update_before_decode_law:
    canonical-framed-admission-and-execution-v0,
  retry_law: canonical-framed-admission-and-execution-v0,
  sampling_failure_law: canonical-framed-admission-and-execution-v0,
  challenge_rules: [
    {
      challenge_ref: 0, position: 0,
      acceptance_abi: {
        use: (accept-boolean-0, accept-contract-0),
        input_types: [TranscriptBytesType], result_type: BooleanType
      },
      decoder_abi: {
        use: (decode-boolean-0, decode-contract-0),
        input_types: [TranscriptBytesType], result_type: BooleanType
      },
      draw_bounds: {squeeze_length: 1, maximum_draws: 1}
    },
    {
      challenge_ref: 1, position: 1,
      acceptance_abi: {
        use: (accept-root-natural-1, accept-contract-1),
        input_types: [TranscriptBytesType], result_type: BooleanType
      },
      decoder_abi: {
        use: (decode-root-natural-1, decode-contract-1),
        input_types: [TranscriptBytesType], result_type: RootNat(2)
      },
      draw_bounds: {squeeze_length: 2, maximum_draws: 3}
    }
  ]
}
```

The body follows the field definitions at
`docs-next/pir/fiat-shamir.md:1317-1340` and the entry-by-entry projection law
at lines 1391-1397. It retains
both ABIs and both bound records: zero rules are selected, dropped, or changed.
This meets the deep review's reversal condition.

### Required-influence exactness

`InfluenceAtom` has exactly one definition on the page, at
`docs-next/pir/fiat-shamir.md:585-604`, and Appendix A gives its exact body tags
zero through thirteen. For the first active challenge after the root opening
with two public bindings, the static projection law at lines 1365-1389 derives
these six required entries, in transition order:

```text
(Atom(CoreHeaderAtom(core-id)), true)
  body V(0,Y(ContentRefV0(core-id)))
(Atom(ConstructionHeaderAtom(construction-id)), true)
  body V(1,Y(ContentRefV0(construction-id)))
(Atom(ApplicationDomainAtom(application-domain-ref)), true)
  body V(2,DeclarationRefBody(Module(application-domain-ref)))
(Atom(ScopeOpenedAtom([0])), true)
  body V(3,S[N(0)])
(Atom(PublicBindingAtom(0)), true)
  body V(4,N(0))
(Atom(PublicBindingAtom(1)), true)
  body V(4,N(1))
```

For a two-challenge Core, the second challenge carries those entries plus one
symbolic `(EveryActualDrawOf(0), true)` entry. If the first challenge produces
two draws, runtime expansion gives the two exact tag-13 bodies
`V(13,R{0:N(0),1:N(0)})` and `V(13,R{0:N(0),1:N(1)})` in draw order. No
synthetic occurrence coordinate is needed for the header, and the two binding
references remain distinct.

The body text explicitly includes every scheduled static atom, condition atom,
module atom, and prior symbolic draw; lines 1378-1386 state that the `true`
entries are exactly the complete base, Reduction, and module requirement.
They expressly include both item 9's joint-member draws and item 10's earlier
continuous-state squeezes from Section 5.2. This meets the review's reversal
condition and closes `F0V2C1-A-INFLUENCE-VIEW-EXACT`.

### Analysis read-catalog join

The current Analysis page has ten literal `AnalysisStaticViewFields` or
`AnalysisExecutionViewFields` selections containing 66 selected top-level
fields. Every selected name resolves to a field declared by the selected owner
body; there are no duplicate or absent selections. Twenty-four of those names
select record or sequence roots. The owner read law defines a field name as an
exact ordinal subtree path and expands every selected subtree to all atomic
leaves, so none of the current names is ambiguous between a leaf and a subtree.

`checks/tests/test_analysis_owner_read_catalog.py` discovers all ten literal
calls and checks their names against the owner bodies. It is sufficient for
this current literal field-existence join. It does not prove the recursive
semantic meaning of the 24 subtree roots, compiler authenticity, or execution
closure. The removed `result_ref` and renamed fields satisfy the deep review's
reversal condition without weakening absent-field refusal, so the finding is
`Affirmative/F0V2C1-A-ANALYSIS-READ-CATALOG-JOIN`.

### Public-setup view totality

The repaired support partition represents the deep review's child-scope
countermodel exactly. For the occurrence-derived `SessionContext` binding
zero it derives:

```text
entries = []
run_established = [0]
body = R{0:ContentRef(protocol-id),1:ContentRef(core-id),2:S[],3:S[N(0)]}
```

This exact named condition excludes the future strategy value from setup, so
the original review's support-boundary reversal condition is met. The stated
totality claim is nevertheless false. Membership in `entries` and
`run_established` is Protocol-determined, but every `entries` element contains
its invocation-supplied value. For one Protocol with one invocation-determined
Boolean public binding, otherwise equal false and true invocations produce two
different canonical view bodies and IDs. Thus the text at
`docs-next/pir/interactive-core.md:3062-3063` cannot conclude that every
Protocol has exactly one setup view. Exactly one view is derivable only for a
Protocol and invocation pair, or for the covered-value equivalence class the
body already defines. The Statement-invariance exclusion at lines 3075-3078
is exact and survives that correction.

The Analysis consumer has a second mismatch. Its fixed-setup projection at
`docs-next/analysis/cryptographic-properties.md:523-525` requires only equal
`entries`, not empty `run_established` sequences. Formation at lines 561-566
then requires the entries to contain every `PublicParameter` and
`SessionContext` binding, contrary to the owner's explicit complement for an
admitted Protocol such as the countermodel. This is not a proof that fixed
setup must admit that Protocol; it is missing formation text for the intended
restricted domain. The finding is therefore
`CannotAnswer/F0V2C1-C-PUBLIC-SETUP-VIEW-TOTALITY`.

### Publication reconstruction and holdouts

The reference and independent publication compilers agree on all eighteen
profiles at the current tree, the round-seven tree, and the migration base.
Relative to round seven, sixteen profiles rotate; `oir-endpoint-graph` and
`analysis-kernel` are stable. Relative to the migration base, the previously
measured seventeen-profile cone remains and only `analysis-kernel` is stable.
Foundation is unchanged, six published upstream rows remain intentionally
stale, and this lane writes no publication table.

The holdout package is independently re-pinned and all eight verdict rows are
re-adjudicated. Five still fit and three still break at the same named
boundaries; none bend, disagree, or change verdict. The aggregate remains
`Affirmative/F0V2C2-A-HOLDOUTS-READJUDICATED`. The four source-specialized
fitting rows separately retain
`CannotAnswer/F0V2C2-C-EXACT-TERMINAL-CARRIERS`; none of the three migration
blockers supplies those missing source carriers.

### Proposed delta

#### Completion replay inputs

- **Owner page and section:** `docs-next/pir/interfaces-and-plans.md`, Section
  3.5, Completion presentation.
- **Exact change:** Add one construction-specific
  `FSFailureReplayInputs` coordinate. Its semantic type is a variant indexed by
  every challenge rule; arm `c` is the record of the trailing
  `SamplingInputTypes(c)` values used by acceptance and decoding, excluding the
  already carried transcript bytes. The failed challenge selects the arm and
  the payload carries the exact public-condition and prior joint-member values
  in ABI order. Admit the Interface only after the complete variant type passes
  Foundation Appendix A.2 `Worst`; return the existing qualified unsupported
  or refused result if it does not. Replace the claim that draws are functions
  of only the existing coordinates with replay from the construction,
  challenge, prefix state, and this exact typed input arm. Add the corresponding
  body arm and require it in the failure entry's map domain.
- **Identity effect:** The Interface-plan profile, Interface/Plan IDs,
  source-authority artifacts, and import dependents rotate. The Core and
  canonical-framed construction bodies need not change.
- **Evidence and gate:** The missing arguments are owner lines 865-866 and
  880-881; noninjectivity is explicit at lines 679-682. Gate
  `F0V2C1-C-INTERFACE-COMPLETION-DERIVATION`.
- **Reversal condition:** Close only if every draw and final state is derived
  from coordinates the Interface actually carries for every admitted
  construction, or if an equivalent exact bounded replay carrier is supplied.
  A final-state replay or one one-shot fixture is insufficient.
- **Nonclaims:** This delta does not claim the external codec implements replay,
  that every construction can form an Interface, or any transcript-security
  property.

#### Executable source-authority compiler dispatch

- **Owner page and section:** No owner-page change is proposed. Update
  `evaluation/k2-protocol-fiat-shamir/reference_model.py`, the authority helper
  at lines 2262-2283 and the execution-view route beginning at line 3174.
- **Exact change:** Pass the tagged family value to an owner-profile-specific
  four-subject compiler. For a canonical-framed static view, form the binding
  payload as arm 0 of `CanonicalFramedSourceBindingPayloadBody(StaticView(y))`,
  with `y` equal to the canonical view-coordinate body and ordered manifest
  field-coordinate bodies; form requirement, no-policy, and closure IDs through
  the corresponding canonical-framed compilers. Keep Fresh views on the
  Interaction compiler and duplex views on the duplex compiler. Add a
  discriminator asserting that the Analysis Fiat--Shamir execution-view payload
  equals the canonical equation and rejects both the untagged six-field record
  and an Interaction-family wrapper.
- **Identity effect:** This changes bounded executable evidence and fixtures,
  not owner or published identities. Any fixture IDs derived from the old model
  preimage must be regenerated and rechecked.
- **Evidence and gate:** Analysis-model lines 16521-16529 select the operation;
  protocol-model lines 3185-3189 select the transcript profile; protocol-model
  lines 2262-2283 bypass its bound compiler. Gate
  `F0V2C1-C-CANONICAL-BINDING-PREIMAGE`.
- **Reversal condition:** Close when the executable payload and all four
  authority subjects equal the selected owner's tagged equations byte for byte,
  or when the executable is explicitly retired as non-correspondence evidence.
- **Nonclaims:** Matching the preimage equation would not prove capability
  freshness, runtime correctness, or theorem applicability.

#### Public-setup quotient and fixed-setup domain

- **Owner pages and sections:** `docs-next/pir/interactive-core.md`, Section
  13.4, Public setup; and
  `docs-next/analysis/cryptographic-properties.md`, Section 3, fixed public
  setup.
- **Exact change:** In the PIR page, state that the Protocol alone determines
  membership in `entries` and `run_established`, while the Protocol plus exact
  invocation determines entry values and therefore the full body and ID.
  Replace “every admitted Protocol has exactly one setup view” with exactly one
  view per admitted Protocol/invocation pair, modulo the body's existing
  covered-value equivalence. In Analysis, require both selected setup views to
  have empty `run_established` sequences before requiring their `entries` to be
  byte-identical and complete; reject the fixed-setup formation otherwise.
- **Identity effect:** The public-setup profile, public-setup view IDs,
  Analysis cryptographic-property profile, and their import dependents rotate.
  Core/Protocol domain bodies need not change.
- **Evidence and gate:** PIR lines 3056-3078 establish the partition and
  invocation-sensitive body; Analysis lines 523-525 and 561-566 omit the empty
  complement premise. Gate `F0V2C1-C-PUBLIC-SETUP-VIEW-TOTALITY`.
- **Reversal condition:** Close when uniqueness is stated at the exact
  Protocol/invocation quotient and the Analysis operation explicitly selects a
  formable subset consistent with both owner sequences. Showing only that the
  future strategy binding enters `run_established` does not establish the
  current one-view-per-Protocol claim.
- **Nonclaims:** This delta does not require the countermodel to form fixed
  setup, restrict Core binding semantics, or prove fixedness, independence, or
  a cryptographic setup property.

## Handoff

Main should commit this complete working tree with subject:

```text
test: review the cross-contract repairs and re-pin the holdouts
```

### Files changed

- `evaluation/formal-source-migration-text-review-f0v2c1/run.py` reruns the ten
  retained findings, derives all six repair countermodels, audits the complete
  source-constructor corpus and Analysis read join, checks both executable
  models, and reconstructs current and baseline publication cones.
- `evaluation/formal-source-migration-text-review-f0v2c1/expected-findings.json`
  freezes sixteen names, outcomes, stable codes, the three-blocker aggregate,
  and metrics digest
  `2b1ee42cddcd7ead71621d50fda0fb471b40d82a8df5cbf7fd60062534361f37`.
- `evaluation/formal-source-migration-text-review-f0v2c1/README.md` states the
  exact current answer, closed repairs, blockers, and nonclaims.
- `evaluation/formal-source-holdout-readjudication-f0v2c2/run.py`,
  `adjudication.json`, `expected-findings.json`, and `README.md` re-pin the
  five current owner pages and migration record, move exact source ranges, and
  freeze the unchanged eight-row adjudication at
  `dc610e14675fccac31f416bbcb3b12355f866ed1d99ba4ece6253ed4f0406e7e`.
- `evaluation/README.md` refreshes the two current package rows.
- This note and `f0v2c2-holdout-readjudication.md` record round eight and the
  proposed deltas. No directory README is edited.

No PIR, Foundation, Relations, OIR, or Analysis owner page; source profile
manifest; check manifest; lifecycle catalog or count pin; publication table;
mechanization; private ledger; or real Git index was edited. No package was
added. No commit, push, or pull request was attempted.

### Validation

The lifecycle-sensitive commands used a clone-local alternate index and object
store under the ignored `.cache/` directory, with the checkout objects as
read-only alternates. The developer and focused runs also used
`UV_NO_SYNC=1`, `UV_OFFLINE=1`, and a clone-local dependency cache. All of
those transient paths and the generated `target/checks` results were removed.
The real index SHA-256 was
`35d3dfeac2d5423d43d3512cad742f2f6edc2c891b70e979ae888cebf6933642`
both before and after the alternate-index matrix.

| Command | Exit | Wall time | Result |
|---|---:|---:|---|
| full reads of owner-repair commits `1548d657` and `16eed00f` | 0 each | 0.01 s and 0.00 s | inspected the complete repair diffs without writing |
| pre-edit migration package `--check` | 1 | 0.07 s | correctly detected the stale round-seven 95-field freeze |
| pre-edit holdout package `--check` | 1 | 0.04 s | owner/support pins and frozen projection drifted; all eight verdict comparisons already agreed |
| final migration package `--check` | 0 | 1.39 s | reproduced sixteen findings, three blockers, and the `CannotAnswer` aggregate |
| final holdout package `--check` | 0 | 0.04 s | reproduced all 26 findings and the affirmative eight-row verdict aggregate |
| two cross-owner developer controls | 0 | 0.05 s | all four unit tests passed |
| direct publication identity print | 0 | 0.36 s | reference and independent compilers agreed on all eighteen current profiles |
| diagnostic publication package `--check` | 1 | 3.29 s | compiler agreement passed; six intentionally stale upstream pins, one stale mutation needle, and the unpublished table failed as expected |
| `python3 -B checks/run.py validate` with alternate index | 0 | 0.04 s | validated 77 checks across six tiers; manifest digest `926710c3c5c29534782ebc0856538807db44d3a8bde10caace17ad5fb1602539` |
| `python3 -B checks/run.py run --tier developer` with alternate index and offline cache | 0 | 1.81 s | all nine developer checks passed |
| focused `research.migration-text-review` wrapper with the same environment | 0 | 1.45 s | passed |
| focused `research.holdout-readjudication` wrapper with the same environment | 0 | 0.10 s | passed |
| Python/JSON parsing and `git diff --check` | 0 | 0.12 s | parsed both changed Python files and all three changed JSON files; no whitespace errors |

### Aggregate outcome

- Migration review:
  `CannotAnswer/F0V2C1-C-MIGRATION-TEXT-NOT-CLOSED`. Thirteen of sixteen
  questions close. The exact blockers are completion draw derivability,
  canonical source-preimage correspondence in the executable model, and
  public-setup view totality.
- Holdout readjudication:
  `Affirmative/F0V2C2-A-HOLDOUTS-READJUDICATED`. All eight verdicts are frozen
  and re-adjudicated: five fit, three break, zero bend, zero disagree, and zero
  change. Four fitting rows retain their separate exact-carrier
  `CannotAnswer`.
- Publication reconstruction: both compilers agree on all eighteen current and
  baseline profiles. Sixteen profiles rotate relative to round seven;
  `oir-endpoint-graph` and `analysis-kernel` are stable. The migration-base cone
  remains seventeen profiles with only `analysis-kernel` stable. Foundation is
  unchanged and nothing is published.

### Nonclaims

These byte-pinned, finite checks do not adopt a proposed delta; publish owner
text or identities; prove an owner law for arbitrary values; establish complete
implementation, runtime, provider, backend, OIR, endpoint, or source-family
correspondence; prove relation satisfaction or theorem truth; establish a
Fiat--Shamir, random-oracle, sponge, quantum-random-oracle, or broader protocol
security result; admit an exact holdout Core; or establish deployment or
production readiness. The Analysis read-control result covers literal current
field existence, not recursive semantic correctness. The affirmative holdout
aggregate says every row was re-adjudicated with a frozen verdict, not that
every protocol fits.

### Surprises and corrections to the brief

- The repair commits do not put all six cross-contract questions in their
  claimed ideal form. Three repaired texts still admit the exact countermodels
  above, so the all-sixteen affirmative aggregate is unavailable.
- The executable model does not use the Interaction compiler in the
  canonical-framed path contemplated by the brief. It selects the transcript
  profile but bypasses both current family compilers with a common untagged
  record. The finding and proposed delta record that stronger mismatch.
- The Interface prose points readers to its owner's Sections 8 and 9, but the
  missing acceptance inputs are explicit in the challenge-transition equation
  in Section 7; Section 9 supplies the execution and replay context. The review
  checked all three sections rather than inferring the transition inputs from
  the citation.
- This clone contains neither `AGENTS.md` nor `.claude/CLAUDE.md`; their
  read-only primary-checkout copies supplied the required instructions.
- The general package discipline describes adding manifest and lifecycle rows,
  while the task-specific instruction forbids manifest edits. Both packages,
  check entries, lifecycle entries, and evaluation rows already existed, so
  this round updates them in place and does not move lifecycle count pins.
- The workflow's private-ledger append conflicts with the express outside-clone
  write prohibition and read-only mount, so no private ledger was changed. The
  seventh deep-review finding is repaired on another branch and was deliberately
  not judged here.
- The full publication check has one stale public-setup mutation needle in
  addition to the expected unpublished identity assertions. The independent
  compiler-agreement test and direct identity reconstruction both pass; this
  lane neither repairs that out-of-scope test nor publishes the table.
- One first alternate-index setup targeted nonexistent `target/` and exited 1
  before index creation or staging. The successful run used ignored `.cache/`
  storage. Exploratory holdout calls also used one nonexistent package spelling
  and the unsupported `--json` option; both exited 2 without writing package
  state, and the canonical `--check` command passes.
- An ignore-pattern probe reused zsh's special `path` name, so later read-only
  commands in that one subshell exited 127. A fresh shell restored the inherited
  search path; no repository state changed.
- Six transient JSON diagnostic captures were inadvertently created under
  `/tmp` outside the clone. All six were unlinked before handoff, as were two
  generated bytecode-cache directories; no outside-clone artifact remains.

The real Git index remains untouched. The working tree is intentionally
uncommitted for Main.

## Round nine

### Exact question and result

Does the current migrated PIR owner text close all seventeen verification
questions: the sixteen questions rerun in round eight and the additional exact
checked-construction checker-contract question?

Yes, for the exact sources at migration head `5295ef09`. All seventeen
findings are affirmative, so the aggregate is
`Affirmative/F0V2C1-A-MIGRATION-TEXT-CLOSED`.

| Finding | Outcome and stable code |
|---|---|
| decision fidelity | `Affirmative/F0V2C1-A-DECISION-FIDELITY` |
| Terminal contract | `Affirmative/F0V2C1-A-TERMINAL-CONTRACT` |
| public-coin graph | `Affirmative/F0V2C1-A-PCGRAPH-TRANSFER` |
| owner-name closure | `Affirmative/F0V2C1-A-OWNER-CLOSURE` |
| manifest closure | `Affirmative/F0V2C1-A-MANIFEST-CLOSURE` |
| publication compilers | `Affirmative/F0V2C1-A-PUBLICATION-COMPILERS` |
| family-body closure | `Affirmative/F0V2C1-A-FS-BODY-CLOSURE` |
| reference-leaf closure | `Affirmative/F0V2C1-A-PIR-REFERENCE-CLOSURE` |
| static-view law selection | `Affirmative/F0V2C1-A-STATIC-VIEW-LAW-SELECTION` |
| declaration-body closure | `Affirmative/F0V2C1-A-DECLARATION-BODY-CLOSURE` |
| Interface completion derivability | `Affirmative/F0V2C1-A-INTERFACE-COMPLETION-DERIVABILITY` |
| source-authority preimage equations | `Affirmative/F0V2C1-A-SOURCE-AUTHORITY-PREIMAGES` |
| checked-construction checker contract | `Affirmative/F0V2C1-A-CHECKER-CONTRACT-IDENTITY-DERIVED` |
| challenge-transition representability | `Affirmative/F0V2C1-A-CHALLENGE-TRANSITION-REPRESENTABLE` |
| influence-view exactness | `Affirmative/F0V2C1-A-INFLUENCE-VIEW-EXACT` |
| Analysis read-catalog join | `Affirmative/F0V2C1-A-ANALYSIS-READ-CATALOG-JOIN` |
| public-setup view totality | `Affirmative/F0V2C1-A-PUBLIC-SETUP-VIEW-TOTAL` |

The retained questions rerun their bounded schedule, terminal, region,
claim-status, view-body, reference-leaf, law-selection, declaration-body,
manifest, and publication controls against current source bytes. Their
affirmative outcomes remain bounded evidence rather than general proofs.

### Completion derivability

The two values the Interface presents in addition to transcript state are
exactly the two trailing operands of the owner definition. The Fiat--Shamir
page defines `SamplingInputTypes(c)` at lines 211-215 as transcript bytes,
`public_conditions`, then `correlation.prior_members`. The Interface names the
public-condition and accepted prior-member values at lines 541-545 and does
not list transcript bytes as a separate replay operand.

The remaining classification is exhaustive for an admitted canonical-framed
Protocol:

- the raw Core `ValueRef` carrier has public-input, verifier-private, constant,
  derived, and occurrence-output arms at
  `docs-next/pir/interactive-core.md:506-511`;
- the Interface permits only a protocol-fixed constant, a public input bound
  to a slot, a derived value of those, or an occurrence value with transport
  at `docs-next/pir/interfaces-and-plans.md:545-551`;
- the invocation assignment is total over the public inputs at Interface lines
  358-361; and
- a verifier-private dependency causes `ChallengeTransfer` to return
  `VerifierPrivate`, while any non-static-public condition is invalid, at Core
  lines 1688-1696. Construction admission additionally requires
  `PublicCoinEligible` and refuses verifier-private influence at
  `docs-next/pir/fiat-shamir.md:937-956`.

Thus a verifier-private public-condition reference is syntactically possible
in an unauthenticated raw carrier but is not admissible in the construction
under review. There is no missing owner premise and no `CannotAnswer` at this
boundary.

The round-eight countermodel has one public occurrence output as a challenge
operand. With no transport entry to `ExternalApplication`, it is refused by
the requirement at Interface lines 547-553 and admission item 6 at lines
611-612. Adding exactly that transport entry makes the countermodel pass this
gate. No transcript-state injectivity is assumed.

The transition at Fiat--Shamir lines 850-889 makes each squeeze output,
post-state, acceptance result, decoded value, and final state a deterministic
function of the construction, challenge, prefix state, and the two presented
operand sequences. Replay explicitly recomputes those quantities at lines
1028-1036. Consequently every draw, acceptance result, and `final_state` is a
function of presented values and `prefix_state`, as the Interface concludes at
lines 553-559. The six completion coordinates and six body arms still agree,
and their previously checked Foundation bounds remain unchanged.

### Source-authority preimages

The owner equations are now implemented rather than merely present in prose.
The canonical-framed page defines the local static-view payload,
checked-construction payload, requirement, no-policy, and closure records at
lines 1665-1692, then wraps both issued families through all four profile
compilers at lines 1694-1707. The duplex page gives the corresponding equations
at lines 1275-1317.

The executable model declares both owner compilers and every source-subject
kind at
`evaluation/k2-protocol-fiat-shamir/reference_model.py:2211-2250`, binds both
families to distinct arms at lines 2278-2289, and applies the selected compiler
at lines 2304-2322. Its authority constructor forms the binding payload,
no-policy declaration, capability requirement, and policy closure through
that compiler beginning at lines 2444-2493. The checked-construction issuance
route supplies the owner-local payload at lines 4246-4259.

The frozen evaluator independently assembles and encodes four subjects for
each of these routes:

1. canonical-framed execution static view;
2. canonical-framed checked construction;
3. duplex static view; and
4. duplex checked construction.

All sixteen executable subject bodies equal the corresponding owner equations
byte for byte. Both actually issued canonical bindings also carry the expected
payload, no-policy, requirement, and closure identities. The duplex profile is
checked through its live publication profile and executable owner compiler;
this bounded executable model does not expose a duplex issuance operation, so
no duplex live-capability claim is made.

### Checker-contract identity

The canonical owner definition at
`docs-next/pir/fiat-shamir.md:1153-1181` requires the exact operation, same-Core
law, defect schema, and checked-result schema. Its canonical body equation is
at lines 1669-1674. The duplex definition is at
`docs-next/pir/duplex-sponge-fiat-shamir.md:832-860`, with its body equation at
lines 1279-1284. Both family manifests support
`pir.checker-contract` and bind `checker-contract-body-v0` at body-compiler
ordinal 5.

The reference and independent publication compilers assign these declaration
references:

| Family | Operation ordinal | Law ordinal | Defect ordinal | Body bytes | Body SHA-256 |
|---|---:|---:|---:|---:|---|
| canonical framed | 1 | 3 | 1 | 1,871 | `f8f79c99a8e74702367b7bfa6fc0a7ccc16427282aae23f24666c0c2ceff97fb` |
| duplex sponge | 1 | 6 | 1 | 5,243 | `75eb2fe3aa516c17e0ae365df9bd8d4c7c218c7a8852ae39e1dc927ee5b64765` |

At each ordinal, the referenced catalog declaration is a record whose name is
exactly the owner-required declaration. The executable helper at
`evaluation/k2-protocol-fiat-shamir/reference_model.py:3986-4056` resolves the
same unique declarations and emits the same four-field body byte for byte. The
current live identities are:

```text
zkcidv0:pir.checker-contract:ebe686d6fb48030f03b79f1cfe72994705c40ea2414afc59a44ff149b8dfd701
zkcidv0:pir.checker-contract:393ff59dfef32f77fee523fc0708dbe591c964369fb2b9461947ff93d9c83210
```

The checked-construction local payload formed at executable lines 4067-4117
carries that profile-relative checker contract. A payload carrying the former
package-local checker coordinate encodes differently and is rejected by the
frozen discriminator.

### Public-setup view totality

The round-eight occurrence-derived countermodel remains represented exactly:

```text
entries = []
run_established = [0]
body = R{0:ContentRef(protocol-id),1:ContentRef(core-id),2:S[],3:S[N(0)]}
```

The owner formation law is at
`docs-next/pir/interactive-core.md:3041-3059`. The repaired sentence at lines
3062-3065 now distinguishes protocol-determined membership from
invocation-determined entry values and claims exactly one view per Protocol and
invocation, up to the quotient's covered-value equivalence. The executable
discriminator projects two invocations of one Protocol with false and true
values for one covered public input. Their bodies differ, as required, while
each Protocol-and-invocation input produces exactly one body. A Statement-only
input remains excluded under lines 3073-3080.

The Analysis-owned fixed-setup half is deliberately not judged here. It is
recorded in the frozen metrics as `OutsideScope`, not as affirmative and not as
`CannotAnswer`; its branch must adjudicate its own fixed-setup premises.

### Retained transition, influence, and read-join results

The heterogeneous two-rule transition still preserves both rules, including
their distinct acceptance and decoder interfaces and bounds. Its newly total
`position` field is the challenge occurrence's position in the exact total Core
schedule at `docs-next/pir/fiat-shamir.md:1421-1427`; an absent frame-schedule
coordinate is never invented. The required-influence projection still carries
one symbolic entry for every actual draw of a prior challenge. The Analysis
read catalog still resolves all ten literal selections and 66 selected fields
to exact owner subtrees.

### Holdout re-adjudication

The holdout package now pins the current Interaction, canonical-framed,
duplex, endpoint, OIR, migration-note, and structural-axis bytes. Its canonical
and duplex family-view citation ranges move to lines 1270-1717 and 869-1325.
All eight rows retain their prior verdict against both comparison sources:
five fit, three break, none bend, none disagree, and none change. The aggregate
remains `Affirmative/F0V2C2-A-HOLDOUTS-READJUDICATED`.

The four source-specialized fitting rows still retain
`CannotAnswer/F0V2C2-C-EXACT-TERMINAL-CARRIERS`. The general replay-input,
owner-compiler, and checker-contract repairs do not supply their missing
protocol-specific Check, Reduction, Claim, or failure-guard coordinates. This
is a retained source-evidence boundary, not a changed holdout verdict or an
owner-page defect.

### Publication reconstruction

The reference and independent compilers agree byte for byte on all eighteen
profiles at the current tree, the round-eight tree, the earlier comparison
tree, and the migration base. Relative to round eight, fourteen profiles
rotate. The stable profiles are `interaction`,
`verifier-derived-query-plan`, `oir-endpoint-graph`, and `analysis-kernel`.
Relative to the earlier comparison tree, sixteen rotate and only
`oir-endpoint-graph` and `analysis-kernel` remain stable. Relative to the
migration base, seventeen rotate and only `analysis-kernel` remains stable.
Foundation is unchanged.

The checked-in legacy publication table differs for six upstream profiles.
That is the expected no-publication boundary: both compilers agree on the
derived current table, but this lane writes neither the table nor an owner
manifest.

### Proposed delta

None. The completion, executable source-authority, and PIR public-setup
reversal conditions proposed in round eight are now satisfied. Those earlier
proposals remain in this note only as historical audit records. The separate
Analysis fixed-setup question is outside this round and receives no proposed
owner-page change from this lane.

## Handoff

Main may commit this working tree with subject:

```text
test: review the replay-input and preimage repairs and re-pin the holdouts
```

### Files changed

- `evaluation/formal-source-migration-text-review-f0v2c1/run.py` now reruns
  seventeen questions. It derives the repaired completion inputs, tests the
  missing-transport countermodel, excludes verifier-private conditions at the
  admission boundary, compares sixteen source-subject bodies byte for byte,
  resolves both checker-contract definitions and catalog references, tests
  public-setup uniqueness per invocation, and reconstructs all publication
  cones.
- `evaluation/formal-source-migration-text-review-f0v2c1/expected-findings.json`
  freezes seventeen affirmative findings and evidence digest
  `90ee4311f65e04e2d2776c62a49fc15e6fca842209c4ce151915c0b7893386b4`.
- `evaluation/formal-source-migration-text-review-f0v2c1/README.md` states the
  exact question, affirmative answer, evidence, and non-claims.
- `evaluation/formal-source-holdout-readjudication-f0v2c2/run.py` re-pins the
  current owner and migration-support bytes.
- `evaluation/formal-source-holdout-readjudication-f0v2c2/adjudication.json`
  moves the two family-view citation ranges without changing a verdict.
- `evaluation/formal-source-holdout-readjudication-f0v2c2/expected-findings.json`
  freezes adjudication digest
  `65222397363d60ef8d59f9ddd0a65b48cf0d0b8a2728ebd6b38a0ca596d2c188`.
- `evaluation/formal-source-holdout-readjudication-f0v2c2/README.md` records the
  unchanged five-fit, three-break result and retained exact-carrier boundary.
- `evaluation/README.md` updates the two existing package rows.
- `docs-next/notes/semantic-revalidation-and-redesign/formal-assurance-research/f0v2c1-migration-text-review.md`
  adds this round-nine adjudication and handoff.
- `docs-next/notes/semantic-revalidation-and-redesign/formal-assurance-research/f0v2c2-holdout-readjudication.md`
  adds the round-nine re-pin record.

No owner page, profile manifest, check manifest, lifecycle inventory,
publication table, directory README, or private artifact was edited. These are
existing packages, so no lifecycle file count changed.

### Commands and results

All commands ran from the clone root. The check-control rows used
`GIT_INDEX_FILE=$PWD/.cache/lane-index`,
`GIT_OBJECT_DIRECTORY=$PWD/.cache/lane-objects`,
`GIT_ALTERNATE_OBJECT_DIRECTORIES=/home/wonjae/code/zkc/.git/objects`,
`UV_NO_SYNC=1`, `UV_OFFLINE=1`, and
`UV_CACHE_DIR=$PWD/.cache/uv`.

| Command | Exit | Wall time | Result |
|---|---:|---:|---|
| `python3 -B evaluation/formal-source-migration-text-review-f0v2c1/run.py --check` | 0 | 2.46 s | 17 of 17 reproduced; no blocker; affirmative aggregate |
| `python3 -B evaluation/formal-source-holdout-readjudication-f0v2c2/run.py --check` | 0 | 0.04 s | five fit, three break, no changed verdict |
| `python3 -B evaluation/k2-protocol-fiat-shamir/run.py --check` | 0 | 6.45 s | 86 of 86 tests passed |
| `python3 -B evaluation/semantic-profile-publication/run.py --print-identities` | 0 | 0.36 s | both compilers emitted the same eighteen-profile table |
| `git read-tree HEAD` with the clone-local alternate index | 0 | 0.00 s | alternate index initialized |
| `git add -A` with the clone-local alternate index and object store | 0 | 0.49 s | all ten changed tracked files represented; real index untouched |
| `python3 -B checks/run.py validate` | 0 | 0.05 s | 77 checks, six tiers; manifest digest `926710c3c5c29534782ebc0856538807db44d3a8bde10caace17ad5fb1602539` |
| `python3 -B checks/run.py run --tier developer` | 0 | 2.02 s | all nine checks passed, including lifecycle inventory |
| `python3 -B checks/run.py run --check research.migration-text-review` | 0 | 2.55 s | focused check passed; inner time 2.490 s |
| `python3 -B checks/run.py run --check research.holdout-readjudication` | 0 | 0.10 s | focused check passed; inner time 0.044 s |
| `git diff --check` | 0 | 0.07 s | no whitespace error |
| owner-path diff audit over PIR, Foundation, Relations, Analysis, and OIR | 0 | 0.00 s | no changed owner path |

The real `.git/index` SHA-256 was
`c68c393b64a5bf2bca41105b1d01a70f6d066e3160b5b33d2b4f48a90b225bf1`
before the alternate-index run and remained the same after cleanup. Generated
check results and clone-local index, object, and cache files were removed.

### Aggregate outcome

The migrated owner-text review is
`Affirmative/F0V2C1-A-MIGRATION-TEXT-CLOSED`: all seventeen questions close at
the pinned tree with no proposed owner delta. The holdout aggregate remains
`Affirmative/F0V2C2-A-HOLDOUTS-READJUDICATED`: five rows fit and three break,
with no bend, disagreement, or verdict change. Four fitting source-specialized
rows deliberately retain
`CannotAnswer/F0V2C2-C-EXACT-TERMINAL-CARRIERS`; the repairs do not manufacture
their protocol-specific terminal evidence.

Both publication compilers agree on all eighteen profiles. Fourteen rotate
from round eight, sixteen from the earlier comparison tree, and seventeen from
the migration base. The respective stable sets are
`{interaction, verifier-derived-query-plan, oir-endpoint-graph,
analysis-kernel}`, `{oir-endpoint-graph, analysis-kernel}`, and
`{analysis-kernel}`. Foundation does not rotate. Six rows of the legacy
checked-in publication table remain stale by design and were not treated as
defects or written by this lane.

### Non-claims

This is frozen, bounded source and executable evidence. It does not prove an
owner law for arbitrary values, publish or bless an identity, establish
external compiler, runtime, provider, backend, or endpoint correspondence,
prove relation satisfaction, theorem truth, random-oracle or protocol
security, or establish deployment or production readiness. It does not judge
the Analysis-owned fixed-setup premise. The duplex comparison exercises the
owner compiler directly and does not claim that this bounded model issues a
live duplex capability.

### Surprises and corrections to the brief

- The semantic expectations in the brief were borne out. A raw Core value
  reference can name verifier-private data, but the Core transfer and
  canonical construction-admission rules reject that route; it is not a new
  `CannotAnswer` boundary.
- The requested Analysis fixed-setup half is correctly outside this round. It
  is recorded as `OutsideScope`, rather than as an affirmative finding or a
  missing-evidence finding.
- `AGENTS.md` is absent from this dedicated clone. Its read-only primary-copy
  counterpart was used for the required repository guidance;
  `.github/CONTRIBUTING.md` and `.claude/CLAUDE.md` are present locally.
- The package-registration and lifecycle-count instructions apply when adding
  a package. This round modifies two already registered packages, and the
  brief separately forbids manifest edits, so no count pin moved.
- During diagnosis, temporary captures named under `/tmp/round9-*` were
  created outside the clone and then deleted. This was a process deviation;
  no such artifact remains, and no primary-checkout or private file was
  written.

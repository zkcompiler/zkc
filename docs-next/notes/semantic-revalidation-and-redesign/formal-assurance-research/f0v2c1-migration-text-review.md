# Migration Text Freeze Review

> **State:** `Affirmative/F0V2C1-A-MIGRATION-TEXT-CLOSED` after round two
> **Authority:** None. This verification lane changes no owner page, source
> profile manifest, or published identity.
> **Executable evidence:**
> [`evaluation/formal-source-migration-text-review-f0v2c1`](../../../../evaluation/formal-source-migration-text-review-f0v2c1/README.md)

## 1. Exact question and aggregate

Does the migrated PIR owner text close all seven independent freeze-review
questions for decision fidelity, the Terminal contract, public-coin graph
transfer and sinks, owner-view definition closure, manifest closure,
publication reconstruction, and family-view body closure?

Yes after the round-two repairs. All seven answers are affirmative and the
aggregate is `Affirmative/F0V2C1-A-MIGRATION-TEXT-CLOSED`, with no blocking
finding.

The audit pins the six migrated owner pages and eight migrated manifests. It
does not treat a resolved selector, a passing source compiler, or a finite
oracle as proof that the represented semantics are correct.

Sections 2 through 10 preserve the first-round evidence and proposed repairs
as history. The `Round two` section below supersedes their negative aggregate
against the current owner bytes.

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


## Handoff

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

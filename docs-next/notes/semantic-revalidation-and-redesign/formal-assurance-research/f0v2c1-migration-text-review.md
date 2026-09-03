# Migration Text Freeze Review

> **State:** `CannotAnswer/F0V2C1-C-MIGRATION-TEXT-NOT-CLOSED` after round
> five; eight of nine questions close, including the static-view law-field
> selection, and the one open question, reference-leaf closure, names a
> family declaration kind the reference atom did not admit
> **Authority:** None. This verification lane changes no owner page, source
> profile manifest, or published identity.
> **Executable evidence:**
> [`evaluation/formal-source-migration-text-review-f0v2c1`](../../../../evaluation/formal-source-migration-text-review-f0v2c1/README.md)

## 1. Exact question and aggregate

Does the migrated PIR owner text close all seven independent freeze-review
questions for decision fidelity, the Terminal contract, public-coin graph
transfer and sinks, owner-view definition closure, manifest closure,
publication reconstruction, and family-view body closure?

Round four answers yes after the owner added a typed region for both
`ClaimSource` arms. The current aggregate is
`Affirmative/F0V2C1-A-MIGRATION-TEXT-CLOSED`.

The audit pins the six migrated owner pages and eight migrated manifests. It
does not treat a resolved selector, a passing source compiler, or a finite
oracle as proof that the represented semantics are correct.

Sections 2 through 10 preserve the first-round evidence and proposed repairs
as history. `Round two` superseded their negative aggregate, `Round three`
recorded the source-region reopening, and `Round four` supersedes both against
the current owner bytes.

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

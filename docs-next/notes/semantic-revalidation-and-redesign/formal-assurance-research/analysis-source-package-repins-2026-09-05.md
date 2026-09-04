# Analysis source-package re-pin verification

> **State:** Re-derived against Analysis head `85b058b1`; every baseline
> research-checkpoint failure is repaired except the explicitly excluded
> semantic-profile publication hold.
> **Authority:** None. This verification updates evaluation models and frozen
> evidence only. It does not edit an owner page or profile manifest, publish an
> identity, or authorize a migration.
> **Executable evidence:** the existing packages named by check ID in Section 2.

## 1. Exact question and answer

Against Analysis head `85b058b1`, after the repaired owner text and the
migration-branch package repairs it contains, can every research-checkpoint
failure other than the excluded publication hold be assigned exactly one drift
class, repaired at its current source and identity inputs, and reproduced
without editing an owner page, profile manifest, check manifest, or lifecycle
entry?

Yes. The baseline had 66 checks: 52 passed and 14 failed. The publication
check remains deliberately untouched. Each of the other thirteen failures is
assigned exactly one class below, and its existing package now reproduces its
frozen result. No package was added.

The classes are:

- **(a) source or identity re-pin:** the package's computation remains valid
  and only current page bytes, generated evidence, or identity expectations
  need to be frozen;
- **(b) authored-text transcription:** an executable model must carry fields
  or structure that the current owner text now requires; and
- **(c) semantic consequence:** re-running the model under the repaired text
  changes a computed observation or finding, so the new result must be derived
  and documented rather than treated as a byte-only re-pin.

## 2. Baseline classification, one class per red check

| Check | Class | Baseline cause and disposition |
|---|---|---|
| `research.profile-publication` | Excluded | The publication table and frozen upstream identities remain intentionally old. The package was neither edited nor used as permission to publish. |
| `research.dependent-surfaces` | (b) | Its graph carrier omitted the owner-authored challenge declaration refs, correlation and reduction-use records, and the construction's heterogeneous `challenge_rules`. The carrier transcription now includes them. |
| `research.family-instance-probe` | (c) | The enlarged Core declarations rotate all six measured identities and make the FRI-like body-byte sequence non-affine on the three measured members. The old all-affine finding is now an exact negative observation. |
| `research.joined-semantic-boundary` | (b) | The imported Analysis closure first stopped on a stale statement identity, but a complete repair also had to consume the re-authored owner-read catalog and the two-field public-setup view. The integrated package itself needed no local edit. |
| `research.finite-cover` | (a) | Its inline expected Analysis identity vector was stale; the finite arithmetic and finding meanings did not change. |
| `research.owner-view-publication-topology` | (a) | Both compilers already derived the current table; the expected rotation cone still described the migration head. The Analysis-head expectation is now eighteen rotated and zero stable profiles. |
| `research.semantic-migration-candidate` | (a) | Its hard failure asserted the migration head's seventeen-to-one cone against the Analysis head. It now freezes the Analysis-head cone separately and reconstructs the migration head to preserve the original control. |
| `research.migration-text-review` | (c) | In addition to stale revisions and identities, three repaired contracts change the review result: owner-compiled source preimages, invocation-qualified public setup, and complete failure-replay operand presentation. All sixteen findings are now affirmative. |
| `research.analysis-premise-text-review` | (a) | The canonical-framed Fiat--Shamir page pin, downstream package hashes, and owner-derived premise and goal identities were stale. The thirteen review classifications, including the declared provider hold, do not change. |
| `research.holdout-readjudication` | (a) | Only exact owner and supporting-note byte pins changed; the five-fit, three-break adjudication is unchanged. |
| `research.owner-view-fs-family-determinacy` | (a) | Current family-view body digests and the Analysis-head rotation cone were stale. The determinacy findings do not change. |
| `research.provider-interpretation` | (a) | Regeneration changes the authenticated Core, Protocol, owner-page, profile, and view-body pins in the certificate; its provider findings do not change. |
| `research.provider-interpretation-arklib` | (a) | Regeneration changes the same current subject and certificate coordinates; the finite provider correspondence findings do not change. |
| `research.provider-interpretation-fs-arklib` | (c) | The current canonical-framed construction changes the table-backed Fiat--Shamir challenge values and therefore the finite outcome census. The Lean table, certificate, checker assertions, and prose are re-derived from the current runtime corpus. |

The Analysis closure is the class-(b) dependency behind the joined-boundary
failure. It now issues fourteen authenticated source views: two public-setup
views, eleven PIR reads selected by the Analysis catalog (ten literal field
selections plus the acceptance-effect closure), and the Relations definition
view. Each view uses the exact current consumer and purpose. Fixed setup
additionally authenticates both `run_established` sequences and requires each
to be empty.

## 3. Re-derived semantic results

### 3.1 Identity topology

The reference and independent publication compilers agree on all eighteen
profiles. Relative to the pre-migration identity pin, the Analysis head rotates
all eighteen. A separate reconstruction at migration head
`5295ef0965309e8851b6c095858265fe3157ac2d` preserves the migration branch's
original result: seventeen profiles rotate and `analysis-kernel` alone is
stable. Comparing those two heads rotates exactly `analysis-kernel` and its
five Analysis dependents. No publication table is written.

### 3.2 Family and provider consequences

The family probe re-derives FRI-like body-byte counts
`(9765, 11477, 13190)` at fold counts `(2, 3, 4)`. The adjacent changes are
`1712` and `1713`, so an exact affine law is false on this finite domain. The
other seven measured size coordinates remain affine. This changes the
`regular-finite-variation` finding to
`Negative/FAMILYINSTANCE-N-FRI-BODY-BYTES-NON-AFFINE`; it does not change the
bounded recommendation to keep family parameterization outside the Core.

The ordinary provider and ArkLib provider certificates are regenerated at the
current subject identities with unchanged findings. The finite Fiat--Shamir
provider table changes, in row-major `(statement, commitment)` order, from
`(2,2,0,1,2,0,2,2,1)` to `(0,1,1,1,2,2,1,1,1)`. The complete one-shot corpus
now contains 20 `Accepted` and 34 `Rejected` runs. The separate retrying corpus
has zero observed `InterpretationFailed` runs, rather than six. That finite
zero is not a totality claim; the interpretation-failure lane remains outside
the affirmative one-shot correspondence.

### 3.3 Migration-text consequences

The migration review independently re-derives three previously unresolved
contracts from current text and executable structure:

1. The source-authority helper selects the owner profile's compiler and forms
   the canonical-framed static-view payload as the tagged arm-zero variant,
   rather than hashing the former untagged six-field record.
2. `docs-next/pir/interactive-core.md:3062` makes setup-view membership
   Protocol-determined but values invocation-determined and states uniqueness
   per invocation. The Analysis fixed-setup projection and formation at
   `docs-next/analysis/cryptographic-properties.md:538` and line 577 both
   require empty `run_established` sequences.
3. `docs-next/pir/interfaces-and-plans.md:537` says the failure draws are
   derived from values the Interface presents. Lines 545--559 partition every
   acceptance operand into a Protocol-fixed constant, a bound public input, a
   derivation of those values, or an occurrence value carried by a required
   `ExternalApplication` transport entry, and refuse a failure presentation
   that omits a determining value.

The dependency model still reconstructs every draw receipt, acceptance result,
and final state under the owner transition. It now has no missing leaf for
public-condition or prior-joint-member values, so all sixteen migration-review
findings reproduce as affirmative.

## 4. Retained CannotAnswer and Proposed delta

No repaired owner passage needed a new `CannotAnswer`. The Analysis premise
review nevertheless retains its pre-existing declared
`CannotAnswer/F0V2D1-C-VCVIO-PROVIDER-DECLARATION`. The generic constructor at
`docs-next/analysis/cryptographic-properties.md:2258-2279` requires an exact
property-profile provider declaration and closed carrier, but Section 3.2
publishes no concrete VCVio declaration or carrier and
`docs-next/analysis/profiles/cryptographic-property.json` contains neither
corresponding semantic-law declaration. That absence is not converted into an
affirmative result.

### Proposed delta

- **Owner page and section:**
  `docs-next/analysis/cryptographic-properties.md`, Section 3.2, plus the
  semantic-law definitions and dependency list in
  `docs-next/analysis/profiles/cryptographic-property.json`.
- **Exact change:** publish `VCVioProviderDeclaration`,
  `VCVioBooleanCarrier`, and the corresponding Schnorr outcome-map premise in
  the exact shape already specified by the provider/carrier decision record.
  Add manifest semantic-law declarations named
  `vcvio-provider-declaration-v0` and `vcvio-boolean-carrier-v0`, both at
  revision zero; make `property-core-v0` depend on them and advance the
  property profile revision. The provider models exactly `Accepted` and
  `Rejected`; every other Fresh outcome lane remains `Unmodelled`.
- **Identity effect:** the property profile rotates, followed by each importing
  Analysis profile and every provider-bound premise, goal, intake result,
  qualified judgment, and frozen consumer identity. PIR Protocols and their
  views do not rotate solely because Analysis publishes this provider.
- **Evidence with gate IDs:** `research.analysis-premise-text-review` freezes
  the owner absence and separate fail-closed finding;
  `research.provider-interpretation` freezes the proposed finite map and the
  same publication absence.
- **Reversal condition:** withdraw this proposal if the property owner rejects
  this provider, selects a different carrier or modelled-lane set, or publishes
  another exact provider declaration that supersedes it.
- **Non-claims:** publication would make the provider-bound premise formable;
  it would not establish that premise, prove provider correspondence or theorem
  applicability, validate a backend, or establish cryptographic security.

## 5. Evidence boundary

Passing checks establish frozen agreement for the exact finite models,
current source bytes, generated certificates, and reconstructed identity
tables they inspect. A negative finding inside a passing package remains a
negative finding, and the retained provider `CannotAnswer` remains a declared
hold.

This work does not make `docs-next` normative, publish or bless an identity,
prove an owner law for arbitrary values, prove relation satisfaction, theorem
truth, protocol soundness, Fiat--Shamir security, random-oracle or QROM
applicability, compiler or backend correctness, deployment safety, or
production readiness.

## Handoff

### Files changed

- This note:
  `docs-next/notes/semantic-revalidation-and-redesign/formal-assurance-research/analysis-source-package-repins-2026-09-05.md`.
- Family-instance re-derivation:
  `evaluation/family-instance-probe/README.md`,
  `expected-findings.json`, `model.py`, and `run.py`.
- Finite-cover identity pins:
  `evaluation/finite-cover-analysis/tests/test_finite_cover.py`.
- Provider certificate regeneration:
  `evaluation/formal-provider-interpretation-f2o2/generated/certificate.json`,
  `generator.py`, and
  `evaluation/formal-provider-interpretation-arklib-f2o3/generated/certificate.json`.
- Fiat--Shamir provider re-derivation:
  `evaluation/formal-provider-interpretation-fs-arklib-f2o4/README.md`,
  `checker.py`, `generated/FiatShamirSchnorrArkLib.lean`,
  `generated/certificate.json`, and `run.py`.
- Analysis-premise source review:
  `evaluation/formal-source-analysis-premise-review-f0v2d1/README.md`,
  `expected-findings.json`, and `run.py`.
- Fiat--Shamir view determinacy:
  `evaluation/formal-source-fs-view-determinacy-f0v3/README.md`,
  `expected-findings.json`, and `run.py`.
- Holdout byte pins:
  `evaluation/formal-source-holdout-readjudication-f0v2c2/run.py`.
- Migration-text review:
  `evaluation/formal-source-migration-text-review-f0v2c1/README.md`,
  `expected-findings.json`, and `run.py`.
- Owner-view topology:
  `evaluation/formal-source-owner-view-repair-f0v/README.md`,
  `independent.py`, `model.py`, and `run.py`.
- Analysis closure and its direct dependent:
  `evaluation/k3-analysis-closure/README.md`, `reference_model.py`,
  `tests/test_reference_model.py`,
  `evaluation/k3-dependent-surfaces/README.md`, and
  `reference_model.py`.
- Migration-candidate identity controls:
  `evaluation/semantic-migration-candidate/README.md`,
  `expected-findings.json`, `independent.py`, `model.py`, and `run.py`.

No owner page, profile manifest, check manifest, lifecycle entry, evaluation
index, publication package, or directory README changed. The working tree has
37 modified tracked files and this one new note.

### Commands and outcomes

Material generation and validation commands are recorded below; read-only
inspection commands are omitted.

| Command | Exit | Wall time and outcome |
|---|---:|---|
| `python3 -B checks/run.py run --tier research-checkpoint --keep-going` with the required offline environment | 1 | 1298.127343 s runner duration; baseline 52 pass and 14 fail. |
| `python3 -B evaluation/formal-provider-interpretation-f2o2/generator.py --write` | 0 | 2.00 s; current certificate regenerated. |
| `python3 -B evaluation/formal-provider-interpretation-arklib-f2o3/generator.py --write` | 0 | 1.98 s; current certificate regenerated. |
| `python3 -B evaluation/formal-provider-interpretation-fs-arklib-f2o4/generator.py --write` | 0 | 1.24 s; Lean table and certificate regenerated. |
| `python3 -B evaluation/formal-source-fs-runtime-f0v3c/run.py --write` | 0 | 354.53 s; existing runtime corpus reproduced without a diff. |
| `python3 -B evaluation/formal-provider-interpretation-fs-arklib-f2o4/run.py --write-expected` | 0 | 177.28 s; frozen findings reproduced without a further diff. |
| Focused checks for dependent surfaces, family variation, owner topology, finite cover, view determinacy, holdout readjudication, and both migration packages | 0 | 0.04--36.12 s each; every focused check passed. |
| `python3 -B evaluation/k3-analysis-closure/run.py --check` | 0 | 1057.21 s; 215 tests passed. |
| `python3 -B checks/run.py run --check research.provider-interpretation` | 0 | 9.48 s; package passed. |
| `python3 -B checks/run.py run --check research.provider-interpretation-arklib` | 0 | 8.63 s; package passed. |
| `python3 -B checks/run.py run --check research.provider-interpretation-fs-arklib` | 0 | 178.08 s; fourteen frozen findings reproduced. |
| `python3 -B checks/run.py run --check research.analysis-premise-text-review` | 0 | 19.94 s; sixteen frozen findings reproduced, including the declared provider hold. |
| `python3 -B checks/run.py run --tier research-checkpoint --keep-going` with the required offline environment | 1 | 1629.315469 s runner duration, 1629.36 s shell wall time; 65 pass and only the excluded publication hold failed. |
| Alternate `git read-tree HEAD` and `git add -A` with clone-local object storage | 0 | 0.00 s and 0.50 s; staged view contained exactly the 37 modified files and this new note. |
| `python3 -B checks/run.py validate` under the alternate index | 0 | 0.04 s; 80 checks, six tiers, manifest valid. |
| `python3 -B checks/run.py run --tier developer` under the alternate index and required offline environment | 0 | 2.08 s; all nine checks passed. |
| `python3 -B checks/run.py run --check research.analysis-premise-text-review` under the alternate index and required offline environment | 0 | 20.10 s; the focused check passed. |
| `python3 -B checks/run.py run --tier research-checkpoint --keep-going` under the alternate index and required offline environment | 1 | 1618.460336 s runner duration, 1618.51 s shell wall time; 65 pass and only the excluded publication hold failed. |

Both post-repair checkpoints' sole red check was
`research.profile-publication`; the final alternate-index run reports exit 1
and 3.407246 s. Its 34 tests produced
eight failures: six cases of the frozen-upstream byte-identity test
(`interaction`, `canonical-framed-fiat-shamir`,
`duplex-sponge-fiat-shamir`, `public-setup`, `commitment-opening`, and
`oracle-commitment`), the public-setup descendant-rotation mutation, and
published-table reproduction. That is the requested publication hold, not an
unclassified re-pin failure.

### Aggregate outcome and non-claims

Every one of the thirteen in-scope baseline reds now passes. The family
package deliberately freezes one `Negative`, and the Analysis-premise package
deliberately retains one `CannotAnswer`; package success does not promote
either outcome. The publication check remains red and untouched. The
temporary alternate index and object store were removed after final
validation; the real index remains unchanged. Nothing was committed, pushed,
published, or proposed as a pull request.

### Surprises and corrections to the brief

- This clone has no `AGENTS.md`. The requested canonical file was read
  read-only at `/home/wonjae/code/zkc/AGENTS.md`; nothing outside this clone was
  written.
- The brief described both the Fiat--Shamir and Interaction page digests in
  the Analysis-premise review as stale. The Fiat--Shamir digest was stale, but
  the frozen Interaction digest already matched the repaired page and was
  revalidated rather than changed.
- The baseline exposed six transitive reds beyond the five named package
  groups: dependent surfaces, the family probe, joined semantic boundary,
  finite cover, owner-view topology, and migration candidate. Each is included
  in the Section 2 classification and repaired in its existing package.
- The current finite Fiat--Shamir runtime has no retrying exhaustion in the
  enumerated corpus. This replaces the old count of six but does not establish
  totality.
- The repaired Interface text closes the migration review's final
  `CannotAnswer`; no additional owner delta is needed for that package. The
  separate Analysis provider declaration remains absent and is retained as
  the Proposed delta above.
- No package was added, so lifecycle count pins, `evaluation/README.md`, and
  both manifests correctly remain unchanged.

Suggested commit subject for Main:
`test: re-pin the analysis packages to the repaired owner text`.

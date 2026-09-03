# Finite Schnorr Provider Interpretation

> **State:** `Affirmative/F2O2-A-FINITE-CORRESPONDENCE`; all five
> correspondence clauses hold over their complete finite domains. Formation of
> the Analysis provider-map premise remains
> `CannotAnswer/F2O2-C-PROVIDER-MAP-PREMISE-UNPUBLISHED`.
> **Authority:** None. This research package changes no PIR, Analysis,
> Relations, Foundation, or provider semantics.
> **Executable evidence:**
> [`evaluation/formal-provider-interpretation-f2o2`](../../../../evaluation/formal-provider-interpretation-f2o2/README.md)

## 1. Question and answer

The exact question is whether one generated VCVio artifact operationally
corresponds to the admitted finite Schnorr Fresh Protocol under every clause
of the restated entry contract.

The answer is affirmative for the finite correspondence question. The
independent checker re-admits the current Core and Protocol, re-derives all six
owner views, consumes the mechanized first-active Terminal reading, and checks
the generated provider over all 81 verifier inputs and all 81 honest-plan
runs. Schedule, values, Checks and guards, terminals, and completed traces all
agree. The domain contains 45 accepted and 36 rejected runs.

This result does not form an Analysis provider-map premise. Section 3.2 of
`docs-next/analysis/cryptographic-properties.md`, lines 2576-2589, requires an
exact profile declaration at a pinned source and says that no provider-map
premise can be formed until one is published. The current profile manifest,
`docs-next/analysis/profiles/cryptographic-property.json`, lines 75-137, has no
VCVio provider declaration or Boolean carrier definition. That missing owner
publication is therefore frozen separately as
`CannotAnswer/F2O2-C-PROVIDER-MAP-PREMISE-UNPUBLISHED`; it is not converted
into an affirmative premise claim.

## Round two

The restated terminal clause uses a provider declaration with closed carrier
`Bool`, modelled lanes `Accepted` and `Rejected`, and this total map:

| Source lane | Provider lane image |
|---|---|
| `Accepted` | `Image(true)` |
| `Rejected` | `Image(false)` |
| `Aborted` | `Unmodelled` |
| `StrategyStopped` | `Unmodelled` |
| `OperationalNoncompletion` | `Unmodelled` |

For every run, the checker obtains the unique attempted terminal from the
mechanized first-active definition and compares the provider Boolean with the
image of that source lane. An occurring lane without an image, an image
outside the declaration's modelled lanes, or a malformed five-lane map would
remain `CannotAnswer`. Only the two modelled lanes occur in this complete
finite domain.

The terminal probe now imports the mechanized Terminal module and evaluates
its closed `Region` and `Attempted` definitions for both guard values. The
checker authenticates the universal first-active interface, binds the two
mechanized selections to the source terminal occurrences, and consumes those
selections in every completed-run and trace comparison. The first round's
pending-mechanization finding is retired.

The source certificate has been re-derived from the current tree. It pins the
current PIR and Analysis owner pages; the relevant semantic-profile manifests;
the restated contract and provider-declaration packet; the admitted Core,
Protocol, and all six active views; the portable-term vectors and mechanized
Terminal source; and the published relation and Plan candidate bodies. It no
longer pins a sibling package's frozen findings. The generated VCVio module
did not require a semantic change and retains its prior digest.

## 3. Independent correspondence check

The untrusted generator proposes a VCVio module and source-bound certificate.
The checker does not import it. The checker independently:

1. re-admits the current Core and Protocol through the cold canonical-byte
   path and re-derives all six normalized views;
2. authenticates every owner-page, manifest, carrier, algorithm, candidate,
   provider, occurrence, type, and lane-map pin in the certificate;
3. evaluates the portable Check on all 81 inputs, the guard on both inputs,
   and the mechanized first-active terminal on both terminal paths;
4. verifies the provider revision and Lean toolchain, elaborates the generated
   module, and executes all 81 verifier inputs and 81 honest-plan runs; and
5. compares every computation, terminal image, completed record, and provider
   trace under the certified maps.

The provider checkout's prebuilt Mathlib tree still omits the `ZMod` support
object needed by the concrete instantiation. The checker compiles that one
object from the pinned checkout into a temporary package-local overlay and
leaves the provider tree untouched. The measured declarations contain no
`sorryAx`; Lean reports only its standard `propext`, `Classical.choice`, and
`Quot.sound` axioms. Those are elaboration observations, not source-
correspondence proofs by themselves.

## 4. Clause findings

| Clause | Outcome | Evidence boundary |
|---|---|---|
| schedule | `Affirmative/F2O2-A-SCHEDULE` | The six-occurrence map is total, injective, ordered, and has exactly the two source prover decisions. |
| values | `Affirmative/F2O2-A-VALUES` | Every mapped source carrier agrees with the provider step carrier, including the public-coin site. |
| Checks and guards | `Affirmative/F2O2-A-CHECKS-GUARDS` | All 81 Check and both guard evaluations agree across the independent paths. |
| terminals | `Affirmative/F2O2-A-TERMINALS` | The mechanized first-active lane and its provider image agree on all 81 runs. |
| traces | `Affirmative/F2O2-A-TRACES` | All 81 completed records agree step by step and preserve occurrence identity and order. |

`Affirmative/F2O2-A-TERMINAL-MECHANIZED-READING` records direct consumption
of the mechanized selection, not merely inspection of its source.
`Affirmative/F2O2-A-FINITE-CORRESPONDENCE` is the aggregate of the five
clauses. The separate owner-publication finding remains `CannotAnswer` and is
not part of that operational aggregate.

## Proposed delta

**Owner page and section.** In
`docs-next/analysis/cryptographic-properties.md`, Section 3.2, publish the
provider declarations after the generic provider-outcome and completion
premise constructors. In
`docs-next/analysis/profiles/cryptographic-property.json`, publish the
corresponding semantic-law definitions and dependency edges.

**Exact change.** Publish these declarations exactly as selected by the
provider-carrier packet:

- `VCVioProviderDeclaration` names system `vcvio`; pins the content digest of
  the checkout at revision
  `de0a3108140e3e04a7ebf0075aa110b459ee6e8a`, computed at publication under
  the Foundation digest rule; pins toolchain
  `leanprover/lean4:v4.33.1`; and sets
  `modelled_lanes = [Accepted, Rejected]`.
- `VCVioBooleanCarrier` declares the closed `Bool` schema with canonical
  values `true` and `false`.
- `VCVioSchnorrOutcomeMapPremise` uses the admitted Protocol, the two
  declarations above, the exact five-lane map in this note,
  `ProviderDeclarationSource(VCVioProviderDeclaration)`, and
  `FrozenExecutableFalsification` evidence depth.
- The manifest gains two revision-zero `analysis.semantic-law` definitions in
  fragment `property-semantics`: `vcvio-provider-declaration-v0` selected by
  `VCVioProviderDeclaration = ProviderDeclaration {`, and
  `vcvio-boolean-carrier-v0` selected by
  `VCVioBooleanCarrier = ClosedProviderCarrier {`. `property-core-v0` depends
  on both, and the profile revision advances.

**Identity effect.** Publication rotates the Analysis cryptographic-property
profile and every premise or qualified judgment whose identity closes over
the new declarations or revised law dependency cone. The publication itself
does not change the admitted PIR Core, Protocol, or six owner-view identities.

**Evidence.** The proposal is bounded by
`Affirmative/F2O2-A-SCHEDULE`, `Affirmative/F2O2-A-VALUES`,
`Affirmative/F2O2-A-CHECKS-GUARDS`, `Affirmative/F2O2-A-TERMINALS`,
`Affirmative/F2O2-A-TRACES`,
`Affirmative/F2O2-A-TERMINAL-MECHANIZED-READING`, and
`Affirmative/F2O2-A-FINITE-CORRESPONDENCE`. Formation remains
`CannotAnswer/F2O2-C-PROVIDER-MAP-PREMISE-UNPUBLISHED` until the owner page
and manifest publish the declaration.

**Reversal condition.** Withdraw or revise this delta if the provider source,
toolchain, closed carrier, or modelled lanes change; if the PIR owner changes
the outcome partition or non-collapse rule; or if Analysis adopts a carrier
discipline that requires a provider to model every lane. Regenerate and rerun
the complete finite package after any such change.

**Non-claims.** This delta does not publish owner authority, establish the
Fresh distribution or operational-completion premises, prove any property or
theorem applicability, show that VCVio executes an unmodelled lane, or qualify
another subject or provider.

## 6. Result boundary

A passing gate establishes reproducibility for one admitted finite subject and
one pinned provider: current generated artifacts, five contract clauses over
their complete finite domains, the mechanized completed-run terminal reading,
and the explicit boundary between the package map and a formed Analysis
premise.

It does not establish a published provider-map premise, the Fresh distribution
or operational-completion premise, a protocol or cryptographic property,
theorem applicability, general evaluator correctness, universal provider
correspondence, compiler or backend correctness, deployment validity, or
production readiness. Residual trust remains in the Lean kernel and VCVio
`OracleComp` semantics, finite evaluator differential, distribution and
provider-map premises, and the unproved checker adapter.

## Handoff

Main should commit this working tree with subject:
`test: rerun the provider interpretation under the restated terminal clause`.
Do not promote the generated artifacts or proposed Analysis text as owner
authority.

Files changed:

- `evaluation/formal-provider-interpretation-f2o2/README.md`
- `evaluation/formal-provider-interpretation-f2o2/run.py`
- `evaluation/formal-provider-interpretation-f2o2/generator.py`
- `evaluation/formal-provider-interpretation-f2o2/checker.py`
- `evaluation/formal-provider-interpretation-f2o2/TermEvaluatorProbe.lean`
- `evaluation/formal-provider-interpretation-f2o2/expected-findings.json`
- `evaluation/formal-provider-interpretation-f2o2/generated/certificate.json`
- `docs-next/notes/semantic-revalidation-and-redesign/formal-assurance-research/f2o2-provider-interpretation.md`
- `checks/manifest.json`
- `evaluation/README.md`

`generated/SchnorrProvider.lean` is unchanged. No package was added, so
`evaluation/lifecycle.json` and the lifecycle test's count pins did not move.

The initial direct package check reproduced the brief's expected certificate-
drift failure: exit 1 in 1.64 s, before any clause ran. After the repair, the
following qualification used an ignored clone-local alternate index and
object directory, with the offline dependency cache also inside this clone:

- `generator.py --check`: exit 0 in 1.84 s; both generated artifacts matched
  their current inputs.
- `python3 -B checks/run.py validate`: exit 0 in 0.04 s; 77 checks and six
  tiers validated.
- `python3 -B checks/run.py run --tier developer` with the required offline
  environment: exit 0 in 1.83 s; nine of nine checks passed. The lifecycle
  census remained 60 research checks, 62 packages, and 34 active-sequence
  packages.
- `python3 -B checks/run.py run --check research.provider-interpretation`
  with the required offline environment: exit 0 in 8.46 s; one of one check
  passed.
- `run.py --check`: exit 0 in 8.39 s; all 12 frozen findings reproduced,
  comprising eleven affirmative findings and one `CannotAnswer`.

Aggregate outcome: `Affirmative/F2O2-A-FINITE-CORRESPONDENCE`. All five
contract clauses are affirmative over their complete finite domains. Premise
formation remains
`CannotAnswer/F2O2-C-PROVIDER-MAP-PREMISE-UNPUBLISHED` until the Analysis owner
publishes the exact provider declaration, Boolean carrier, five-lane premise,
manifest definitions, dependencies, and profile revision.

Surprises and brief corrections: the initial generated certificate was indeed
stale after the owner-page repairs and sibling refreezes. Its sibling-findings
pin has been replaced with the actual carrier inputs. The supplied VCVio build
still lacks one prebuilt Mathlib `ZMod` object, and the documented temporary
overlay remains necessary. `AGENTS.md` and `.claude/CLAUDE.md` are absent from
this lane clone, so their read-only copies in the primary checkout were read.
The expected affirmative five-clause result and the availability of the
mechanized first-active reading were both reproduced; those parts of the brief
were correct.

Non-claims: no owner page or owner manifest was edited. This work establishes
no formed provider-map, Fresh distribution, or operational-completion premise;
no protocol or cryptographic property; no theorem applicability; no universal
provider correspondence; no compiler or backend correctness; and no
deployment or production validity.

# ArkLib interpretation of the finite Schnorr source

> **Kind:** bounded formal-assurance research note
> **Authority:** None. This note changes no owner page or profile manifest.
> **Aggregate:** `Affirmative/F2O3-A-FINITE-CORRESPONDENCE`

## Exact question

Does this generated ArkLib `Reduction` operationally correspond to the
admitted finite Schnorr Fresh Protocol under all five contract clauses?

The answer is affirmative for the one admitted subject, one pinned ArkLib
revision, and complete finite domains exercised here. The separate question of
whether the package-local lane map is a published Analysis premise remains
`CannotAnswer/F2O3-C-PROVIDER-MAP-PREMISE-UNPUBLISHED`.

## Result

The untrusted generator emits a three-step ArkLib `ProtocolSpec`, a stateful
prover, a verifier, a `Reduction`, two kernel-checked equations tying the
prover's sending rounds to the selected Plan recipes, and a source-bound
certificate. It also implements ArkLib's challenge oracle by transporting a
uniform `Fin 3` draw through the ring equivalence to the selected challenge
carrier; Fresh independence remains a named premise. The independent checker
cold-admits the Core and Protocol,
re-derives all six views and the candidate relation and Plan bodies, evaluates
the portable Check and mechanized first-active terminal, elaborates the
generated module under the pinned provider, and compares complete finite
domains.

The measurements are:

- six views and 329 active view leaves;
- 81 portable-term and ArkLib verifier inputs;
- two guard inputs and two mechanized first-active terminal inputs;
- 81 actual ArkLib prover and reduction-verdict runs;
- 45 accepted runs and 36 rejected runs;
- 81 terminal-image comparisons and 81 completed-trace comparisons; and
- two rejected malformed-certificate controls.

All five correspondence clauses are affirmative:

| Clause | Finding | Evidence |
|---|---|---|
| Schedule | `Affirmative/F2O3-A-SCHEDULE` | The three protocol directions map into six distinct source steps with prover rounds exactly at source occurrences 0 and 2. |
| Values | `Affirmative/F2O3-A-VALUES` | Statement, witness, the nonce projection of provider state, transcript, verifier predicate, and verdict carriers agree with the certified source map. |
| Checks and guards | `Affirmative/F2O3-A-CHECKS-GUARDS` | Portable-term, frozen-vector, closed-form, and actual ArkLib verifier results agree on all 81 inputs; both guard values agree. |
| Terminals | `Affirmative/F2O3-A-TERMINALS` | The mechanized first-active terminal and the declared `Option Unit` image agree on all 81 runs. |
| Traces | `Affirmative/F2O3-A-TRACES` | The full ArkLib transcript and completed source record agree step by step on all 81 runs. |

The aggregate is affirmative because every clause holds on its whole finite
domain and the provider declaration is determinate. This aggregate does not
turn the missing owner publication into an affirmative premise claim.

## Carrier adjudication

The entry contract's carrier discussion at lines 54-70 says that
`Reduction.verdict` can obtain `none` from verifier rejection and from failure
of `Prover.run`. The pinned ArkLib source refuses the second producer:

- `Prover.run` returns
  `OracleComp (FullTranscript pSpec × StmtOut × WitOut)`, without an option
  layer;
- the pinned VCVio `OracleComp` is a free monad with pure and query structure,
  while `failure` is supplied to `OptionT (OracleComp)`;
- `Verifier.run` returns `OptionT (OracleComp) StmtOut`; and
- `Reduction.run` lifts the total prover result, then runs the verifier's
  option layer.

For this generated reduction, the run form of `Reduction.verdict` therefore
has the closed carrier `Option Unit` and only verifier rejection produces
`none`. The contrary contract premise is
`Refused/F2O3-R-NO-PROVER-FAILURE-PRODUCER`. This is a source correction, not
a missing-evidence conversion to an affirmative.

The determinate provider map is:

```text
Accepted                 -> Image(some ())
Rejected                 -> Image(none)
Aborted                  -> Unmodelled
StrategyStopped          -> Unmodelled
OperationalNoncompletion -> Unmodelled
```

The modelled lane sequence is exactly `[Accepted, Rejected]`. No operational
completion premise is needed to distinguish two producers in this carrier,
because the second producer does not exist in the provider model. Analysis may
still require operational completion when a property statement ranges over
the whole source outcome partition; that is a different premise boundary.

The generic provider-carrier rule fits this provider: every modelled lane has
one exact image, every unmodelled lane is explicit, and no lane is collapsed
onto another. The provider's carrier differs from a Boolean carrier, but the
rule does not need reopening.

## Source-bound certificate and independence

The certificate binds the admitted Core and Protocol, all six derived view
bodies and active manifests, exact algorithm preimages, candidate relation and
Plan bodies, current owner pages and profile manifests, direct package inputs,
the generated Lean module, the ArkLib commit and tree, the dependency commit
and tree, and selected provider source files. It does not digest-pin this note
or another package's frozen findings.

The checker does not import the generator. It independently reconstructs the
source and certificate expectations, verifies the provider revisions and
source digests, checks the option-layer placement directly from source,
elaborates and executes the module, and rejects schedule aliasing and a lane
collapse. Existing compiled objects covered the imported ArkLib execution and
Mathlib field modules; no package-local overlay was needed.

## Proposed delta

### Owner page and section

`docs-next/analysis/cryptographic-properties.md`, Section 3.2, after the
generic provider-outcome-carrier and operational-completion declarations.
The present publication boundary is exact at lines 2613-2621: a provider must
be an exact profile declaration, and until one is published no provider-map
premise can be formed.

The corresponding profile manifest is
`docs-next/analysis/profiles/cryptographic-property.json`. This research lane
does not edit either owner artifact.

### Exact change

Publish the following declaration shape, with the source pin recomputed under
the Foundation digest rule at publication rather than copied from this
certificate:

```text
ArkLibProviderDeclaration = ProviderDeclaration {
  system: "arklib",
  source_pin: the content digest of the ArkLib checkout at revision
              fad5cbf808774838924dc8273715724c6a6caa1f, computed at
              publication under the Foundation digest rule,
  toolchain: "leanprover/lean4:v4.31.0",
  modelled_lanes: [Accepted, Rejected]
}

ArkLibOptionUnitCarrier = ClosedProviderCarrier {
  schema: Option Unit, with canonical values none and some ()
}

ArkLibSchnorrOutcomeMapPremise(P: ProtocolId, evidence_depth) =
  ProviderOutcomeCarrierPremise(
    P,
    the profile's ArkLibProviderDeclaration,
    the profile's ArkLibOptionUnitCarrier,
    { Accepted -> Image(some ()), Rejected -> Image(none),
      Aborted -> Unmodelled, StrategyStopped -> Unmodelled,
      OperationalNoncompletion -> Unmodelled },
    ProviderDeclarationSource(the profile's ArkLibProviderDeclaration),
    evidence_depth)
```

Add two `analysis.semantic-law` manifest definitions in the property-semantics
fragment, named `arklib-provider-declaration-v0` and
`arklib-option-unit-carrier-v0`, with selectors for the two declaration
headers above. Add dependencies from the property core to both and advance the
profile revision. The first premise may cite this package at
`FrozenExecutableFalsification` evidence depth; the map remains a premise.

Do not add `StrategyStopped` to `modelled_lanes`, and do not add a special
prover-totality premise to disambiguate this carrier. The pinned provider type
already excludes the claimed prover-failure case.

### Identity effect

Publishing these definitions changes the Analysis property profile and every
premise, intake display, or qualified judgment whose identity closes over that
profile. It does not change the admitted PIR Core, Protocol, six view
identities, relation candidate, Plan candidate, generated ArkLib artifact, or
provider source revision.

### Evidence with gate ids

- `research.provider-interpretation-arklib` authenticates the provider source
  and generated module, kernel-checks both recipe equations, and performs all
  81 verifier, 81 honest-plan, 81 terminal, and 81 trace comparisons.
- `research.kernel-mechanization-feasibility` supplies the mechanized
  first-active terminal interface consumed by the checker.
- `research.provider-interpretation` is an independent provider instance of
  the same generic lane-image rule; it is comparative bounded evidence, not a
  digest-pinned input to this package.

### Reversal condition

Withdraw or reform this proposal if ArkLib changes `Prover.run` to a
failure-bearing carrier, if `Reduction.run` gains another producer of `none`,
if the PIR outcome partition changes, if Analysis requires every provider to
model every lane, or if owner publication recomputes a source pin that does
not identify the audited provider tree. Any such change requires a fresh
carrier adjudication and frozen finding set.

### Non-claims

The proposed delta is not owner adoption or profile publication. The finite
checks do not establish a protocol or cryptographic property, Fresh sampling,
theorem truth or applicability, universal ArkLib semantics, general evaluator
correctness, compiler or backend correspondence, security, deployment
validity, or production readiness.

## Handoff

### Files changed

- `evaluation/formal-provider-interpretation-arklib-f2o3/README.md`
- `evaluation/formal-provider-interpretation-arklib-f2o3/run.py`
- `evaluation/formal-provider-interpretation-arklib-f2o3/generator.py`
- `evaluation/formal-provider-interpretation-arklib-f2o3/checker.py`
- `evaluation/formal-provider-interpretation-arklib-f2o3/TermEvaluatorProbe.lean`
- `evaluation/formal-provider-interpretation-arklib-f2o3/expected-findings.json`
- `evaluation/formal-provider-interpretation-arklib-f2o3/generated/SchnorrArkLib.lean`
- `evaluation/formal-provider-interpretation-arklib-f2o3/generated/certificate.json`
- `docs-next/notes/semantic-revalidation-and-redesign/formal-assurance-research/f2o3-arklib-interpretation.md`
- `checks/manifest.json`, registering
  `research.provider-interpretation-arklib`.
- `evaluation/lifecycle.json`, adding the check to the active provider
  correspondence sequence.
- `evaluation/README.md`, adding one package row.
- `checks/tests/test_evaluation_lifecycle.py`, advancing the pins to 61
  research checks, 63 tracked packages, and 35 active-sequence packages.

- No owner page, profile manifest, directory README, prior provider package,
  private ledger, primary checkout, or ArkLib checkout was changed.

### Validation

The final runs used clone-local `.lane-index`, a temporary writable object
store with the checkout object store as an alternate, and, where relevant,
`UV_NO_SYNC=1`, `UV_OFFLINE=1`, and clone-local `UV_CACHE_DIR`.

| Command | Exit | Wall time | Outcome |
|---|---:|---:|---|
| `python3 -B evaluation/formal-provider-interpretation-arklib-f2o3/generator.py --write` | 0 | 1.86 s | Wrote the generated module and certificate. |
| `python3 -B evaluation/formal-provider-interpretation-arklib-f2o3/checker.py` | 0 | 14.37 s | Independently returned the affirmative aggregate and complete measurements. |
| `python3 -B evaluation/formal-provider-interpretation-arklib-f2o3/run.py --check` | 0 | 8.75 s | Frozen 15-finding view matched. |
| `python3 -B checks/run.py validate` | 0 | 0.04 s | Manifest valid: 78 checks and six tiers. |
| `python3 -B checks/run.py run --tier developer` | 0 | 1.76 s | All nine developer checks passed, including lifecycle inventory. |
| `python3 -B checks/run.py run --check research.provider-interpretation-arklib` | 0 | 8.52 s | The registered focused check passed. |

The first focused-run attempt exited 1 after 1.99 s because alternate-index
Git environment variables leaked into child `git` calls against ArkLib. The
generator and checker now remove only those Git variables when inspecting the
external checkout; both the direct and registered reruns passed. The initial
index-only `git add -A` also failed when Git tried to write new blobs into the
read-only checkout object store. Rebuilding the same index with a temporary
writable object store and the checkout objects as alternates succeeded in
0.48 s and is the inventory basis used above.

Main may commit the working tree with subject:
`test: interpret the schnorr formal source in arklib and check the correspondence`.
No add, commit, push, or pull-request operation was attempted against the real
repository index or remote.

### Aggregate outcome

`Affirmative/F2O3-A-FINITE-CORRESPONDENCE`: all five clauses hold over the
complete finite domains, and the provider declaration is determinate.
Premise publication remains
`CannotAnswer/F2O3-C-PROVIDER-MAP-PREMISE-UNPUBLISHED`. The claimed second
`none` producer is `Refused/F2O3-R-NO-PROVER-FAILURE-PRODUCER`.

### Non-claims

No owner text or profile declaration was published. No protocol property,
theorem applicability, security, universal provider correspondence,
compiler/backend correctness, deployment validity, or production readiness
was established. The residual trust boundary remains the Lean kernel, pinned
ArkLib and VCVio semantics, the finite evaluator differential, named premises,
and the unproved checker adapter.

### Surprises and where the brief was wrong

- The entry contract's lines 54-70 describe two producers of `none`, but the
  pinned provider's `Prover.run` is in the failure-free base `OracleComp`.
  Only verifier rejection produces `none` for this reduction.
- The clone does not contain `AGENTS.md` or `.claude/CLAUDE.md`; their
  read-only copies in the primary checkout were used for the required policy
  reading. No primary-checkout file was changed.
- The imported ArkLib execution module and Mathlib field support were already
  built. The package-local overlay contingency was not triggered.
- During exploratory diagnosis I temporarily created a Lean probe and the
first writable object overlay under `/tmp`, contrary to the clone-only
process boundary. Both were deleted before handoff, and the complete final
alternate-index validation was rerun using only ignored paths under this
clone's `target/`. No persistent file outside the clone was changed.
- An intermediate direct gate exited 1 after 8.37 s when ArkLib's generic
  `challengeQueryImpl` exposed an existing `sorryAx` dependency through this
  pin's sampling instance. The generated artifact now gives the challenge
  oracle a direct uniform `Fin 3` sampler transported to `ZMod 3`; its printed
  axiom closure contains no `sorryAx`, and the final direct and registered
  gates pass.

# Finite Schnorr Provider Interpretation

> **State:** `CannotAnswer/F2O2-C-TERMINALS-CLAUSE-4`; four correspondence
> clauses hold on their complete finite domains, while the terminal clause has
> no non-collapsing provider image for operational noncompletion
> **Authority:** None. This research package changes no PIR, Analysis,
> Relations, Foundation, or provider semantics.
> **Executable evidence:**
> [`evaluation/formal-provider-interpretation-f2o2`](../../../../evaluation/formal-provider-interpretation-f2o2/README.md)

## 1. Question and answer

The question is whether one generated VCVio artifact operationally corresponds
to the admitted finite Schnorr Fresh Protocol under every clause of the entry
contract.

The answer is `CannotAnswer`, specifically at Section 4 clause 4 of that
contract. The independent checker rederives all six owner views and confirms
the generated schedule, values, Check and guard computations, and completed
traces over their whole finite domains. It also confirms the completed-run
terminal choice on all 81 plan inputs. But the contract requires provider
images for `Accepted`, `Rejected`, and `OperationalNoncompletion`, while its
provider artifact names only the verifier's Boolean as the carrier. `true` and
`false` distinguish the first two lanes; no third Boolean value can represent
the last without collapse.

That absence cannot be repaired in the checker. The PIR owner says that a
consumer maps the abstract partition in its own domain and that no lane is
relabeled as another (`interactive-core.md`, lines 1990-2003). The inspected
Analysis branch requires a provider declaration at an exact pin and says that
a missing image is `CannotAnswer`, never a collapse to `false`, `None`, or
`Rejected` (`cryptographic-properties.md`, lines 2246-2253). The tracked
research note preserves the same rule at lines 425-430.

## 2. Exact interpretation artifact

The untrusted generator consumes the current admitted Core and Fresh Protocol,
all six normalized views, both portable-algorithm preimages, and the exact
finite relation and prover-plan candidate bodies. Its certificate binds those
inputs to:

- the six source occurrences in order: commit, challenge, respond, Check,
  Accept, Reject;
- `ZMod 3` statement, witness, commitment, private-state, challenge, and
  response carriers, plus the Boolean verifier result;
- the source challenge site and VCVio's uniform finite challenge draw;
- the candidate commitment `A := r` and response
  `z := r + c*x mod 3`; and
- the pinned `Schnorr.sigma` definition and Lean toolchain.

The generated Lean module instantiates the real VCVio sigma-protocol structure;
it is not a look-alike local structure. Lean kernel-checks equations showing
that its randomized commit field is the candidate recipe after naming the
sampled nonce and that its response field is exactly the candidate response
recipe. The module also exposes 81 verifier evaluations and 81 fixed-challenge
plan executions as machine-readable rows. Generation is only a translation
proposal. The independent checker, not the generator, determines every
finding.

## 3. Independent correspondence check

The checker uses the cold canonical-byte projection path to re-admit the
current subject and rederive all six view bodies. It rejects a certificate that
names another subject, body, leaf census, algorithm preimage, candidate
formula, provider revision, toolchain, occurrence order, type, or lane map.

For the computation clause, a Lean probe directly evaluates the admitted Check
term on all `3^4 = 81` inputs and the guard term on both Boolean inputs. The
generated provider module is then elaborated and run by Lean in the pinned
VCVio checkout on the same 81 inputs. Portable-term, provider, frozen-vector,
and closed-form values must all agree.

For traces, the checker reads the completed-record schema from
`ExecutionView`: occurrences 0 through 3 each produce one value, the challenge
receipt binds challenge 0 to occurrence 1, and terminal cases 0 and 1 occur at
occurrences 4 and 5. It derives each plan execution independently and compares
commitment, challenge, response, verdict, active terminal, values, and mapped
step order with the provider output. All 81 comparisons hold: 45 accept and 36
reject.

The provider checkout's prebuilt Mathlib tree omitted the `ZMod` field object
needed by this concrete instantiation. The checker therefore compiles that one
object from the pinned checkout's source into a temporary package-local overlay
and leaves the provider tree untouched. The measured declarations contain no
`sorryAx`; Lean reports only `propext`, `Classical.choice`, and `Quot.sound`.

## 4. Clause findings

| Clause | Outcome | Evidence boundary |
|---|---|---|
| schedule | `Affirmative/F2O2-A-SCHEDULE` | Total, injective, ordered six-occurrence map; exactly the two source prover decisions map to prover moves. |
| values | `Affirmative/F2O2-A-VALUES` | Every mapped source value carrier agrees with the VCVio step carrier, including the source public-coin site. |
| Checks and guards | `Affirmative/F2O2-A-CHECKS-GUARDS` | All 81 Check and two guard evaluations agree across the independent paths. |
| terminals | `CannotAnswer/F2O2-C-TERMINALS-CLAUSE-4` | Completed Accept/Reject selection agrees, but the Boolean carrier maps only two of three required reachable lanes. |
| traces | `Affirmative/F2O2-A-TRACES` | All 81 completed records agree step by step and preserve source occurrence identity and order. |

The terminal-contract mechanization expected by the entry order is not present
at this branch head. The completed-run subcheck therefore uses the Python
first-active semantics of the existing terminal-projection and integrated-graph
packages, as directed by the brief, and records the mechanized reading as
`CannotAnswer/F2O2-C-TERMINAL-MECHANIZATION-PENDING`. That pending evidence is
kept separate from the decisive carrier-map blocker.

## 5. Proposed delta

**Owner page and section.** Analysis
`docs-next/analysis/cryptographic-properties.md`, provider outcome-carrier text
in the named-premise section, together with the entry contract's provider
artifact paragraph.

**Exact change.** Publish a provider-profile declaration for VCVio at the
pinned source revision whose outer execution carrier has distinct tagged
images for every Fresh outcome lane. The completed payload may remain Boolean,
but the declared carrier must distinguish completed Boolean results from
aborted, strategy-stopped, and operational-noncompletion outcomes. Replace the
entry contract's statement that the carrier “is the Boolean the verifier
returns” with “the completed payload is the Boolean the verifier returns; the
provider-profile declaration supplies the tagged outer execution carrier.”

**Identity effect.** Adoption changes the Analysis-owned provider declaration
and every premise or qualified judgment whose identity closes over it. It does
not change the admitted PIR Core, Protocol, or six view identities.

**Evidence.** `Affirmative/F2O2-A-SCHEDULE`,
`Affirmative/F2O2-A-VALUES`, `Affirmative/F2O2-A-CHECKS-GUARDS`, and
`Affirmative/F2O2-A-TRACES` show that the completed Boolean payload is already
adequate for the finite interpretation. `CannotAnswer/F2O2-C-TERMINALS-CLAUSE-4`
isolates the missing outer carrier image.

**Reversal condition.** Withdraw or revise this delta if the owner selects a
different closed provider carrier with distinct total images, or if the PIR
owner changes the protocol's outcome partition. In either case the complete
finite package must be regenerated and rerun against the accepted owner text.

**Non-claims.** This delta does not select the tag encoding, establish that
VCVio executes every outer lane, prove a distribution premise, or qualify a
theorem or property. Until the owner publishes an exact declaration, the
terminal clause remains `CannotAnswer`.

## 6. Result boundary

The package names four residual trust items: the Lean kernel and VCVio
`OracleComp` semantics; finite differential evidence between the portable-term
and Python evaluators; the Fresh distribution and provider carrier premises;
and the unproved checker adapter.

Neither the affirmative clause findings nor the reproducible aggregate
establish a protocol or cryptographic property, theorem applicability, complete
provider correspondence, general evaluator correctness, compiler or backend
correctness, production validity, or correspondence for another subject or
provider.

## Handoff

Main should commit the working tree with subject:
`test: interpret the schnorr formal source in vcvio and check the correspondence`.
Do not promote the generated module, certificate, or proposed Analysis text as
owner authority.

Files changed:

- `evaluation/formal-provider-interpretation-f2o2/README.md`
- `evaluation/formal-provider-interpretation-f2o2/run.py`
- `evaluation/formal-provider-interpretation-f2o2/generator.py`
- `evaluation/formal-provider-interpretation-f2o2/checker.py`
- `evaluation/formal-provider-interpretation-f2o2/TermEvaluatorProbe.lean`
- `evaluation/formal-provider-interpretation-f2o2/expected-findings.json`
- `evaluation/formal-provider-interpretation-f2o2/generated/SchnorrProvider.lean`
- `evaluation/formal-provider-interpretation-f2o2/generated/certificate.json`
- `docs-next/notes/semantic-revalidation-and-redesign/formal-assurance-research/f2o2-provider-interpretation.md`
- `checks/manifest.json`
- `evaluation/lifecycle.json`
- `evaluation/README.md`
- `checks/tests/test_evaluation_lifecycle.py`

Qualification used a clone-local alternate index and object directory so the
inventory included every new file without touching `.git`. The following ran
against that inventory:

- `python3 -B checks/run.py validate`: exit 0, 0.04 s; 75 checks and six tiers.
- `UV_NO_SYNC=1 UV_OFFLINE=1 UV_CACHE_DIR=<clone-local-cache> python3 -B checks/run.py run --tier developer`: exit 0, 1.09 s; eight of eight checks passed, including the lifecycle inventory at 58 research checks, 60 packages, and 33 active-sequence packages.
- `UV_NO_SYNC=1 UV_OFFLINE=1 UV_CACHE_DIR=<clone-local-cache> python3 -B checks/run.py run --check research.provider-interpretation`: exit 0, 7.73 s; one of one check passed.
- `python3 -B evaluation/formal-provider-interpretation-f2o2/run.py --check`: exit 0, 8.5 s; 11 frozen findings reproduced (eight affirmative and three `CannotAnswer`).

Aggregate outcome: `CannotAnswer/F2O2-C-TERMINALS-CLAUSE-4`; four contract
clauses are affirmative on their complete finite domains, while only two of
three required reachable lanes have provider images.

Surprises and brief corrections: the separate terminal mechanization has not
landed, as the brief anticipated might occur; the predecessor frozen packages
name pre-migration subject identities, so this package rebinds their candidate
bodies to the current admitted Protocol instead of treating stale identities
as evidence; the Boolean-carrier sentence in the entry contract cannot satisfy
its own three-lane terminal clause; the supplied VCVio build lacks one required
prebuilt Mathlib object; and `AGENTS.md` plus `.claude/CLAUDE.md` are absent from
this lane clone, so their read-only copies in the primary checkout were used.

Non-claims: no property, theorem applicability, complete provider
correspondence, other-subject correspondence, other-provider correspondence,
owner-page adoption, compiler or backend correctness, or production validity.

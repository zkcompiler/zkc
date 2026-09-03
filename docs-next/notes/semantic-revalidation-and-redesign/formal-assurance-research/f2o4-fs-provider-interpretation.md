# ArkLib interpretation of the finite Fiat--Shamir protocol

> **State:** `Affirmative/F2O4-A-FS-FINITE-CORRESPONDENCE`; all five
> correspondence clauses hold on the complete one-shot finite domain.
> **Authority:** None. This research package changes no owner page, profile
> manifest, publication table, or normative provider declaration.
> **Executable evidence:**
> [`evaluation/formal-provider-interpretation-fs-arklib-f2o4`](../../../../evaluation/formal-provider-interpretation-fs-arklib-f2o4/README.md)

## 1. Exact question and answer

Does ArkLib's Fiat--Shamir transform of the generated finite Schnorr
reduction operationally correspond to the admitted finite canonical-framed
Protocol, run for run, when ArkLib's abstract challenge oracle is instantiated
by the migrated construction's exact derivation function?

Yes, for the exact one-shot construction and complete finite corpus selected
by the entry contract. The independent checker finds exact agreement for
schedule, values, oracle points, checks and terminals, and traces across all
54 source runs.

## 2. Source subject and table authentication

The source runtime now re-admits its retained retrying construction under the
owner-fixed application-domain body and adds a second construction with one
maximum draw, unconditional acceptance, and total decoding. Both reuse the
admitted additive `Z/3Z` Schnorr Core. The one-shot identities are:

```text
TranscriptConstruction: zkcidv0:pir.transcript-construction:eaebbb902e26db8af22147b867676769bdeebfa9dc95c58af007b25d53876a78
FS Protocol:            zkcidv0:pir.protocol:4a80c29a982ac7ba9dfca5fd86d7c7f1507e2005da407b14691191f79f9bfc21
```

The checker loads the source model, executor, replay, and views cold. It
reconstructs the admitted subject, executes and independently replays all 54
one-shot cases, compares each complete record to the frozen run set, rebuilds
every transcript prefix from its factored canonical frames, and checks each of
the nine frozen table entries against the corresponding source derivation.
The table is therefore an authenticated input to the provider comparison, not
a provider-side recomputation.

The separate retrying corpus remains unchanged in behavior: 24 runs accept,
24 reject, and six end in `InterpretationFailed` after exactly two rejected
draws. The checker authenticates that measured count but does not include
those cases in the one-shot correspondence claim.

## 3. Generated transform and source-bound certificate

The untrusted generator emits a Lean module that imports the preceding
generated Schnorr reduction, applies `Reduction.fiatShamir`, and supplies
`fsChallengeOracle` as a nine-entry table lookup. Every listed finite point
returns its frozen challenge; any point outside the table reaches an explicit
refusal.

Both the transformed prover and transformed verifier record the exact round,
statement, message-prefix commitment, and returned answer for every oracle
call. The source challenge occurrence maps to ArkLib's round-one query, while
the prior-message prefix maps to the commitment. This makes extra, absent, or
differently framed queries directly observable rather than inferred from the
final verdict.

The certificate pins by content the three owner pages, three profile
manifests, the source runtime model and runtime paths, both run sets and both
derivation tables, the preceding generated reduction, the term-calculus
inputs, the local template and probe, and the generated module. It pins ArkLib
revision `fad5cbf808774838924dc8273715724c6a6caa1f`, tree
`e38383088598a1305c15447c53db309ccd6b35ee`, dependency revision, relevant
sources, and Lean `v4.31.0`. No research note or sibling finding file is an
input.

## 4. Independent execution

The checker does not import the generator. After authenticating the
certificate and generated source, it:

1. elaborates the Core Check term for all 81 finite environments and compares
   the kernel-executed rows with the independent evaluator;
2. builds the preceding generated reduction into a package-local overlay so
   the transformed module can import it without modifying ArkLib;
3. elaborates the transformed module under the pinned, already-built ArkLib
   checkout and verifies that its declarations contain no `sorryAx`; and
4. executes all 27 honest strategy runs and all 27 verifier-input runs with
   the table-backed oracle.

The transformed module's remaining axiom closure is exactly `propext`,
`Classical.choice`, and `Quot.sound`. This is an environment observation,
not a theorem or authority claim.

## 5. Five correspondence clauses

| Clause | Result | Evidence |
|---|---|---|
| schedule | `Affirmative/F2O4-A-SCHEDULE` | the commitment, challenge query, response, check, and selected terminal map totally, injectively, and in order |
| values | `Affirmative/F2O4-A-VALUES` | the statement, witness, commitment, challenge, response, check, and terminal carriers agree |
| oracle points | `Affirmative/F2O4-A-ORACLE-POINTS` | the prover and verifier query sequences exactly equal the source-derived sequences on every applicable run |
| checks and terminals | `Affirmative/F2O4-A-CHECKS-TERMINALS` | the elaborated term denotation equals the provider check, and the provider verdict equals the source lane image |
| traces | `Affirmative/F2O4-A-TRACES` | provider proof steps and source completed-record occurrences agree under the maps, excluding source-only receipts |

The complete result partition is 22 `Accepted` and 32 `Rejected`. Three
directed controls establish the oracle-point boundary:

- a superfluous query is
  `Negative/F2O4-N-SUPERFLUOUS-ORACLE-QUERY`;
- a missing query is `Negative/F2O4-N-MISSING-ORACLE-QUERY`; and
- a commitment-framed query different from the source prefix is
  `Negative/F2O4-N-DIFFERENTLY-FRAMED-ORACLE-QUERY`.

A point outside the nine-entry domain is
`Refused/F2O4-R-OUTSIDE-FINITE-TABLE`, not evidence about an unmeasured
provider execution.

## 6. Provider declaration

The checker derives the provider declaration from the executed ArkLib model.
The closed carrier is `Option Unit`, with canonical values `some ()` and
`none`. The six source lanes map as follows:

| Source lane | Provider image |
|---|---|
| `Accepted` | `Image(some ())` |
| `Rejected` | `Image(none)` |
| `Aborted` | `Unmodelled` |
| `InterpretationFailed` | `Unmodelled` |
| `StrategyStopped` | `Unmodelled` |
| `OperationalNoncompletion` | `Unmodelled` |

No ArkLib construct in this package produces source sampling exhaustion, so
the retrying construction's six measured exhaustions remain occurrences of
the unmodelled interpretation-failure lane. The contract's carrier rule fits
this execution model exactly; no owner-page delta is proposed.

## 7. Result boundary

This package establishes finite run-for-run operational correspondence for
one exact generated reduction, one exact admitted one-shot protocol, one
nine-point table-backed oracle, and the five listed clauses. It also
establishes the stated `Option Unit` carrier and lane interpretation for the
measured execution model.

It does not establish correspondence outside the table domain, a provider
construct for sampling exhaustion, arbitrary-reduction or arbitrary-protocol
behavior, owner publication, general evaluator or compiler correctness,
theorem applicability or truth, protocol soundness, zero knowledge,
Fiat--Shamir security, random-oracle or quantum-random-oracle security,
concrete-hash suitability, duplex-sponge correspondence, or production
readiness.

## Handoff

Main should commit the complete working tree with subject
`test: interpret the fiat-shamir schnorr protocol in arklib and check the correspondence`.

Files changed:

- the source runtime package updates
  `README.md`, `model.py`, `executor.py`, `run.py`,
  `expected-findings.json`, `expected-runs.json`, and
  `derivation-vectors.json`, and adds
  `expected-runs-one-shot.json` and
  `derivation-vectors-one-shot.json`;
- the source runtime note
  `docs-next/notes/semantic-revalidation-and-redesign/formal-assurance-research/f0v3c-fs-runtime.md`;
- the new
  `evaluation/formal-provider-interpretation-fs-arklib-f2o4/` package:
  `README.md`, `generator.py`, `checker.py`, `run.py`,
  `template.lean`, `TermEvaluatorProbe.lean`,
  `expected-findings.json`, `generated/FiatShamirSchnorrArkLib.lean`,
  and `generated/certificate.json`;
- this research note; and
- `checks/manifest.json`, `evaluation/lifecycle.json`,
  `evaluation/README.md`, and
  `checks/tests/test_evaluation_lifecycle.py`.

The lifecycle-sensitive checks used an alternate index and writable object
store under ignored `target/f2o4-validation/`, with the checkout's real
objects configured as read-only alternates. The real Git index was never
modified. Dependency resolution was offline with a clone-local cache.

| Command | Exit | Wall time | Result |
|---|---:|---:|---|
| `python3 -B evaluation/formal-source-fs-runtime-f0v3c/run.py --write` | 0 | 342.65 s | Refroze the owner-admitted retrying evidence and the independent one-shot runs, views, lane counts, and derivation table. |
| `generator.py --write` followed by `generator.py --check` | 0, 0 | 2.32 s combined | Emitted and then reproduced the table-backed Lean module and source-bound certificate. |
| Direct `checker.py` | 0 | 185.13 s | Cold-authenticated the source and certificate, elaborated the term and provider modules, and compared all five clauses. |
| `python3 -B evaluation/formal-source-fs-runtime-f0v3c/run.py --check` | 0 | 341.11 s | Reproduced 108 runs and 18 derivation vectors with affirmative aggregate. |
| JSON/Python parse checks and `git diff --check` | 0 | 0.20 s | All edited Python sources compile, all checked JSON decodes, and no whitespace error is present. |
| `python3 -B checks/run.py validate` under the alternate index | 0 | 0.04 s | The 80-check, six-tier manifest is valid. |
| Offline `python3 -B checks/run.py run --tier developer` under the alternate index | 0 | 1.80 s | Nine of nine checks passed, including lifecycle inventory. |
| Offline `python3 -B checks/run.py run --check research.provider-interpretation-fs-arklib` under the alternate index | 0 | 170.59 s | The focused correspondence check passed. |

Aggregate outcome:
`Affirmative/F2O4-A-FS-FINITE-CORRESPONDENCE`. All five correspondence
clauses are affirmative on the complete one-shot finite domain. The
superfluous, missing, and differently framed query controls are negative as
required, and an outside-domain point is refused. The provider carrier is
`Option Unit`; only `Accepted` and `Rejected` are modelled. The retrying
construction's six measured `InterpretationFailed` runs are reported as
unmodelled and are not folded into the affirmative claim.

Non-claims: no owner publication, arbitrary-domain or arbitrary-protocol
correspondence, provider support for sampling exhaustion, general evaluator
or compiler correctness, theorem, protocol or cryptographic security,
duplex-sponge result, or production-readiness result.

Surprises and corrections to the brief: this clone omits `AGENTS.md` and
`.claude/CLAUDE.md`, so their read-only primary-checkout copies supplied the
required instructions. ArkLib was built at the requested revision, but the
preceding generated Schnorr module is not an ArkLib module; the checker
therefore builds it into the required package-local overlay before elaborating
the transform. A development prototype initially placed that single overlay
object under `/tmp`; it was deleted, and every final build output is under
the clone-local ignored `target/`. The workflow's private-ledger append is
superseded by the explicit prohibition on writes outside this clone.

The entry contract and carrier packet fit the observed execution model, so no
Proposed delta is needed. No owner page, profile manifest, directory README,
primary checkout, private ledger, or real Git index was modified. No commit,
push, or pull request was attempted.

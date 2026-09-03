# R-A: Structural feature-axis expressibility matrix

> **Kind:** bounded post-freeze research record and executable classifier
> **Authority:** none; this note does not amend a PIR owner page
> **Package:** `evaluation/expressibility-axes/`
> **Check:** `research.expressibility-axes`
> **Aggregate:** `Affirmative/RA-A-AXES-CLOSED-AND-DERIVED`

## 1. Exact question

Does one closed structural-feature vocabulary, with every value routed to one
current constructor or profile, one listed Core reopening condition, or one
explicit boundary, deterministically classify every frozen case without using
protocol-family names as rules?

The answer is affirmative at this package's bounded resolution. The executable
matrix has 20 axes, 125 closed values, 40 destinations, and 63 complete case
rows. Thirty-nine rows derive `fits`, 12 derive `bends`, and 12 derive
`breaks`. No family name participates in the derivation.

## 2. Read boundary and evidence

The structural vocabulary was reconstructed from:

- [`interactive-core.md`](../../../pir/interactive-core.md), especially
  Sections 4--9, 14, and 15;
- [`fiat-shamir.md`](../../../pir/fiat-shamir.md), especially Sections 1--3,
  9, 11, and 12;
- [`interfaces-and-plans.md`](../../../pir/interfaces-and-plans.md), Sections
  4--5;
- [`verifier-derived-query-plans.md`](../../../pir/verifier-derived-query-plans.md),
  Sections 3--9;
- the [portfolio](../r2-protocol-witnesses/expressibility-validation-portfolio.md),
  all five holdout analyses, and the
  [holdout adjudication](../semantic-closure-and-freeze/cold-protocol-holdouts/portfolio-adjudication-and-freeze-decision.md);
  and
- the [post-freeze program](../post-freeze-research-program/README.md).

The 20-row peer-review pressure map is private and is not copied here. The
matrix freezes its exact source path, SHA-256 digest, row coordinates, labels,
projected verdicts, and required obstruction destinations. The public checker
therefore checks the extracted comparison but does not imply publication or
authority for the private note.

For classes absent from the portfolio and peer map, the case rows cite primary
sources directly: [QuickSilver](https://eprint.iacr.org/2021/076.pdf), the
[Wesolowski](https://eprint.iacr.org/2018/623.pdf) and
[Pietrzak](https://eprint.iacr.org/2018/627.pdf) VDFs,
[LegoSNARK](https://eprint.iacr.org/2019/142),
[Kilian](https://doi.org/10.1145/129712.129782),
[Micali](https://people.csail.mit.edu/silvio/Selected%20Scientific%20Papers/Proof%20Systems/Computationally_Sound_Proofs.pdf),
[verifiable computation over encrypted data](https://eprint.iacr.org/2014/202.pdf),
[anonymous credentials](https://www.iacr.org/archive/eurocrypt2001/20450093.pdf),
the [GMR interactive-machine model](https://doi.org/10.1145/22145.22178),
[private-coin interactive proofs](https://www.cs.toronto.edu/tss/files/papers/goldwasser-Sipser.pdf),
[noncommunicating multiprover proofs](https://www.math.ias.edu/~avi/PUBLICATIONS/MYPAPERS/GKBW88/GKBW88.pdf),
[distributed interactive proofs](https://arxiv.org/abs/2006.16191), and
[quantum interactive proofs](https://arxiv.org/abs/cs/9901015).

These citations ground authored feature readings. They do not constitute a
machine-checked correspondence from a paper to the matrix. In particular, the
GMR row is a model-level pressure case for a prover-chosen continuation count;
it does not claim that GMR's named zero-knowledge protocol has that feature.

## 3. Closed structural vocabulary

[`axes.json`](../../../../evaluation/expressibility-axes/axes.json) is the
machine-readable authority for this package. It closes the following axes and
routes every individual value to exactly one destination:

| Axis | Structural question | Destination owner |
|---|---|---|
| `party_structure` | how many logical parties and which roles exist? | Core Sections 4.1/14 or the multiparty, multiverifier, and multi-role boundaries |
| `oracle_publishers` | who publishes each Oracle? | Core Section 7, PublicEnvironment, the Oracle-lifecycle reopening, or multiparty boundary |
| `verifier_input_privacy` | are verifier inputs public, private, relation-critical private, or partitioned? | Core Sections 4.1--4.2, the private-grounding reopening, or multiverifier boundary |
| `query_privacy` | are queries absent, public, verifier-private, mixed, or partitioned? | Core Section 7 or the multiverifier boundary |
| `verifier_randomness_privacy` | is verifier randomness absent, public-reconstructible, private, mixed, or partitioned? | Core Challenge/visibility and Plan, or the multiverifier boundary |
| `challenge_source` | none, verifier-fresh, transcript, duplex, imported, prover-selected, or source-omitted? | Fresh/FS constructors or an exact boundary |
| `challenge_interpretation` | none, public/private coin, shared, rejection sampled, grinding, imported, or omitted? | Challenge/FS constructors or an exact boundary |
| `round_structure` | fixed, finitely elaborated, symbolic instance-indexed, data-dependent, chosen, or unbounded? | finite composition, symbolic-recurrence reopening, or schedule/loop boundary |
| `statement_timing` | when is the statement fixed relative to the first challenge? | Core Section 4.4 or the late-statement reopening |
| `oracle_kinds` | table, polynomial, codeword, logical, algorithmic, encrypted, or quantum? | Core Oracle/query-plan, Oracle-lifecycle reopening, or quantum boundary |
| `oracle_access_modes` | full, binding, logical, derived, adaptive-plan, mutable, or quantum? | Core Oracle/query-plan, Oracle-lifecycle reopening, or explicit boundary |
| `commitment_relation` | absent, logical-only, checked compilation, statement-native, or opaque external? | Core/FS commitment constructors or module-semantics reopening |
| `setup_kind` | none, transparent, CRS, verifier-secret, checked preprocessing, multiparty, or encrypted-data preprocessing? | PublicEnvironment/Plan/visibility, Oracle-lifecycle reopening, or multiparty boundary |
| `setup_trust` | transparent, trusted/updatable CRS, designated-verifier, multiparty, or source-undetermined? | explicit parameter/visibility constructor or exact boundary |
| `composition_modes` | sequential, interleaved, shared, folding, finite recursion, imported verifier, cross-execution, or concurrent? | finite Core/Plan/imported-verifier constructors or explicit boundary |
| `termination_modes` | first-active, abort, interpretation failure, continuation, omitted, or nonterminating? | Core/Plan terminal constructors or exact boundary |
| `randomness_sources` | none, environment, local tapes, transcript, duplex, setup, or quantum measurement? | Challenge/Plan/FS constructors or quantum boundary |
| `statement_adaptivity` | nonadaptive, pre-challenge, post-challenge, cross-execution, or partitioned? | statement scope, reopening, or explicit boundary |
| `query_adaptivity` | none, nonadaptive, finite transcript/answer adaptive, plan-adaptive, or cross-execution? | Core Oracle or explicit boundary |
| `communication_kind` | typed classical, no messages, encrypted classical, or quantum? | Core Message/Check or quantum boundary |

The distinction between `finite_elaborated_instance` and
`symbolic_instance_indexed` is material. An explicit Sumcheck, GKR,
Bulletproofs, WHIR, Circle, or LatticeFold+ instance can fit after complete
finite elaboration while the unbounded family description still bends at the
symbolic-recurrence reopening condition. Likewise,
`algorithmic_carrier_with_closed_plan` reaches the checked query-plan profile,
while `algorithmic_carrier_without_closed_plan` reaches the Oracle-lifecycle
reopening condition. Protocol names do not select either value.

## 4. Derivation rule

For one complete feature vector, the checker resolves all 20 cells to their
destinations and applies this fixed precedence:

```text
any explicit_boundary     -> breaks(all selected boundary ids)
else any reopening_condition -> bends(all selected reopening ids)
else                       -> fits
```

The checker recomputes the verdict and exact obstruction set. It does not trust
the frozen `predicted_verdict` or `predicted_destinations` fields. A stored
prediction mismatch changes the aggregate to
`CannotAnswer/RA-C-RECORDED-VERDICT-DISAGREEMENT` under `--check` because the
frozen expected projection no longer agrees.

Historical `Undetermined` is preserved as an evidence failure. The H03 broad
application reaches cross-execution and imported-challenge boundaries; the H05
complete noninteractive construction reaches the exact source-incomplete
boundary. Neither becomes an affirmative or a semantic rejection of the
underlying protocol.

## 5. Frozen cases and recorded agreement

[`cases.json`](../../../../evaluation/expressibility-axes/cases.json)
contains 63 complete vectors, or 1,260 checked matrix cells.

| Coverage | Rows | `fits` | `bends` | `breaks` | Checked historical comparison |
|---|---:|---:|---:|---:|---|
| portfolio identifiers | 25 | 19 | 4 | 2 | complete `P01`--`P10`, `V01`--`V05`, `H01`--`H05` census; clusters split by shape |
| holdout adjudication | 8 | 5 | 0 | 3 | all eight distinct H01--H05 decisions/projections agree |
| peer-review pressure map | 22 | 13 | 6 | 3 | all 20 rows covered; two mixed rows split; all 22 projections agree |
| previously unconsidered classes | 13 | 5 | 2 | 6 | every row has a primary-source coordinate; no prior verdict is imputed |

The peer-review row splits are necessary structural distinctions, not extra
votes: shared challenge versus imported challenge in row 13, and one logical
distributed Prover versus independent noncommunicating provers in row 18.

The additional source classes fall predictably as follows:

| Source-shaped case | Derived place | Exact reason |
|---|---|---|
| QuickSilver designated-verifier VOLE proof | `bends` | checked correlated preprocessing reaches `RC-ORACLE-LIFECYCLE`; verifier-private inputs and coins themselves fit |
| Wesolowski VDF proof | `fits` | fixed classical no-oracle proof with a transcript-derived interpreted challenge |
| Pietrzak VDF family | `bends` | symbolic instance-indexed recursion reaches `RC-SYMBOLIC-RECURRENCE` |
| LegoSNARK commit-and-prove | `fits` | commitment is statement material under a finite CRS-backed proof |
| finite Kilian argument | `fits` | finite logical PCP Oracle plus checked commitment and closed query plan |
| finite Micali CS proof | `fits` | the same finite carrier under canonical transcript derivation |
| amortized FHE verifiable computation | `breaks` | required adaptive state spans executions; encrypted lifecycle reopenings are subordinate to `B-CROSS-EXECUTION` |
| anonymous credential lifecycle | `breaks` | issuer/holder/verifier roles, cross-execution state, concurrency, and scheduler choice hit four explicit boundaries |
| prover-chosen continuation count | `breaks` | runtime topology reaches `B-DYNAMIC-SCHEDULE` |
| private-coin interactive proof | `fits` | verifier-private input, local randomness, and Fresh challenge are existing constructors |
| noncommunicating multiprover proof | `breaks` | physical independent provers reach `B-MULTIPARTY` |
| distributed verifier knowledge | `breaks` | partitioned inputs, queries, and randomness reach `B-MULTIVERIFIER` |
| quantum interactive proof | `breaks` | quantum states, access, measurement, and messages all reach `B-QUANTUM-CARRIER` |

## 6. Axes whose destination is a boundary today

These are the boundary-valued cells in the closed vocabulary. A new protocol
selecting one of them derives `breaks` even if every other feature fits.

| Axis | Boundary-valued choices |
|---|---|
| party structure | independent noncommunicating provers; multiple verifiers with distributed knowledge; more than two lifecycle roles |
| Oracle publisher | multiple independent provers |
| verifier input/query/randomness privacy | any of those partitions across multiple verifiers |
| challenge source | imported from another execution; prover-selected; source omits the transform |
| challenge interpretation | imported semantics; source omits the interpretation |
| rounds | data-dependent; prover-chosen; verifier/scheduler-chosen; unbounded |
| Oracle kind/access | quantum state/access; answer-adaptive plan topology |
| setup kind/trust | correlated multiparty preprocessing; multiparty trust; source-undetermined setup |
| composition | cross-execution; concurrent sessions |
| termination | source omits terminal semantics; nonterminating |
| randomness | quantum measurement |
| statement adaptivity | cross-execution; partitioned across verifiers |
| query adaptivity | answer-adaptive plan; cross-execution |
| communication | quantum messages |

The 12 exact boundary destinations are:

```text
B-ANSWER-ADAPTIVE-PLAN
B-CONCURRENT-SESSIONS
B-CROSS-EXECUTION
B-DYNAMIC-SCHEDULE
B-IMPORTED-CHALLENGE
B-MULTIPARTY
B-MULTIROLE-LIFECYCLE
B-MULTIVERIFIER
B-PROVER-CHALLENGE
B-QUANTUM-CARRIER
B-SOURCE-INCOMPLETE
B-UNBOUNDED-LOOP
```

The five `bends` destinations are existing Section 15 reopening conditions,
not boundaries: late statement, symbolic recurrence, Oracle/preprocessing
lifecycle, verifier-private relation grounding, and an acceptance-relevant
module effect whose exact semantics cannot yet be stated.

## 7. Findings

The frozen 18-finding projection records:

- `Affirmative/RA-A-AXIS-SCHEMA-CLOSED` for the 20 axes and 125 values;
- `Affirmative/RA-A-DESTINATIONS-TOTAL` for the 40 one-to-one value
  destinations;
- `Affirmative/RA-A-CASE-MATRIX-TOTAL` for all 1,260 case cells;
- `Affirmative/RA-A-HOLDOUT-ADJUDICATION` for eight recorded decisions;
- `Affirmative/RA-A-PEER-REVIEW-MAP` for 22 split recorded projections;
- `Affirmative/RA-A-MUTATIONS-REFUSED` for six fail-closed controls; and
- aggregate `Affirmative/RA-A-AXES-CLOSED-AND-DERIVED` with zero recorded
  disagreements.

Three obligations remain explicit `CannotAnswer`: universal completeness of
the vocabulary, machine-checked source-to-vector correspondence, and every
cryptographic or implementation property.

## 8. Pass meaning and non-claims

A pass establishes only totality and deterministic derivation for the pinned
20-axis vocabulary and 63 authored vectors, plus exact agreement with the
frozen holdout and peer-review projections. It establishes no universal
taxonomy. A protocol can expose a genuinely new feature and require a new
value, destination, or axis; until reviewed, that is missing evidence, not an
invented `fits`, `bends`, or `breaks` result.

The package does not establish source-protocol correspondence, Core admission,
profile implementation, compiler support, relation satisfaction, theorem
truth or applicability, setup validity, soundness, knowledge, zero knowledge,
Fiat--Shamir security, recursion correctness, quantum semantics, or deployment
readiness. It edits no owner page and proposes no owner-page delta.

## Handoff

- **Branch:** `lane/ra-expressibility-axes`
- **Commit hash:** not created. `git add -A` could not create `.git/index.lock`
  because this clone's Git metadata is mounted read-only. The checks below used
  a temporary index/object overlay containing the exact staged worktree; that
  validates the content but does not update the real branch ref.
- **What was run:** `python3 -B checks/run.py validate` exited 0 in 0.04s;
  `python3 -B checks/run.py run --tier developer` exited 0 in 0.84s; and
  `python3 -B checks/run.py run --check research.expressibility-axes` exited 0
  in 0.17s. The successful developer run used `UV_NO_SYNC=1` with the existing
  read-only primary-checkout environment because dependency installation is
  network-blocked in this sandbox.
- **Aggregate:** `Affirmative/RA-A-AXES-CLOSED-AND-DERIVED`; 63 rows, 1,260
  cells, zero frozen-prediction, holdout-adjudication, or peer-map
  disagreements.
- **Non-claims:** no universal taxonomy, paper correspondence, owner
  publication, protocol support, implementation correspondence, theorem,
  cryptographic property, or deployment claim.
- **Surprises:** a closed finite query plan makes concrete WHIR/Circle shapes
  fit while the older unspecified FRI/STIR/WHIR family row still bends; virtual
  distributed proving remains two-role while physical noncommunicating
  multiprover interaction breaks. The first developer run failed in 0.47s
  because `/home/wonjae/.cache/uv` was read-only; a retry with an empty writable
  cache failed in 7.99s because DNS access to PyPI is blocked. Neither reached
  a semantic test failure.
- **Where this brief was wrong:** `AGENTS.md` and `.claude/CLAUDE.md` were absent
  from this dedicated clone and were read from the read-only primary checkout;
  the workflow's private-ledger append conflicts with the explicit prohibition
  on writing outside this clone and was not performed; and the instruction to
  stage and commit in this clone is impossible while `.git` is mounted
  read-only. Even with writable Git metadata, an exact commit hash cannot be
  embedded in the same commit that contains this handoff.

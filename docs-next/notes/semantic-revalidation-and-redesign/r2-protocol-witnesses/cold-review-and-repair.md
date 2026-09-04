# FRI-Grind-1 Cold Review and Repair Decision

> **Kind:** Temporary R2 falsification and repair record
> **State:** Repaired `FRI-Grind-1` closed; the first executable attempt remains
> retained as a failed witness and broader R2 remains active
> **Authority:** None. This record classifies finite witness evidence; it does
> not select the target architecture, establish protocol security, or activate
> Stage 4B.
> **Review boundary:** Public repository artifacts and public research only.
> Nothing under `docs/private/` was used by the cold reviewers.
> **Disposition:** Retain through broader R2 and later absorption, then delete
> this temporary package after its accepted conclusions have durable owners.

## 1. Frozen attempt and verdict

The first lean `FRI-Grind-1` attempt was frozen before review. Four independent
roles checked semantic closure, identity/report closure, source/research
fidelity, and malformed-input behavior. All four reproduced the same generated
report and the complete local test suite before attempting falsification.

| Artifact | Frozen SHA-256 |
|---|---|
| `frigrind.py` | `ddb6415cc1a0764d16678defbea35a4b947c80bd7f6252a72f1fc67abadeea74` |
| `execution.py` | `9e5c6ffde7ba6204eed19e20d9ac52041f13150007f8fa5998c951ea3693f480` |
| `relations.py` | `c7b34d9c53283c79f8e5c79c02cc18596ffe8cce985b48d4ce7da3e87d10241a` |
| `terms.py` | `122b91abd015316ceaee9937f3d17d06ff5f83cae105d37035f5765c4e638892` |
| `report.py` | `b233b0980f3608e427e66a0ba58001d92841b9b453c254e97a9babb7d123e5c1` |
| generated report | `f29575dbb41f259ea99d4191c7ebbe4502dba4cbfb22af16cfba9b3dbdfa220c` |

The attempt is reproducible but failed the R2 semantic-closure gate. This is a
failed witness, not a discarded result. It demonstrated that green replay and
compact sealed output are insufficient when the identities and qualification
boundaries do not denote the claimed semantic subjects.

## 2. Confirmed architectural defect cluster

The reviews converged on one authority-duplication defect with several visible
consequences:

1. `ProtocolCoreId` did not close over the ordered interaction. Statement,
   messages, checks, failure effects, routes, and residual behavior were partly
   authored in separate executor and relation tables.
2. Fiat--Shamir initialization included scenario and invocation packaging.
   Changing only a nonce-search bound changed transcript challenges, so
   evaluation metadata became a transcript-selection input.
3. the Statement and `g1` codecs were eight bytes although the declared field
   admitted larger values; admission therefore did not establish total
   framing over the absorbed domain;
4. freely constructible records could pass Relations after challenge values,
   checks, routes, receipts, costs, or invocation identifiers were forged;
5. candidate maps were checked only against caller-supplied action schemas, so
   both sides and the map could be shortened together;
6. the affirmative Statement bridge derived both operands from one invocation
   value and therefore did not witness a correspondence;
7. all reported Fresh executions used FS-derived coins. That was valid coupled
   comparison evidence but supplied no non-FS-derived Fresh execution source;
8. result entries sealed only outcome, boundary, and code. They did not bind a
   typed subject or decisive evidence;
9. evaluator implementation bytes, execution-affecting inputs, and records had
   no single identified request/qualification chain; and
10. failed-check transition validation admitted truncated or otherwise
    non-exact terminal suffixes.

Additional confirmed corrections are to close residual and predicate
vocabularies, pre-admit aggregate work before loops, remove a semantic
`force_pow_failure` hook, avoid manufactured generator-evidence events, remove
post-parse tautological judgments, and stop calling the local grinding-event
mass an honest protocol-success probability.

## 3. Evidence that survived

The repair retains rather than reimplements the following results:

- exact fixture, generated-vocabulary, and generated-spine reconstruction;
- the primary-source FRI, IOP/BCS, adaptive Fiat--Shamir, RBR, and grinding
  analysis, with its existing theorem and non-transfer boundaries;
- bounded canonical term encoding and strict duplicate-key rejection;
- structural rejection of latent FS machinery in Fresh scenarios;
- the concrete strong-prefix mutations for omitted, delayed, duplicated,
  wire-only, private-coin, future-read, namespace, routing, and post-grinding
  influence defects;
- the explicit distinction among shared, mapped-distinct, and hybrid
  organization, without assuming strategy or distributional equivalence;
- honest termination at `FriTerminalNotModeled`; and
- the exact current eight-by-twenty-seven-bit anchor projection, source-byte
  authority refusal, and unpriced-loss non-claim.

The cited protocol-ordering and theorem-premise reconstruction survived. It
does not validate executable distribution, strategy, probability, or
theorem-applicability claims; those remain separate obligations. The failure is
in the executable evidence boundary, not the Stage 1--3 factorization
hypothesis.

## 4. Repair architecture

The repaired witness will use seven explicit artifacts.

### 4.1 Identity regime and term ABI

All artifact identities use one explicit witness-local `SemanticRegimeId`. Its
closed finite-term ABI has tagged, length-delimited null, booleans, integers,
UTF-8 text, bytes, canonical sequences, and sorted string-keyed maps under
explicit byte, node, and depth bounds. Identities bind the regime, an ASCII
domain, and the encoded preimage; unsupported regimes are rejected. This is not
a universal v0 ABI.

### 4.2 Complete Protocol Core

`ProtocolCore` owns one closed ordered action term. Every action has a closed
occurrence, kind, actor, domain, multiplicity, and semantic contract.
Challenges own namespace, public-coin source, and required prior influences;
checks own predicates and exact failure effects; routes own closed formulas;
the only successful suffix is the closed residual `FriTerminalNotModeled`.

Execution schedules, challenge slots, candidate action schemas, route order,
and terminal laws are derived from this term. No ambient parallel schedule is
permitted.

### 4.3 Interpretation-local construction

`ScenarioVariant` contains the Core, interpretation, fixed witness-local
`StrategyContract`s, and exactly one realization construction. Admission checks
declared prior reads and prospective previews against Core order; it does not
define an adversary class. Durable semantics must expose execution as a relation
parameterized by protocol, strategy, inputs, and verifier coins, with Analysis
quantifying over an admitted causal strategy class.

Fresh owns Core-derived coin slots and names sequential-reveal,
conditional-uniform finite-slot, and no-future-access laws. Concrete execution
consumes an identified tape; it neither samples from nor proves the declared
distribution. FS owns a transcript construction containing only semantic
initialization, framing, absorption, and sampling rules.

FS initialization is a function of `CoreId`, `TranscriptConstructionId`, and
an explicit `ApplicationContextId`. The application context is intentional
semantic domain/session input, so changing it is expected to rotate challenges;
Statement remains a separately absorbed Core action. File, request, evaluator,
source, search, and resource identities do not initialize the transcript.

### 4.4 Execution request and evaluator basis

`InputBundleId` names the Statement and base prover inputs.
`ExecutionRequestId` additionally closes over the scenario, application
context, evaluator basis, FS search plan or Fresh fixed-nonce plan, Fresh coin
tape where applicable, aggregate resource plan, `CoreDerivationKind`, source
fixture, and source package. Admission reconstructs the package, requires exact
package `InputBundle` equality, and requires either the exact fixture grinding
Core or its exact drop-grinding projection. A request-local search interval may
deliberately override the package default; this is source grounding, not replay
of every invocation default.

`EvaluatorBasisId` binds the recognized construction IDs, qualification-law
version, exact evaluator source digests, request-execution hard caps, and
separate qualification caps. The latter bound dependency count and aggregate
target-plus-dependency replay; the local profile permits one direct dependency
and rejects nested dependencies. This is validation evidence against
implementation drift. It does not redefine semantic `AlgorithmId` or claim
that source hashes prove semantic equivalence.

### 4.5 Qualified execution

`ExecutionRecordId` binds the request, evaluator basis, events, receipts,
disposition, and exact resource usage. `qualify_execution` re-executes the
identified request under the identified evaluator and requires exact record
equality. Relations consume only a qualified execution and recheck its
qualification boundary.

Qualification pre-admits aggregate worst-case target-plus-dependency replay,
requalifies each dependency, exactly reexecutes the target, and binds aggregate
actual `QualificationUsage`.

Resource admission bounds total challenge draws, retry attempts, nonce
candidates, transcript events, trace events, and worst-case hash queries
before evaluation. Exhausting bounded FS nonce search is a prover `Abort`, not
verifier `Reject` or `ResourceExceeded`; a fixed Fresh nonce followed by nonzero
pow is verifier `Reject`. Immediate rejection is a witness-local,
acceptance-equivalent short circuit for the modeled check/route predicate, not
paper-level FRI/BCS trace equivalence. A source-residual execution ends at
exactly its declared residual.

### 4.6 Relation shape and validation profile

`RelationShapeId` owns subject organization, Core-derived action schemas, and
the exact disposition map. It excludes provenance, evaluator details,
evidence sources, and presentation labels. `ValidationProfileId` separately
owns evaluator and qualification-law bindings plus observation, origin,
terminal, and strategy comparison policy. A report-level replay basis binds
the `relations.py`, `report.py`, and `run.py` implementations used to assemble
and verify the public evidence graph; it is not part of reusable relation
policy.

Only separate judgments remain: exact typed map, mapped-value commutation,
full-observation comparison, origin-sensitive comparison, and strategy
relation. Redundant profile/provenance checks are removed rather than given
new names.

### 4.7 Grounded bridge and case binding

A positive pointwise Statement bridge requires two independently identified
operands: a relation-side public value and a Statement occurrence extracted
from a qualified protocol execution, plus an explicit typed map. The current
fixture supplies no independent relation-side operand, so the repaired report
must return `MissingDependency` until one exists. It must not manufacture a
second value from the invocation.

Every report case binds `outcome`, `boundary`, `code`, `subject_id`, and
`evidence_id`. Compact evidence preimages contain the exact request,
qualification, record, relation/profile, projection, or bridge operand IDs.
The expected-results oracle freezes all five fields.

## 5. Fresh evidence split

The repaired report distinguishes four requests:

1. the FS source-residual execution;
2. an external, non-FS-derived Fresh grinding support-point execution using an
   exact frozen tape and no FS execution dependency;
3. an FS-coupled Fresh grinding execution used only for shared-subject
   comparison; and
4. an FS-coupled Fresh no-grinding execution used for the distinct/hybrid
   comparison.

This closes exact external-source execution at one point only. It does not
establish uniform sampling, stochastic independence, nonce-before-tape
authoring, or general Fresh non-anticipation. Coupled evidence remains useful
but separately identified.

## 6. Adjudicated recommendations

- **Accepted:** complete Core ownership, transcript-construction separation,
  full-domain codecs, execution-request identity, exact replay qualification,
  external non-FS-derived Fresh support-point execution, explicit local semantic
  regime and term ABI, source-package/Core-derivation grounding, qualification
  replay accounting, prover-`Abort`/verifier-`Reject` separation,
  relation/validation identity separation, grounded bridge operands, result
  subject/evidence binding, and aggregate resource admission.
- **Accepted with a boundary correction:** evaluator source digests belong to
  the validation basis and request/record/report chain, not automatically to a
  semantic protocol or algorithm identity.
- **Withdrawn:** the affirmative current Statement bridge, the label
  `source-faithful`, the protocol-success probability field, manufactured
  generator provenance, and the arbitrary report-size quota. No replacement
  event-probability field is admitted by this finite witness.
- **Deferred as non-blocking:** a CLI for verifying arbitrary serialized
  reports. Canonical replay is the current consumer boundary; a strict loader
  may be added if an external report becomes an admitted input.
- **Rejected as a gate metric:** raw diagnostic-branch coverage. High-value
  boundary paths are required, but unused diagnostic count does not establish
  semantic incompleteness by itself.

## 7. Work order and gate

The dependency order was Core/construction/types, execution requests and
qualification, Relations and bridge, report and frozen cases,
malformed/boundary tests, then documentation. Closure required the repaired
artifact to rerun the cold-review counterexamples and undergo a new
non-authoring replay against new hashes.

Passing that replay closes only the corrected `FRI-Grind-1` attempt. R2 still
requires materially different protocol witnesses before R3 model research and
R4 selection. R3 and Stage 4B remain inactive.

## 8. Repaired refreeze and non-authoring replay

The repaired snapshot was frozen after correcting the report-root binding
defect found by the final independent audit. A runner may name only the
resolved checkout whose evaluator modules are loaded; a different checkout
must execute its own runner.

| Artifact | Repaired SHA-256 |
|---|---|
| `terms.py` | `1eb41cbcf8f2d080cc6c1e35730057f25a733dce5bb096f5a7f419534b064bd7` |
| `frigrind.py` | `f2433c2b5f9708fffa4e9aab8c8200defdcc341bafbbff51665659b80ae1cf0d` |
| `execution.py` | `993d1f996d2ed8663d96d0f9417f6de2ffc8708907d50ed2ffcd1716d7332c36` |
| `relations.py` | `90acccf4cd32e0894b130775e0a7aa98ecdd0158e840f65812ad8969ee881d7a` |
| `report.py` | `1538c7ae0c507c388547ef1af214f3afddc88d04535386cce764451fb2e57be9` |
| `run.py` | `c6eff7739b65c917d6f91511902a56e30679fde958dcd8ec4e9cc3c2321b1632` |
| `expected-results.json` | `06e09d7bb220f15c220d7c626eb4b065a2321041a168c1f1dd60ef3d28093507` |
| `test_execution_v3.py` | `b2d45718c73242dec1578897171e5531aaebdce1fab1ba3795d895cd66b1e54d` |
| `test_relations_v3.py` | `11b1d7f2e2bc9c0dc2483a246c9a2aae9b3eae25cf829d1dd09661fc8e37a62c` |
| `test_report_v3.py` | `149eedb944e14eb976cc2922b85c494b41e0a74fb0dd975e1fb511b1f4b25f39` |
| `test_sources_v3.py` | `a3b53fa4fc81d0cc5bec4a80fa8b05465e7eb3fdcf96cc8ac4cbce8e4df88ec1` |
| canonical generated report | `3612802ef7e9b43291e6ee5534387d44dcc03a5ed9369e89f3250d740fd916ee` |

The report identity is
`sha256:f812aa1e374994eee5ef2279b28819c66050aa2ff0df750d1749f3b498f9d29d`;
its report replay basis is
`sha256:ede48737711f6fedd0486a7da39cfdbbe3400e1cdc5eff13de1065efe8e48912`.
The v3 report contains 41 cases and 41 one-to-one evidence objects. Every case
has exactly outcome, boundary, code, subject, and evidence identities.

In the live checkout, the expected-results replay passed and all 39 execution,
Relations, report, and source-fidelity tests passed in 104.063 seconds. A
minimal temporary checkout containing only this evaluator package and the two
frozen source fixtures loaded its own modules, reproduced the byte-identical
report, and passed the same 39 tests in 108.179 seconds. Supplying `/tmp` as an
alternate root was rejected before source reads or replay.

The repaired result establishes the following finite facts only:

- four separately identified FS, external-Fresh, and coupled-Fresh execution
  forms qualify at the source residual;
- the external Fresh support point has no FS execution dependency and is not
  used as relation-run evidence;
- the Statement bridge remains `MissingDependency`, while substituted
  Statement influence and Fresh distribution evidence remain `NotExercised`;
- execution and qualification resource exhaustion remain distinct from prover
  `Abort`, verifier `Reject`, malformed input, and checker failure; and
- Core-derived relation shape, reusable validation policy, exact run evidence,
  and hybrid factorization have separate identities and replay boundaries.

`CheckerFailure` is declared but intentionally absent from an accepted report;
malformed-input and resealed-report tests instead verify that failures are
returned or rejected without being mistaken for semantic results. Durable
strategy-parameterized execution, a qualified relation-side Statement operand,
native oracle/IOR semantics, distributional laws, theorem applicability,
general Relations grounding, and property transport remain open. The passing
replay therefore closes the repaired `FRI-Grind-1` attempt, not R2, R3, Stage
4B, or the final architecture.

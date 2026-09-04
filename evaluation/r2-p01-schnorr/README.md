# P01 Schnorr/Sigma Phase B Evaluator

This package is the finite executable witness for the P01 Phase B repair. It
implements one challenge-neutral Schnorr Core with distinct Fresh and
Fiat--Shamir Protocols, staged owner-local generation and relation satisfaction,
and portable public execution, proof verification, Relations grounding, finite
Analysis, and source-bound report replay.

It is a temporary R2 research instrument, not a compiler component, production
protocol, cryptographic security evaluator, or durable semantic authority. The
[P01 source page](../../docs-next/notes/semantic-revalidation-and-redesign/r2-protocol-witnesses/p01-schnorr-sigma.md)
owns source reconstruction and the current-target obstruction. The
[Phase B decision](../../docs-next/notes/semantic-revalidation-and-redesign/r2-protocol-witnesses/p01-phase-b-repair-and-refreeze.md)
owns the selected model, gate disposition, and reopening conditions.

## Run

From the repository root:

```sh
python3 -m unittest discover -s evaluation/r2-p01-schnorr/tests -v
python3 evaluation/r2-p01-schnorr/run.py --check
```

The repaired suite passes 69/69: 8 semantic, 27 execution/Interface, 8
provenance/diagnostics, 13 Relations/Analysis, and 13 report/replay tests. The
execution group includes staged causality, exact equal-content occurrence
separation, single-use finalization, state-sensitive challenge resolution, and
read-only local audit reconstruction. The report/replay group exercises strict
reconstruction, expected-oracle separation, source and fixture perturbations,
mixed-root refusal, and minimal copied-checkout replay.

The runner writes the canonical public report to standard output. An explicit
output can be selected with:

```sh
python3 evaluation/r2-p01-schnorr/run.py \
  --check \
  --output /tmp/p01-public-report.json
```

`--check` is retained for command symmetry; report construction, strict
verification, and the final expected-projection comparison always run.

## Package boundaries

| Path | Role |
|---|---|
| [`cases/public-inputs.json`](cases/public-inputs.json) | Exact v3 public algebra, `Application` context authority, Statement, Fresh support point, FS proof, non-claims, and public resource plan. |
| [`cases/source-ledger.json`](cases/source-ledger.json) | Public research citations and selected revisions; the report binds the ledger fixture bytes, not the external documents' content. |
| [`cases/expected-results.json`](cases/expected-results.json) | Separately frozen public projection compared only after oracle-independent report construction and verification. |
| `cases/private-generation.json` | Exact v3 owner-local witness, nonce, precommitment-audit policy, and local resource plan, decoded and consumed by generation tests only; excluded from the public report and replay packet. |
| [`p01model/`](p01model/) | Finite semantics, execution, Interface, Relations, Analysis, provenance, diagnostics, independent reconstruction, and report logic. |
| [`tests/`](tests/) | Semantic, execution/Interface, provenance/diagnostics, Relations/Analysis, and report/replay checks. |
| [`run.py`](run.py) | Source-bound public report builder, verifier, and post-build projection comparator. |

The former combined v1 fixture `cases/schnorr-p01.json` and monolithic legacy
test `tests/test_p01.py` were deleted. Public replay inputs, source provenance,
private generation, and the expected oracle now have distinct owners.

The public decoder rejects altered disclosure, application authority, Fresh
coin-source classification, resource-plan shape or budget, non-claim boundary,
and extra or missing fields. `FrozenPublicSupportPointNotSamplingEvidence`
means exactly what it says: the Fresh vector is public replay data, not evidence
of uniform sampling. Finite Analysis scope is derived from executed exhaustive
results; it is not accepted as an input-authored fixture claim.

## Exact finite support point

The profile is `p=23`, `q=11`, `g=2`, with challenge set
`C={0,...,7}`. The public Statement is `Y=13`; the owner-local positive
assignment uses `x=7,r=4` and commitment `A=16`.

| Result | Exact value |
|---|---|
| Fresh challenge and response | `c=3,z=3` |
| Fiat--Shamir challenge and response | `c=6,z=2` |
| Public FS proof bytes | `1002` |
| FS query length | 448 bytes |
| FS query SHA-256 | `ccb57bf733f23917e32f91edfefc8ff82332bb30e36118f411f21caf874e4218` |
| First squeezed byte | 110, reduced modulo 8 to `c=6` |
| Accepting finite transcripts | 968 |
| Unordered distinct-challenge forks | 3,388 |
| Conditional real/simulator distribution equalities | 88 |
| Samples per side across those distributions | 968 |

The FS query, session derivation, framing, and challenge are reconstructed by a
separately coded path in `independent.py` without calling the semantic framing,
duplex, or sampling helpers. The path still consumes the admitted construction
shape and finite parameters, so its validation basis binds the executed package
initializer plus `terms.py`, `semantic.py`, and `independent.py`. Agreement is
implementation-diversity, byte-level falsification evidence, not independent
semantic authority, CFRG conformance, or a Fiat--Shamir security theorem.

## Public report

The public report schema is `zkc.r2.p01.public-report.v3`. The current report
identity is:

```text
evidence-sha256:a74b746e60a3fd344f00d8673011ce53749291d51fef2e4d126a7109bc091006
```

The separately frozen expected projection has SHA-256
`0589d7aef533111dded0bc57bc8bb145a9e6abc98812903e33b278866ea29ae2`.

It publishes 45 exact executed cases:

- 22 affirmative cases;
- 23 nonaffirmative cases covering strong-FS and public-coin mutations,
  malformed or rejecting proofs, public resource ceilings, Statement-
  grounding mismatch, equal-challenge rejection, and theorem refusals;
- Fresh and FS public records, qualifications, and Interface checks;
- Relations-issued Statement grounding; and
- actual-transcript and exhaustive finite Analysis results.

`build_report(repo_root)` accepts no expected-results argument and never reads
or hashes the private generation sidecar. It first binds exact public fixture
bytes and normalized content, then binds explicit component-specific manifests
for the declared source closure of each result. `verify_report` checks typed
identities, case evidence, report evidence, manifest closure, and an exact
oracle-independent rebuild. It rejects an `overall_pass` field. Only after
construction and strict verification does the runner load and compare the
separately frozen expected projection.

The prior 62-test report identity failed cold review and is retired. This
rotated report binds the repaired execution source and the complete separately
coded reconstruction basis before comparison with the refrozen projection.

The report keeps these lanes distinct:

| Lane | Meaning |
|---|---|
| Semantic identity | Stable finite profile, Core, Protocol, construction, Interface, and relation meaning. |
| `ArtifactContentId` | Exact public bytes or canonical public content. |
| `ValidationBasisId` | Exact checker laws, component source closure, and resource bounds. |
| `EvidenceRecordId` | One bounded observed result under named operands and validation basis. |
| Owner-local reference | Exact nonportable witness, invocation, and precommitment occurrence authority; never a public artifact identity. |

The copied-checkout test uses only the public fixtures, expected projection,
runner, and complete `p01model` source closure, including the executed package
initializer. It launches that copied runner
from an isolated working directory with an empty `PYTHONPATH`; alternate and
mixed loaded roots are rejected. The private sidecar and tests themselves are
not part of the portable replay packet.

## Diagnostic classification versus execution

The source closure declares 203 diagnostics and classifies each exactly once:

| Class | Count |
|---|---:|
| Affirmative | 30 |
| Constructible driver | 144 |
| Internal invariant or fault | 15 |
| Environmental | 1 |
| Retired, dead, or redundant | 13 |

This is classification closure only. It is published separately from the 45
executed report cases and their 39 distinct codes, and does **not** claim that
all 144 constructible codes
have a driver, are reachable, or fail at their intended first boundary. Full
diagnostic reachability remains a nonblocking hygiene queue rather than the T3
denominator. The current instrumented suite fires 68 of the 203 declared codes
and leaves 135 unreached; that live snapshot does not strengthen the matrix or
classification claims.

## Current disposition

The prior 62-test snapshot failed cold review on modeled causality, equal-
content occurrence aliasing, and incomplete independent-basis closure. At the
current finite scope, the repaired Phase B gates 1--9 are closed: the source and
toy boundary, one v3 construction, shared-Core factorization, staged execution
and Interface, finite Analysis, the 13-obligation semantic falsification matrix,
Relations, exact local occurrence and typed public identity/source binding, and
copied public replay are implemented and reproduced. Closing Gate 6 does not
claim 144/144 diagnostic drivers. Separate read-only lifecycle and provenance
cold reviews reran the original counterexamples, found and drove repairs for an
invalid-Fresh state transition and an omitted package-initializer source, and
then passed the final snapshot. Gate 10 is closed here, and P01 is retained at
T3 for this exact finite scope.

## Residual trust and non-claims

The evidence trusts the Python interpreter and runtime, standard-library
SHA-256 and SHAKE implementations, operating-system and filesystem behavior,
stable checkout bytes during evaluation, and correctness of the finite checker
source. Source manifests show which bytes were evaluated; they do not prove
those bytes correct or prove faithful runtime execution.

Python constructor seals, object identity, and underscore-private issuers are
API boundaries, not defenses against hostile same-process reflection. The
public application-context fixture binds the value used here but does not
authenticate an external caller. The toy group provides no meaningful
discrete-log hardness or witness/nonce confidentiality.

The owner-local lifecycle is challenge-neutral prefix, exact opaque invocation
reference, precommitment of exact Relations authority, witness occurrence,
nonce, canonical commitment, closed `ResponsePlan`, bases, and resources, then
one consuming finalization. Fresh enters only as a support-point binding at
finalization; FS derives the challenge from frozen `A`. Qualification is a
read-only, non-authoritative audit reconstruction followed by public replay.
Only an admitted completed invocation installs resolvable challenge state;
missing, malformed, or out-of-domain Fresh bindings consume their handles but
remain unresolvable. A valid invocation can retain its resolved challenge when
the later response stage aborts or exceeds a public resource ceiling. This
establishes only modeled capability-flow order. It does not establish
out-of-band challenge ignorance, nonce uniformity or independence, Fresh
sampling, historical artifact-authoring chronology, or general adversarial non-
anticipation. `ResponsePlan` is not a strategy language.

This package does not establish CFRG conformance, production security, general
completeness or soundness, proof of knowledge, malicious-verifier zero
knowledge, ROM or QROM security, secure composition, compiler correctness, or
architecture-wide sufficiency.

# Native FRI/IOR Semantic Validation

This package is a standalone, finite executable test of the candidate protocol
model against a native FRI interactive-oracle interaction. It is a temporary
research instrument, not a compiler component, production prover or verifier,
cryptographic security evaluator, or source-conformance implementation.

The package tests this factorization:

```text
native logical-oracle FRI Core
        |
        | commitment/opening construction declaration
        | + checked one-execution receipt
        v
committed FRI Core
        |
        | grinding augmentation declaration
        | + checked one-execution receipt
        v
work-augmented committed FRI Core
        |
        | Fresh challenge interpretation
        v
work-augmented committed FRI Fresh Protocol
        |
        | checked Fiat--Shamir construction over the same Core
        v
work-augmented committed FRI Fiat--Shamir Protocol
```

The finite case currently inhabits that model. This supports retaining the
separation between native oracle semantics, commitment compilation, work
augmentation, and challenge interpretation. It does not establish that the
model supports every FRI variant or IOP, and it does not establish any
soundness, proximity, knowledge, binding, hiding, ROM, or QROM theorem.

The package also contains a separate exact classical control. That additive
lane instantiates the three-fold, scalar-terminal schedule, admits one exact
structural logical-Oracle-to-commitment construction, runs Fresh and strong
Fiat--Shamir interpretations over the same committed Core, and reconstructs
the public Fiat--Shamir execution in a separately coded verifier. It does not
replace or silently reinterpret the earlier control.

## Run

From the repository root:

```sh
python3 -m unittest discover -s evaluation/native-fri-ior/tests
python3 evaluation/native-fri-ior/run.py --check
python3 evaluation/native-fri-ior/generate.py
python3 evaluation/native-fri-ior/generate.py --check-fixtures
```

The first command currently runs 456 tests. The public runner rebuilds and
verifies a report from public fixtures before comparing its projection with a
separately frozen regression golden. Its exact-classical result is produced by
the separately coded verifier directly from the frozen public input and proof;
the producer model is not an alternate public acceptance path. The owner
command reconstructs the earlier five-result capability chain and separately
regenerates and checks the exact native, Fresh, and strong-Fiat--Shamir control.
The final command re-derives every derived vector twice and compares it
byte-for-byte without changing the checkout.

The current public replay has four affirmative implementations or views:

| Lane | Result |
|---|---|
| Native logical-oracle execution | `FRI-IOR-NATIVE-100` |
| Committed public verification | `FRI-IOR-COMMITTED-100` |
| Separately coded public replay | `FRI-IOR-INDEPENDENT-100` |
| Separately coded exact classical public replay | `FRI-IOR-CLASSICAL-INDEPENDENT-100` |

The producer and separately coded replay agree on selected exact positive
public-execution facts: outcome, both fold challenges, ordered initial-domain
indices, proof bytes, and the resource snapshot. Separately, the producer
classifies two authenticated late negatives at distinct refusal boundaries:

- an inconsistent first fold reaches `FRI-IOR-COMMITTED-020`; and
- a fold-consistent excessive terminal degree reaches
  `FRI-IOR-COMMITTED-022`.

That agreement is implementation-diversity and finite falsification evidence.
The second verifier still shares the published term and transcript contract;
it is not independent semantic authority.

## Earlier structural control

The selected case uses the quadratic extension of the 97-element field, an
order-16 initial domain, two binary folds, a degree-less-than-two terminal
polynomial, and four ordered query occurrences. The frozen transcript derives
fold challenges `[1, 59]` and `[0, 54]`, then queries initial-domain indices
`[3, 15, 11, 10]`. Eight logical layer-query occurrences map to five unique
authenticated openings without erasing order or multiplicity.

This is deliberately not Section 5.7 Algorithm 1 of ePrint 2023/1071 at
initial degree bound eight. That source profile performs three folds and sends
a scalar terminal. The executable case is an early-terminated structural
profile, and the source ledger explicitly makes no exact algorithm, theorem,
or implementation-profile correspondence claim.

## Exact classical control

The additive classical lane uses the Goldilocks prime field, an order-64
initial multiplicative domain, degree bound eight, three binary folds, and one
scalar terminal. Four labelled query draws expand to twelve logical layer
occurrences. Three salted SHA-256 pair-leaf trees commit the source and two
folded Oracles; a canonical physical opening table may deduplicate entries
without erasing logical order or multiplicity.

The source Core retains native logical-Oracle publication/query/answer
semantics. A distinct target Core publishes roots and openings. Their exact
structural construction rederives the target, preserves the exact public
Statement and application-context coordinates through its public-environment
map, and checks total publication/coin/query/answer/check/outcome maps,
construction-owned advice shape, public replay closure, and intrinsic bounds
before minting process-local authority. Static construction owns the canonical
physical-opening derivation law and its maximum bound; each run derives and
checks its concrete deduplicated table from the logical occurrences. A
separate one-run checker rebuilds all three roots, verifies native and target
executions independently, and emits an inert receipt for that pair only. Its
semantic receipt identity excludes validation limits and resource snapshots;
a separate validation-basis identity binds those non-semantic conditions.

The committed target has separate Fresh and strong-Fiat--Shamir Protocol
identities over one unchanged Core. The strong transcript binds the complete
public Statement and application context, each prior root, each prior fold
challenge, the scalar terminal before query sampling, and distinct labels.
The separate public verifier independently reimplements term framing,
sampling, Merkle authentication, occurrence coverage, Goldilocks arithmetic,
and all twelve fold equations.

The Relations/Analysis additions remain bounded pressure instruments. PIR now
issues a causal, purpose-bound confidential view of the exact initial Oracle;
Relations compares that view with its separately authorized secret assignment
without putting either material, a digest of it, or the generating trace into
portable identity. The comparison can establish exact whole-carrier material
agreement for this run, while the public relation-run view remains public-only.
Analysis derives a scalar residual with proximity `NotEvaluated`, forms
distinct round-by-round and restricted-restoration questions, and classifies
one direct-FRI parameter substitution as non-vacuous. These paths establish no
theorem truth, applicability, proximity, soundness, outer relation, or property
transport. Durable Analysis promotion still requires an explicit profile and
catalog revision.

## Fixture and authority boundaries

| File | Role |
|---|---|
| `cases/public-inputs.json` | Frozen public Statement, application context, semantic profiles, and transcript plan. |
| `cases/public-proof.json` | Frozen positive committed proof. |
| `cases/public-native-vector.json` | Explicitly declassified complete native trace for validation; forbidden as committed-verifier input. |
| `cases/public-negative-proofs.json` | Two reviewed negative proof vectors; not a complete refusal taxonomy. |
| `cases/replay-policy.json` | Report-local operational limits with no semantic authority. |
| `cases/exact-classical-public-inputs.json` | Frozen exact-classical public Statement, application context, profile identity, and committed-Core identity. |
| `cases/exact-classical-public-proof.json` | Frozen three-root, scalar-terminal exact-classical public proof. |
| `cases/exact-classical-replay-policy.json` | Exact-classical report-local limits with no semantic authority. |
| `cases/source-ledger.json` | Consulted-source identities and metadata; not source authentication or correspondence evidence. |
| `cases/expected-results.json` | Regression golden loaded only after report construction and verification. |
| `cases/owner-generation-input.json` | Declassified toy values that populate private semantic roles; excluded from public replay and containing no real secret. |
| `cases/owner-relation-input.json` | Separately loaded declassified Relations operand; excluded from public replay and not evidence of independent provenance. |
| `cases/exact-classical-owner-generation-input.json` | Declassified toy coefficients and deterministic salt seed occupying owner-only generation roles; excluded from public replay and containing no real secret. |

The public report never reads any owner input or the expected-results golden.
Its source bases are derived from the static transitive local-import closure of
each public entry point, including both separately coded replay modules. The
owner report exports identities, source-basis identities, and result codes, not
coefficients, salts, the source trace, or a complete logical oracle.

Replay assumes a fresh process over a stable checkout. Concurrent mutation of
imported source files during one run is outside the evidence boundary; the
recorded source bases are not a hostile-filesystem attestation.

Full reports written by `run.py`, owner summaries written by `generate.py`,
temporary staging files, caches, retrieved papers, and build products are
disposable outputs and are not committed. The case files above are reviewed
test vectors, authored inputs, and a regression golden rather than disposable
run products.

## Refreeze

Refreezing is an explicit authoring operation:

```sh
python3 evaluation/native-fri-ior/generate.py --refreeze-fixtures
python3 evaluation/native-fri-ior/generate.py --check-fixtures
python3 evaluation/native-fri-ior/run.py --check
python3 -m unittest discover -s evaluation/native-fri-ior/tests
```

The authoring command derives the public vectors twice before replacing them,
verifies the rebuilt public report, and writes the expected projection last.
Each file replacement is atomic, but the set of files is not crash-atomic;
inspect the Git diff and rerun the non-mutating checks after any interruption.

## Research result and remaining pressure

The combined cases are best classified as a conservative semantic extension:
they need explicit logical-oracle access and origin, Core-changing commitment
construction, work augmentation, ordered query occurrences, and typed
Relations and Analysis surfaces while preserving the central Interactive Core
factorization. The exact classical lane now has a frozen, owner-regenerable,
publicly replayable packet for one bounded three-fold scalar-terminal profile
and closes a reusable structural Oracle-commitment construction for one
bounded source/target/profile triple. It does not generalize either result to
other FRI or commitment profiles. The earlier work-augmentation construction
remains validation-bound to one run.

Primary-source pressure from exact and batched FRI, DEEP-FRI and DEEP-ALI,
STIR, Circle FRI, WHIR, and the BCS compiler supports one further localized
proposal: a finite nonadaptive verifier-derived Oracle and query-plan seam.
That proposal is not implemented or durable yet. The exact classical profile
is now executable, while the derived-oracle seam and representative batched,
DEEP, STIR, Circle, WHIR, and BCS constructions remain constructive tests
before broad family support can be claimed.

The research basis and current decisions are recorded in:

- [validation plan](../../docs-next/notes/semantic-revalidation-and-redesign/r2-protocol-witnesses/native-fri-ior-validation-plan.md);
- [source dossier](../../docs-next/notes/semantic-revalidation-and-redesign/r2-protocol-witnesses/native-fri-ior-source-dossier.md);
- [architecture decision](../../docs-next/notes/semantic-revalidation-and-redesign/r2-protocol-witnesses/native-fri-ior-architecture-decision.md);
- [Analysis dossier](../../docs-next/notes/semantic-revalidation-and-redesign/r2-protocol-witnesses/native-fri-ior-analysis-dossier.md); and
- [cross-family pressure synthesis](../../docs-next/notes/semantic-revalidation-and-redesign/r2-protocol-witnesses/fri-ior-variant-pressure-synthesis.md).

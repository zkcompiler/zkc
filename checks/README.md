# Repository checks

This directory is the repository's test and evidence **control plane**. It
answers four operational questions:

1. Which executable checks exist?
2. What narrowly stated claim does each check exercise?
3. What does a passing result explicitly *not* establish?
4. Which checks belong in edit-time, pull-request, research-checkpoint,
   scheduled, freeze, or externally provisioned runs?

It does not define project semantics. Semantic authority remains with the
documents routed from [`docs/README.md`](../docs/README.md), while the
experimental redesign is routed from
[`docs-next/README.md`](../docs-next/README.md). A green command is bounded
evidence about its declared subject, never an automatic theorem, security
claim, compiler-correctness claim, or production-readiness claim.

## Architecture

The project deliberately keeps five roles separate:

```text
normative documents
        |
        +---- evaluation/   exploratory models, witnesses, and falsifiers
        |
        +---- reference/    durable independent semantic twin
        |
        +---- C++ / MLIR / Rust implementation and regression suites
        |
        `---- checks/       inventory, selection, execution provenance
```

`checks/` orchestrates the other roles but owns none of their semantic
judgments. In particular:

- `evaluation/` may answer whether a proposed model is coherent on a finite
  pressure case before product implementation. Its packages may later be
  promoted, replaced, or deleted.
- `reference/` is a long-lived, bounded semantic twin. It should remain small,
  deterministic, and independently implemented where disagreement would be
  useful.
- native and Rust suites test shipped implementation behavior, including
  cross-implementation and pinned-upstream cases.
- external formal readings classify exact receipts against pinned source. They
  are not silently converted into local build success.

The manifest is therefore an execution contract, not a second specification.

## Manifest

[`manifest.json`](manifest.json) is strict JSON. The runner rejects duplicate
keys, unknown fields, unknown tiers, invalid stable IDs, undeclared command
placeholders, missing source paths, and unsupported classifications. Every
check declares:

- a stable semantic ID and human title;
- its subject and the exact bounded claim exercised;
- a classification and one or more methods;
- the source files that define the check;
- its execution tiers, qualitative cost, environment, and shardability;
- whether failure blocks that tier;
- at least one explicit non-claim; and
- either an argument-vector command or an externally owned workflow.

Commands are argument vectors rather than shell strings. The supported
placeholders are `{repo}`, `{python}`, `{build_dir}`, and `{artifacts}`. This
keeps command resolution inspectable and avoids accidental shell
interpretation. The runner never retries a failure and applies no hidden
timeout.

The qualitative cost labels are routing hints, not performance promises. They
must be corrected from measured results when the shape of a check changes.

## Tiers

The tiers are named execution contexts, not an implicit monotone ladder:

| Tier | Intended use |
|---|---|
| `developer` | Cheap source-policy, control-plane, and stable-reference feedback. |
| `pr` | Durable public integration checks for implementation and conformance changes. |
| `research-checkpoint` | Bounded redesign witnesses needed to close one coherent semantic boundary. |
| `scheduled` | Broader research reruns and diagnostics that are too slow or noisy per edit. |
| `release-freeze` | Every locally executable durable and research check, including the canonical expensive Analysis run. |
| `formal-reading` | A pinned external checkout and proof-assistant environment owned by its workflow. |

Because the tiers answer different questions, callers should select the tier
that matches the changed authority surface. `release-freeze` is deliberately
expensive and is not an edit-time or routine review loop.

## Use

Validate and inspect the inventory without executing checks:

```sh
python3 -B checks/run.py validate
python3 -B checks/run.py list --tier developer
python3 -B checks/run.py list --tier research-checkpoint
python3 -B checks/run.py list --check research.native-fri-ior --json
```

Resolve a command set without executing it:

```sh
python3 -B checks/run.py run --tier pr --dry-run
```

Run a tier or selected stable IDs:

```sh
python3 -B checks/run.py run --tier developer
python3 -B checks/run.py run \
  --check research.duplex-transcript \
  --check research.native-fri-ior \
  --keep-going
```

For a non-default native build directory:

```sh
python3 -B checks/run.py run \
  --tier pr \
  --build-dir /absolute/path/to/configured-build
```

By default, each run writes logs, declared child artifacts, and `result.json`
under the ignored `target/checks/` tree. `--artifacts-dir` and `--result` can
place them elsewhere. The result records the manifest digest, selected tier or
IDs, revision, clean/dirty state without path disclosure, environment,
resolved argument vectors, elapsed time, return code, logs, and exact status
for each check.

## Status and exit semantics

The result vocabulary is intentionally not Boolean:

| Status | Meaning |
|---|---|
| `pass` | The command returned zero and produced every declared artifact. |
| `fail` | The command returned nonzero, or omitted a declared artifact. |
| `cannot-run` | A declared tool, configured build, working directory, or process launch was unavailable. |
| `external` | The check belongs to a separately provisioned workflow; no local pass was inferred. |
| `not-run` | Execution stopped after an earlier blocking failure. |
| `dry-run` | Resolution succeeded but execution was intentionally omitted. |

Exit `0` means the selected local blocking checks passed (or the operation was
an explicit dry run). Exit `1` means a blocking check failed. Exit `2` means
the selection was incomplete or the manifest/selection was invalid. A
non-blocking diagnostic failure is retained as an observation; it is not
rewritten as a semantic failure.

## Method policy

No single method is treated as sufficient. Checks may declare known-answer,
negative, round-trip, differential, property, metamorphic, mutation,
bounded-exhaustive, translation-validation, fuzzing, sanitizer,
pinned-upstream replay, formal-reading, policy, static-analysis, or diagnostic
methods. A declaration says which mechanism is present; it does not grade its
quality automatically.

The intended long-term pattern is:

```text
research pressure case
        |
        v
accepted law and machine-readable fixture
        |
        +---- independent Python result
        |
        +---- implementation result
        |
        `---- differential / properties / mutations / upstream reading
                         |
                         v
                 bounded evidence record
```

Python twins are reserved for deterministic, stable, high-risk semantic
surfaces where a structurally independent result is valuable. They are not a
second implementation of the entire product. Exploratory packages graduate
only when the exercised law, fixture, expected outcome, and non-claims have
stabilized; otherwise they remain research instruments or are retired.

## Performance policy

The property-Analysis suite is retained as one canonical one-process freeze
check. Process-level test sharding is not used as a default optimization:
earlier measurement showed that isolated workers replicated the dominant
fixture construction. The next optimization step is measurement by phase,
followed by build-once/check-many restructuring of immutable fixtures and only
then safe parallelism. The canonical one-process path remains available as an
equivalence and freeze gate throughout that work.

Routine development must use focused IDs or the smaller tiers. A freeze run is
performed once for a meaningful checkpoint, not repeatedly until it happens
to pass.

## Mechanization boundary

The project is not adopting an additional specification language at this
stage. The manifest and semantic artifacts remain mechanization-ready by using
stable rule/check IDs, explicit inputs, explicit failure outcomes,
machine-readable fixtures, and named ownership boundaries. If duplicated
hand-written semantics later become the dominant maintenance cost, those
artifacts provide the right input for a separate mechanization decision
without making today's research depend on a new toolchain.

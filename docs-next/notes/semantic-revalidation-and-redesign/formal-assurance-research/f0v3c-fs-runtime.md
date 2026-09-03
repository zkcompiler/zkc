# Finite canonical-framed Fiat--Shamir runtime

> **State:** `Affirmative/F0V3C-A-FS-RUNTIME`; two owner-determined finite
> constructions execute and replay completely.
> **Authority:** None. This research package edits no owner page, profile
> manifest, publication table, or normative identity registry.
> **Executable evidence:**
> [`evaluation/formal-source-fs-runtime-f0v3c`](../../../../evaluation/formal-source-fs-runtime-f0v3c/README.md)

## 1. Exact question and answer

Do the current canonical-framed owner pages determine, admit, execute, and
independently replay both a bounded retrying construction and a one-shot
construction over the admitted finite Schnorr subject without an
executor-local semantic choice?

Yes, for these two exact constructions and their complete finite corpora. The
canonical-framed owner page now fixes the nominal application-domain
declaration body as one nonempty semantic symbol with no surplus field. The
earlier owner gap is therefore closed at the pinned source revision.

## 2. Admitted constructions

Both constructions reuse the admitted additive `Z/3Z` Schnorr Core and Fresh
Protocol:

```text
Core:  zkcidv0:pir.interactive-core:dcb652fdca792d8664c51f2b98dca17d530607ff994c1eab15a59ed5c61cf2b8
Fresh: zkcidv0:pir.protocol:cc2fee36c903072621553a98fdb0d7bf3b84d13a18b0a51b04b7235367b7324f
```

The retrying construction keeps its prior two-draw rejection sampler and exact
identities:

```text
TranscriptConstruction: zkcidv0:pir.transcript-construction:84873ab6046a1ec005fed9b90cdabb9b6532ffbba890b00dadad53558b94f4ee
FS Protocol:            zkcidv0:pir.protocol:83554765ae235514d1e77a72ca179315020c7d9efc320276a019ec6ce5827ae9
```

The second construction admits one draw, always accepts, and decodes every
draw output:

```text
TranscriptConstruction: zkcidv0:pir.transcript-construction:eaebbb902e26db8af22147b867676769bdeebfa9dc95c58af007b25d53876a78
FS Protocol:            zkcidv0:pir.protocol:4a80c29a982ac7ba9dfca5fd86d7c7f1507e2005da407b14691191f79f9bfc21
```

Both construction checks conclude `StructurallyConstructed`. The occurrence,
value, and challenge maps have sizes six, five, and one.

## 3. Runtime and independent replay

For each construction, one path executes the Core through the transcript
resolver while a separate module independently reconstructs initialization,
frames, namespaces, draw transitions, Core occurrences, terminals, and exact
completed-record variants. The replay module does not import the executor.
Every complete record and transition sequence agrees, and three malformed
record controls are refused.

Each corpus contains all 27 strategy triples and all 27 verifier triples:

| Lane | Retrying | One-shot |
|---|---:|---:|
| `Accepted` | 24 | 22 |
| `Rejected` | 24 | 32 |
| `Aborted` | 0 | 0 |
| `InterpretationFailed` | 6 | 0 |
| `StrategyStopped` | 0 | 0 |
| `OperationalNoncompletion` | 0 | 0 |

The retrying corpus retains its six measured two-draw exhaustions. The
one-shot construction has no exhaustion because its acceptance and decode
algorithms are total.

## 4. Frozen derivation functions and views

The retrying run set and derivation table remain in `expected-runs.json` and
`derivation-vectors.json`. The one-shot run set and its own nine-entry table
are independently frozen in `expected-runs-one-shot.json` and
`derivation-vectors-one-shot.json`. Every table entry carries the exact
statement, commitment, transcript-prefix digest, decoded challenge, and draw
count.

Both subjects reproduce the transcript declaration, required influence,
challenge transition, construction, and execution views. The two current
schema compilers accept every reproduced construction view.

## 5. Findings

| Contract clause | Frozen result |
|---|---|
| owner admission | `Affirmative/F0V3C-A-OWNER-ADMISSION` |
| retrying execution | `Affirmative/F0V3C-A-FINITE-EXECUTION` |
| one-shot execution | `Affirmative/F0V3C-A-ONE-SHOT-EXECUTION` |
| independent replay | `Affirmative/F0V3C-A-INDEPENDENT-REPLAY` |
| view reproduction | `Affirmative/F0V3C-A-VIEW-REPRODUCTION` |
| six-lane partition | `Affirmative/F0V3C-A-SIX-LANE-PARTITION` |
| derivation functions | `Affirmative/F0V3C-A-DERIVATION-VECTORS` |
| aggregate | `Affirmative/F0V3C-A-FS-RUNTIME` |

## 6. Result boundary

This package establishes owner-determined construction for two exact finite
subjects, exhaustive execution, independent exact-record replay, view-schema
conformance, measured lane counts, and two machine-readable derivation
functions.

It does not establish publication, arbitrary-Core behavior, general evaluator
correctness, compiler/backend/provider correspondence, relation truth,
theorem applicability, protocol soundness, zero knowledge, Fiat--Shamir
security, random-oracle or quantum-random-oracle security, concrete-hash
suitability, duplex-sponge behavior, or production readiness.

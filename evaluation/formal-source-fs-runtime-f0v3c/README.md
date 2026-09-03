# Finite canonical-framed Fiat--Shamir runtime

This package asks one exact question: do the current canonical-framed owner
pages determine, admit, execute, and independently replay both a bounded
retrying construction and a one-shot construction over the admitted finite
Schnorr subject without an executor-local semantic choice?

Run from the repository root:

```sh
python3 -B evaluation/formal-source-fs-runtime-f0v3c/run.py --check
```

The frozen aggregate is `Affirmative/F0V3C-A-FS-RUNTIME`. The canonical
application-domain page now supplies the exact nominal declaration body that
was absent from the earlier packet, so both construction identities are
owner-determined at the pinned source revision.

## Admitted subjects

Both subjects reuse the admitted additive `Z/3Z` Schnorr Core and Fresh
Protocol. They share a 32-byte state, bounded transcript bytes, an all-zero
initial state, eight-byte draws, one challenge rule, the same canonical
framing, and a typed sampling-exhausted failure.

| Subject | Maximum draws | Acceptance | Decode |
|---|---:|---|---|
| retrying | 2 | hash-quartile rejection sampling | accepted quartiles map to `0`, `1`, or `2` |
| one-shot | 1 | always accepts | all four hash quartiles map totally to `0`, `1`, or `2` |

The retrying construction and Protocol identities remain:

```text
zkcidv0:pir.transcript-construction:84873ab6046a1ec005fed9b90cdabb9b6532ffbba890b00dadad53558b94f4ee
zkcidv0:pir.protocol:83554765ae235514d1e77a72ca179315020c7d9efc320276a019ec6ce5827ae9
```

The one-shot construction and Protocol identities are:

```text
zkcidv0:pir.transcript-construction:eaebbb902e26db8af22147b867676769bdeebfa9dc95c58af007b25d53876a78
zkcidv0:pir.protocol:4a80c29a982ac7ba9dfca5fd86d7c7f1507e2005da407b14691191f79f9bfc21
```

Both share Core
`zkcidv0:pir.interactive-core:dcb652fdca792d8664c51f2b98dca17d530607ff994c1eab15a59ed5c61cf2b8`.
Each has occurrence, value, and challenge maps of sizes six, five, and one,
and each construction check concludes `StructurallyConstructed`.

## Execution and replay

The first path drives the Core engine through the resolver hooks, emits the
ordered initialization and condition frames, derives the complete challenge
namespace, performs the bounded draw loop, records each transition, and closes
the exact completed-record variant.

The second path independently implements framing, namespace construction, draw
progression, Core execution, lane selection, and receipt construction. It does
not import the executor. It recomputes each record and requires exact
dictionary equality. Three directed record-shape mutations remain frozen as
negative controls.

Each subject has all 27 `(statement, witness, nonce)` strategy runs and all 27
`(statement, commitment, response)` verifier inputs:

| Lane | Retrying | One-shot |
|---|---:|---:|
| `Accepted` | 24 | 22 |
| `Rejected` | 24 | 32 |
| `Aborted` | 0 | 0 |
| `InterpretationFailed` | 6 | 0 |
| `StrategyStopped` | 0 | 0 |
| `OperationalNoncompletion` | 0 | 0 |

The six retrying interpretation failures remain genuine two-draw sampling
exhaustions. The one-shot subject is total over the finite domain and therefore
has no exhaustion run.

## Frozen outputs

`expected-runs.json` and `derivation-vectors.json` retain the retrying
subject's 54 runs and nine-entry derivation function.
`expected-runs-one-shot.json` and `derivation-vectors-one-shot.json` freeze
the second subject independently. The one-shot table is total:

| `(statement, commitment)` | Derived challenge |
|---|---:|
| `(0,0)`, `(0,1)`, `(2,0)`, `(2,1)` | 2 |
| `(0,2)`, `(1,2)` | 0 |
| `(1,0)`, `(2,2)` | 1 |
| `(1,1)` | 2 |

Both subjects derive the four canonical-framed construction views and the
execution view, and both current schema compilers accept the reproduced view
values.

## Frozen findings

| Clause | Outcome |
|---|---|
| owner admission | `Affirmative/F0V3C-A-OWNER-ADMISSION` |
| retrying execution | `Affirmative/F0V3C-A-FINITE-EXECUTION` |
| retrying replay | `Affirmative/F0V3C-A-INDEPENDENT-REPLAY` |
| view reproduction | `Affirmative/F0V3C-A-VIEW-REPRODUCTION` |
| six-lane partition | `Affirmative/F0V3C-A-SIX-LANE-PARTITION` |
| retrying derivation table | `Affirmative/F0V3C-A-DERIVATION-VECTORS` |
| one-shot execution | `Affirmative/F0V3C-A-ONE-SHOT-EXECUTION` |
| aggregate | `Affirmative/F0V3C-A-FS-RUNTIME` |

## Result boundary

A passing check establishes owner-determined construction for the two exact
subjects, exhaustive execution of their finite corpora, equality of two
runtime paths, exact-field replay refusal, measured lane counts, frozen
derivation tables, and conformance of reproduced view values to the pinned
schemas.

It does not establish publication, arbitrary-Core behavior, general evaluator
correctness, compiler/backend/provider correspondence, theorem applicability
or truth, protocol soundness, zero knowledge, Fiat--Shamir security,
random-oracle or quantum-random-oracle security, concrete-hash suitability,
duplex-sponge behavior, or production readiness.

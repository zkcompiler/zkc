# Finite canonical-framed Fiat--Shamir runtime

This package asks one exact question: do the current canonical-framed owner
pages determine, admit, execute, and independently replay both a bounded
retrying construction and a one-shot construction over the admitted finite
Schnorr subject without an executor-local semantic choice?

Run from the repository root:

```sh
python3 -B evaluation/formal-source-fs-runtime-f0v3c/run.py --check
```

The frozen aggregate is `Affirmative/F0V3C-A-FS-RUNTIME`. The two exact
constructions admit and execute. Each challenge-transition rule now carries
the occurrence's position in the exact total Core schedule. The Schnorr
challenge is `Always`, has no public conditions, and therefore emits no frame
under Section 4; its execution view consequently carries
`frame_schedule_coordinate = None` while retaining its total-schedule
position.

## Admitted subjects

Both subjects reuse the admitted additive `Z/3Z` Schnorr Core and Fresh
Protocol. They share a 32-byte state, bounded transcript bytes, an all-zero
initial state, eight-byte draws, one challenge rule, the same canonical
framing, and a typed sampling-exhausted failure.

| Subject | Maximum draws | Acceptance | Decode |
|---|---:|---|---|
| retrying | 2 | hash-quartile rejection sampling | accepted quartiles map to `0`, `1`, or `2` |
| one-shot | 1 | always accepts | all four hash quartiles map totally to `0`, `1`, or `2` |

The retrying construction and Protocol identities are:

```text
zkcidv0:pir.transcript-construction:c8d7a037c4ba85d9824d33217f5e0101711f1fe515f0a8da8bd8ebdc811d233f
zkcidv0:pir.protocol:6af3a4c7c224014f49c236b73a6bc64e0365429cd969a7ac2eef06d64ff0d3a8
```

The one-shot construction and Protocol identities are:

```text
zkcidv0:pir.transcript-construction:8bee78815de3b3beaf327e8d8032ea516857e991e2ef6b3f5db7360d01c405d4
zkcidv0:pir.protocol:8bde0b353976922b49cc9eb35f5ad34f7c307f3767103d7cca91dcc2a7a5aeb0
```

Both share Core
`zkcidv0:pir.interactive-core:b1f9e272e88b994475911a42fb016f7ac6bf8acf039c69d094907801c24fcca6`.
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
| `Accepted` | 22 | 18 |
| `Rejected` | 32 | 36 |
| `Aborted` | 0 | 0 |
| `InterpretationFailed` | 0 | 0 |
| `StrategyStopped` | 0 | 0 |
| `OperationalNoncompletion` | 0 | 0 |

At the repaired identities, neither finite corpus exhausts sampling. This is a
measured fact for these exact 54-run corpora, not a totality statement about
the retrying sampler.

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

Both subjects derive and validate all four construction views through both
current schema compilers. They also derive the execution view. The transition
view uses the total schedule position for the unframed challenge, and the
execution view records that no frame-schedule entry exists.

## Repaired-body pressure suite

A separate admitted Core has two root public bindings and two challenges at
occurrence positions 1 and 3. Its construction uses distinct decoder result
types and draw bounds `(1,1)` and `(2,3)`. The projected transition body keeps
one ordered rule per challenge; the influence body keeps both binding atoms
and one symbolic `EveryActualDrawOf` entry for the earlier challenge. Both
schema compilers accept all three construction-owned values.

## Frozen findings

| Clause | Outcome |
|---|---|
| owner admission | `Affirmative/F0V3C-A-OWNER-ADMISSION` |
| retrying execution | `Affirmative/F0V3C-A-FINITE-EXECUTION` |
| retrying replay | `Affirmative/F0V3C-A-INDEPENDENT-REPLAY` |
| Schnorr transition/execution views | `Affirmative/F0V3C-A-TOTAL-SCHEDULE-PROJECTION` |
| repaired-body pressure projection | `Affirmative/F0V3C-A-REPAIRED-VIEW-PROJECTION` |
| six-lane partition | `Affirmative/F0V3C-A-SIX-LANE-PARTITION` |
| retrying derivation table | `Affirmative/F0V3C-A-DERIVATION-VECTORS` |
| one-shot execution | `Affirmative/F0V3C-A-ONE-SHOT-EXECUTION` |
| aggregate | `Affirmative/F0V3C-A-FS-RUNTIME` |

## Result boundary

A passing check establishes owner-determined construction for the two exact
subjects, exhaustive execution of their finite corpora, equality of two
runtime paths, exact-field replay refusal, measured lane counts, frozen
derivation tables, all four Schnorr construction views, both execution views,
and the repaired-body pressure projection. It checks the owner distinction
between a challenge's total-schedule position and its optional frame-schedule
coordinate.

It does not publish owner text, cover arbitrary Cores, prove general evaluator
correctness, establish
compiler/backend/provider correspondence, prove theorem applicability or
truth, protocol soundness, zero knowledge, Fiat--Shamir security, random-oracle
or quantum-random-oracle security, concrete-hash suitability, duplex-sponge
behavior, or production readiness.

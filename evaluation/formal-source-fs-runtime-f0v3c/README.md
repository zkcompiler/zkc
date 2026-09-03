# Finite canonical-framed Fiat--Shamir runtime

This package asks one exact question: can the current canonical-framed owner
text determine, admit, execute, and independently replay one same-Core
Fiat--Shamir construction over the admitted finite Schnorr subject without an
executor-local semantic choice?

Run from the repository root:

```sh
python3 -B evaluation/formal-source-fs-runtime-f0v3c/run.py --check
```

The frozen aggregate is `CannotAnswer/F0V3C-C-FS-RUNTIME`. The candidate is
fully executable, but owner admission is not determined: lines 68--71 of
`docs-next/pir/fiat-shamir.md` require the exact nominal
`pir.fs-application-domain` declaration body from the companion page, while
lines 2256--2259 of `docs-next/pir/interactive-core.md` recognize that
declaration kind without defining its body. The executable therefore keeps one
explicit proposed body and does not call its resulting identities admitted.

## Candidate subject

The package reuses the target package's admitted additive `Z/3Z` Schnorr Core
and Fresh Protocol without changing either body. Its proposed construction has
a 32-byte state, a bounded transcript byte type, an all-zero initial state,
eight-byte draws, at most two draws, one challenge rule, and a typed
sampling-exhausted failure. The proposed application-purpose body is the
single-field record containing the symbol `finite-schnorr-runtime`.

Five portable algorithms form the transition suite:

| Algorithm | Exact term-level behavior |
|---|---|
| `CanonicalFramedAbsorb` | `sha2-256(state || frame)` |
| `CanonicalFramedSqueezeBytes` | hashes `state || namespace || u64be(count)` and selects one of four fixed eight-byte outputs by the resulting unsigned 64-bit quartile |
| `CanonicalFramedAdvanceState` | `sha2-256(state || namespace || u64be(count) || output)` |
| `CanonicalFramedAccept` | hashes the output and accepts exactly when the first unsigned 64 bits are below `3 * 2^62` |
| `CanonicalFramedDecode` | hashes the output and maps the first three unsigned 64-bit quartiles to `0`, `1`, and `2` in `Z/3Z`; the fourth maps to `2` but is unreachable after acceptance |

Each algorithm is a canonical term over admitted primitive references, has the
target package's exact evaluation contract, and is type-checked before use.
Every invocation authenticates the algorithm's module dependency closure and
evaluation contract. Consequently the suite's candidate meaning comes from
its frozen terms and admitted primitive denotations, not from an unrecorded
host callback. SHA-256 is used only as a deterministic primitive in a toy
correspondence instrument; no distribution or security property is assumed.

Under the explicit proposed body, the construction and Protocol identities are
respectively:

```text
zkcidv0:pir.transcript-construction:84873ab6046a1ec005fed9b90cdabb9b6532ffbba890b00dadad53558b94f4ee
zkcidv0:pir.protocol:83554765ae235514d1e77a72ca179315020c7d9efc320276a019ec6ce5827ae9
```

They share Core
`zkcidv0:pir.interactive-core:dcb652fdca792d8664c51f2b98dca17d530607ff994c1eab15a59ed5c61cf2b8`
with the admitted Fresh Protocol. The occurrence, value, and challenge maps
have sizes six, five, and one, and the checked candidate conclusion is
`StructurallyConstructed`. These are reproducible proposal-local facts, not
owner-issued admission.

## Execution and replay

The first path drives the Core engine through the resolver hooks. It emits the
ordered initialization and condition frames, derives the complete challenge
namespace, performs the bounded draw loop, records each draw and state
transition, emits either an `FSChallengeReceipt` or an
`FSSamplingFailureReceipt`, evaluates the Schnorr check, and closes the exact
completed-record variant.

The second path separately implements framing, namespace construction, draw
progression, Core execution, lane selection, and receipt construction. It does
not import the executor. It recomputes each record and requires exact dictionary
equality, so missing, surplus, or wrong-variant fields fail. Three directed
record-shape mutations are frozen as negative controls.

The finite corpus contains all 27 `(statement, witness, nonce)` strategy runs
and all 27 `(statement, commitment, response)` verifier inputs. Both paths
agree on all 54 records and transition sequences. The measured outcome
partition is:

| Lane | Runs |
|---|---:|
| `Accepted` | 24 |
| `Rejected` | 24 |
| `Aborted` | 0 |
| `InterpretationFailed` | 6 |
| `StrategyStopped` | 0 |
| `OperationalNoncompletion` | 0 |

The six interpretation failures are genuine two-draw sampling exhaustions in
the chosen finite suite; the check freezes them instead of tuning the suite to
remove them.

## Frozen outputs and views

`expected-runs.json` records every case name, lane, completed-record digest,
transcript-prefix digest, and derived result. `derivation-vectors.json` gives
the exact nine-element function from `(challenge, statement, transcript
prefix)` to a decoded value or exhaustion, including enough canonical frame
material to reconstruct every prefix. It is the machine-readable handoff for a
later provider comparison.

The package derives the four canonical-framed construction views and validates
each value with both schema compilers from the predecessor family-view package.
It separately derives the `CanonicalFramedExecutionViewBody` fields for this
candidate, including resolver coordinates, receipt schemas, the six-lane
partition, and replay qualification.

## Frozen findings

| Clause | Outcome |
|---|---|
| admission | `CannotAnswer/F0V3C-C-APPLICATION-DOMAIN-BODY` |
| execution | `Affirmative/F0V3C-A-FINITE-EXECUTION` |
| replay | `Affirmative/F0V3C-A-INDEPENDENT-REPLAY` |
| views | `Affirmative/F0V3C-A-VIEW-REPRODUCTION` |
| outcome partition | `Affirmative/F0V3C-A-SIX-LANE-PARTITION` |
| derivation function | `Affirmative/F0V3C-A-DERIVATION-VECTORS` |
| aggregate | `CannotAnswer/F0V3C-C-FS-RUNTIME` |

## Result boundary

A passing check establishes reproducibility of the candidate terms and
identities, complete enumeration of this finite corpus, equality of two runtime
paths, exact-field replay refusal, measured lane counts and exhaustion, frozen
derivation vectors, and conformance of the candidate view values to the current
schemas.

It does not establish owner admission or publication, arbitrary-Core behavior,
general evaluator correctness, compiler/backend/runtime implementation
correspondence, provider correspondence, theorem applicability or truth,
protocol soundness, zero knowledge, Fiat--Shamir security, random-oracle or
quantum-random-oracle security, SHA-256 suitability, duplex-sponge behavior, or
production readiness.

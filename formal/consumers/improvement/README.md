# Formal improvement consumer

This package is an independent Lean consumer of the maintained `formal` library.
The [check](check.py) beside this page copies its modules into a fresh Lake
consumer, builds them against the maintained package and audits their axiom
cones; `just test-lean` runs it.

## Results and limits

| Area | Checked result | Scope and design consequence |
|---|---|---|
| Claim composition | [Claims.lean](Claims.lean): cubic sum reduction followed by virtual-product expansion into three opening obligations; honest completeness; terminal composition | Uses the actual intermediate claim and existing `ReductionContract.then`. The private-object environment occurs in semantic propositions, not verifier inputs. PCS soundness is a required supplied contract |
| Challenge fixation | Same module: fixed degree-three collision count/mass; at most one cancelling challenge for two fixed nonzero batch errors; cancellation after every known challenge if errors are adaptive | Degree bounds and pre-challenge fixation are indispensable. No arbitrary-round/adaptive/FS security theorem is claimed |
| Execution | [Execution.lean](Execution.lean): actual three-operation cubic verifier prefix, coefficient evaluation/degree laws, exact receipt characterization and composed reduction contract | Returning residual obligations is distinct from terminal acceptance. Malformed/incorrect pre-challenge inputs, later missing/incorrect values and exhausted sampling have exact outcome/state/event controls |
| Sharing | [Sharing.lean](Sharing.lean): an accepted, well-formed `n+1`-node DAG expands to `2^(n+1)-1` syntax occurrences | At `n=20`, 21 versus 2,097,151. This is a proved syntax-size obstruction, not measured wall-clock time, physical allocation or a new compact checker |
| Certificates | [HornerCertificate.lean](HornerCertificate.lean): exact finite codec dispatches to installed direct/Horner rules; actual Sumcheck child candidate is consumed with its existing execution theorem | Rejects unknown version/rule, missing/trailing data, wrong source/operand/rule. This validates a consumer boundary; the two-word prototype is not the production artifact format or a native exporter |

`Claim` has object-dependent point types. Controls show that object identity,
coordinate order and all residuals matter. The predicate that all claims hold
does not itself authenticate transcript order; batching must bind the same
ordered bundle before its challenge. The proposed production descriptor and
multi-round/multi-point API remain open to the contrasting workloads.

## Validation

The check builds a fresh consumer, audits stored declarations and their axiom
cones, and records input hashes for the current checkout. It permits only
`propext`, `Classical.choice` and `Quot.sound`. Dependency objects may be reused;
consumer objects are built in the new output directory.

Run it with `just test-lean`. The [workflow](../../../.github/workflows/ci.yml)'s
manual `optional` formal-checks scope also runs it; pull-request checks do not build Lean.

## Reproduce

After installing the pinned toolchain and preparing the main package's pinned
dependencies, choose a new output directory:

```sh
python3 formal/consumers/improvement/check.py \
  --output /tmp/zkc-formal-improvement-replay
```

The runner copies the four modules into a separate Lake package, depends on the
maintained library, builds and audits all four modules, and rejects input drift
or a missing audit marker. These controls add no production admission rule or
native exporter. Broader claim APIs, portable artifact composition and compact
graph checking retain their own [formal questions](../../docs/native-connection.md).

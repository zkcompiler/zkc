# Formal improvement consumer

This package is an independent Lean consumer of the maintained `formal` library.
The [check](check.py) beside this page copies its modules into a fresh Lake
consumer, builds them against the maintained package and audits their axiom
cones; `just test-lean` runs it.

The result supports concrete design work now: explicit evaluation obligations,
consumer-installed finite transformation rules and a joint source/certificate
design for shared arithmetic. It also supports retaining the existing execution,
refinement and specialized quadratic Sumcheck foundations.

## Results and limits

| ID | Checked result | Scope and design consequence |
|---|---|---|
| FI-CLAIMS | [Claims.lean](Claims.lean): cubic sum reduction followed by virtual-product expansion into three opening obligations; honest completeness; terminal composition | Uses the actual intermediate claim and existing `ReductionContract.then`. The private-object environment occurs in semantic propositions, not verifier inputs. PCS soundness is a required supplied contract |
| FI-FRESHNESS | Same module: fixed degree-three collision count/mass; at most one cancelling challenge for two fixed nonzero batch errors; cancellation after every known challenge if errors are adaptive | Degree bounds and pre-challenge fixation are indispensable. No arbitrary-round/adaptive/FS security theorem is claimed |
| FI-EXECUTION | [Execution.lean](Execution.lean): actual three-operation cubic verifier prefix, coefficient evaluation/degree laws, exact receipt characterization and composed reduction contract | Returning residual obligations is distinct from terminal acceptance. Malformed/incorrect pre-challenge inputs, later missing/incorrect values and exhausted sampling have exact outcome/state/event controls |
| FI-SHARING | [Sharing.lean](Sharing.lean): an accepted, well-formed `n+1`-node DAG expands to `2^(n+1)-1` syntax occurrences | At `n=20`, 21 versus 2,097,151. This is a proved syntax-size obstruction, not measured wall-clock time, physical allocation or a new compact checker |
| FI-CERTIFICATE | [HornerCertificate.lean](HornerCertificate.lean): exact finite codec dispatches to installed direct/Horner rules; actual Sumcheck child candidate is consumed with its existing execution theorem | Rejects unknown version/rule, missing/trailing data, wrong source/operand/rule. This validates a consumer boundary; the two-word prototype is not the production artifact format or a native exporter |

`Claim` has object-dependent point types. Controls show that object identity,
coordinate order and all residuals matter. The predicate that all claims hold
does not itself authenticate transcript order; batching must bind the same
ordered bundle before its challenge. The proposed production descriptor and
multi-round/multi-point API remain open to the contrasting workloads.

## Validation

The new modules contain **53 authored theorems**. A fresh standalone Lake
consumer audits **308 stored declarations, including 158 theorem declarations**
when generated versions are counted. Only `propext`, `Classical.choice` and
`Quot.sound` occur in their audited axiom cones. The successful run records 319
source inputs with no drift and uses Lean 4.33.1. Dependency objects may be
reused; experiment objects are built in the new output directory.

The [workflow](../../../.github/workflows/ci.yml) runs maintained validation
on PRs and main pushes, with weekly/manual fresh reproduction.

## Reproduce

After installing the pinned toolchain and preparing the main package's pinned
dependencies, choose a new output directory:

```sh
python3 formal/consumers/improvement/check.py \
  --output /tmp/zkc-formal-improvement-replay
```

The runner copies the four experiment modules into a separate Lake package,
depends on the real main package, builds/audits all four modules, hashes current
build inputs and rejects drift or a missing audit marker. It neither imports
historical review receipts as proof inputs nor changes their pins.

These modules are classified for promotion into maintained Lean APIs once real
consumers and the remaining gates justify that move. CI should move to the
maintained successors before this package retires.

## Handoff

Review the four experiment modules together. They add no production admission
rule, protocol definition or change to an existing maintained theorem statement.

The next semantic deliverables are an actual multi-round/multi-point claim
composition with explicit terminal obligations, and the first bounded-machine
encoding contract. Memory/lookup and AIR/FRI then discriminate the common API.
Portable artifact composition and compact graph checking have separate proof
and implementation gates; the present experiments establish their starting
points, not completion of those projects.

# Formal composition consumer

This package is an independent Lean consumer of the maintained `formal` library.
The [check](check.py) beside this page copies its modules into a fresh Lake
consumer, builds them against the maintained package and audits their axiom
cones; `just test-lean` runs it.

## Results

| ID | Checked result | Scope |
|---|---|---|
| FC-MLE | [Multilinear.lean](Multilinear.lean): ordered Boolean-value tables, arbitrary-point interpolation, virtual equality-weighted quadratic evaluation and Boolean-sum laws | A logical reference representation; no prescribed native layout |
| FC-COMPOSE | [Claims.lean](Claims.lean): two different-point evaluation claims, batching, arbitrary adaptive Sumcheck rounds, an actual returned point/scalar, and two final object-indexed openings | Reuses maintained quadratic Sumcheck and `ReductionContract.then`; verifier functions do not receive the private tables |
| FC-SOURCE | Same module: effectful `rounds_outcome` and `source_reduction` for arbitrary stateful message/react callbacks | The latter consumes the actual round receipt and exact bundle returned by `finish`; typed messages, no new byte codec |
| FC-PROBABILITY | `Claims.soundness`: ordinary interactive error at most `(1+2*n)/|F|`, plus honest completeness for every tape | Two fixed equal-dimension input claims; batching precedes adaptive prover selection; subsequent round challenges are independent uniform samples; terminal checker must be sound |
| FC-MACHINE | [Machine.lean](Machine.lean): wrapping accumulator machine with advice, branching, static-address memory and successful completion; integer local constraints; arbitrary-row decoding; global encoding soundness and completeness | Every admitted program, positive word modulus, memory size and bound; no real ISA mapping or full field AIR |
| FC-FIELD | `field_add_iff`: modular addition constraint iff integer equation under word ranges, Boolean carry and `P >= 2*W` | This equation only; range enforcement, remaining instructions and the full arithmetization are separate |
| FC-CONTROLS | [Controls.lean](Controls.lean): two-point/two-round receipts, arbitrary honest tapes and adversarial semantic controls | Kernel-checked examples and counterexamples; the fixture opening oracle is not a PCS |

The key new result is a composed probability theorem, not just another algebraic
identity. The initial error vector is fixed before batching; each round message
may adapt to earlier challenges. Final opening replies may depend on the completed
tape. The opening checker parameter has perfect semantic soundness. Instantiating
a cryptographic PCS requires a further experiment and error argument, and is not
claimed by the test oracle.

Machine soundness quantifies over **arbitrary satisfying encoded witnesses**.
It does not assume that the witness came from an honest encoder. The public
statement map is identity and retains the exact program, execution bound,
accumulator input/output and both memory boundaries. `encoding_adequacy` proves
equivalence of the two existential relations. The model's `Executes` relation
requires a final halt; a correct prefix is insufficient. There is no theorem yet
connecting the machine constraints to this package's evaluation protocol.

## Negative controls and design consequences

The claim controls reject substituted object identities and permuted coordinates,
and demonstrate that omitting a residual obligation hides falsehood. They retain
a cancelling fixed bad pair at one batching challenge, and show that claims chosen
after seeing the challenge can cancel for every challenge. A bad first boundary
does not consume the challenge tape. Exhaustion in round two retains the first
challenge and the second received message.

The machine controls cover stale reads, missed writes, wrong advice, disconnected
PC, incorrect carry, substituted programs, wrong final accumulator/memory,
insufficient bound and non-halting prefixes. Removing word ranges admits the
unwrapped value 8 in an otherwise valid 3-bit addition equation. Modular controls
show that even injective representation of individual words is insufficient:
for `W=8,P=11`, `7+7=3+8*0` is true modulo 11 and false over the integers.

These counterexamples justify explicit range, equation-magnitude and boundary
obligations. They do not establish defects in the unchanged maintained core.
The existing quadratic instance is sufficient for the equality-weighted MLE
client; the earlier cubic experiment remains a distinct degree requirement.

## Validation and reproduction

The four modules contain **57 authored theorems**. A fresh standalone consumer
builds and audits **486 stored declarations, including 236 theorem declarations**
when generated versions are counted. Lean 4.33.1 is pinned. The audit permits
only `propext`, `Classical.choice` and `Quot.sound`; no warnings, `sorry` or new
axioms are admitted. The recorded run checks 325 source inputs with no drift
during the run. Existing dependency objects may be reused; experiment objects
are built afresh in the selected output directory.

```sh
python3 -B formal/consumers/composition/check.py \
  --output /tmp/zkc-formal-composition-replay
```

The output directory must be new. The runner uses the maintained main package,
copies the experiment sources into a separate Lake consumer, checks the transitive
axiom cones and records input/build hashes. It does not treat historical receipts
as proof inputs. Its complete source manifest includes maintained files beyond
the experiment's transitive imports, so its count is specific to the observed
checkout, not a promised permanent library size.

The main [build workflow](../../../.github/workflows/ci.yml) runs this check
and retains its JSON/log outputs.

The `Examples/OpeningReduction` modules in the maintained source tree are not
imported or audited as owned declarations by this consumer.

## Handoff

The current proposal is to retain the execution/refinement core and specialized
quadratic proof, then compare a memory-log encoding of the **same machine and
public statement** against the row-map encoding. Establish deterministic adequacy
before selecting a randomized memory argument or composing it with opening claims.
The field/limb, real-ISA correspondence, PCS and native-layout obligations remain
open.

The concurrent cubic `Examples/OpeningReduction` work overlaps in table and
opening vocabulary but has a different virtual-product/degree path. Inspect both
completed theorem sets before promoting a shared table or opening API; this
package does not silently adopt a still-changing parallel implementation.
The six-instruction accumulator fixture is an execution witness for this model,
not a verified RISC-V program. Selecting and checking an upstream state/observation
map remains part of the larger machine gate.

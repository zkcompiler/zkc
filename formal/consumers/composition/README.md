# Formal composition consumer

This package is an independent Lean consumer of the maintained `formal` library.
The [check](check.py) beside this page copies its modules into a fresh Lake
consumer, builds them against the maintained package and audits their axiom
cones; `just test-lean` runs it.

## Results

| Area | Checked result | Scope |
|---|---|---|
| Multilinear objects | [Multilinear.lean](Multilinear.lean): ordered Boolean-value tables, arbitrary-point interpolation, virtual equality-weighted quadratic evaluation and Boolean-sum laws | A logical reference representation; no prescribed native layout |
| Claim composition | [Claims.lean](Claims.lean): two different-point evaluation claims, batching, arbitrary adaptive Sumcheck rounds, an actual returned point/scalar, and two final object-indexed openings | Reuses maintained quadratic Sumcheck and `ReductionContract.then`; verifier functions do not receive the private tables |
| Source binding | Same module: effectful `rounds_outcome` and `source_reduction` for arbitrary stateful message/react callbacks | The latter consumes the actual round receipt and exact bundle returned by `finish`; typed messages, no new byte codec |
| Probability | `Claims.soundness`: ordinary interactive error at most `(1+2*n)/|F|`, plus honest completeness for every tape | Two fixed equal-dimension input claims; batching precedes adaptive prover selection; subsequent round challenges are independent uniform samples; terminal checker must be sound |
| Machine encoding | [Machine.lean](Machine.lean): wrapping accumulator machine with advice, branching, static-address memory and successful completion; integer local constraints; arbitrary-row decoding; global encoding soundness and completeness | Every admitted program, positive word modulus, memory size and bound; no real ISA mapping or full field AIR |
| Field embedding | `field_add_iff`: modular addition constraint iff integer equation under word ranges, Boolean carry and `P >= 2*W` | This equation only; range enforcement, remaining instructions and the full arithmetization are separate |
| Controls | [Controls.lean](Controls.lean): two-point/two-round receipts, arbitrary honest tapes and adversarial semantic controls | Kernel-checked examples and counterexamples; the fixture opening oracle is not a PCS |

The composed probability theorem has explicit sampling and terminal premises. The initial error vector is fixed before batching; each round message
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
obligations. The quadratic instance covers the equality-weighted MLE client;
[the cubic consumer](../improvement/README.md) has a distinct degree requirement.

## Validation and reproduction

The check reports audited declarations, axiom cones and input hashes for the
current checkout. It permits only `propext`, `Classical.choice` and `Quot.sound`;
no warnings, `sorry` or new axioms are admitted. Dependency objects may be reused;
consumer objects are built in the selected output directory.

```sh
python3 -B formal/consumers/composition/check.py \
  --output /tmp/zkc-formal-composition-replay
```

The output directory must be new. The runner uses the maintained main package,
copies the experiment sources into a separate Lake consumer, checks the transitive
axiom cones and records input/build hashes. Its source manifest includes
maintained files beyond the consumer's transitive imports; reported counts apply
to the tested checkout.

The [workflow](../../../.github/workflows/ci.yml)'s manual `optional` formal-checks scope runs this
check and retains its JSON/log outputs.

The `Examples/OpeningReduction` modules in the maintained source tree are not
imported or audited as owned declarations by this consumer.

Field/limb adequacy, a real-ISA state/observation map, cryptographic PCS soundness
and native layout correspondence remain separate obligations. The accumulator
fixture is a witness for this model, not a verified RISC-V program. See the
[formal questions](../../design/formal-questions.md) for extension boundaries.

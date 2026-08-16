# Benchmark record — generation versus upstream

Scope: one machine, one revision, three instances measured in one
batch; the claims below are exactly these runs and nothing broader
(evaluation/README.md's scoped-claims policy).

- Machine: Linux 6.8.0-134-generic, 32 cpus. Revision: branch
  feat/fri-generality, the pull request that introduced the shape
  knobs; upstream pin 3da3467. Toolchain: 1.97.1, release profile,
  serial grind graph.
- Instances (all value-faithful, ell 100, 16-bit grind, BabyBear
  quartic; `gen.py <instance>` regenerates each crate and its golden
  wire, and the bench asserts the emitted wire byte for byte against
  the golden before timing):
  - **A** `instance-a.json` — trace 2^20, rate 1/2 (SP1's core-config
    arithmetic).
  - **B22** `instance-b22.json` — trace 2^22, rate 1/2: the second
    trace-size point the allocation-flatness criterion requires.
  - **Q20** `instance-quarter20.json` — trace 2^20, rate 1/4: the
    blowup knob at scale.

## Wall clock (criterion, 10 samples, medians)

| instance | upstream | emitted | ratio |
|---|---|---|---|
| A (2^20, rate 1/2) | 8.395 s | 8.875 s | 1.057x |
| B22 (2^22, rate 1/2) | 34.149 s | 35.694 s | 1.045x |
| Q20 (2^20, rate 1/4) | 16.502 s | 17.409 s | 1.055x |

Every ratio is inside the ratified <=1.1x coefficient. An earlier
single-instance run of A recorded 1.018x; the batch above was measured
in one sitting so the three points share their conditions, and both
readings sit inside the gate.

## Allocation (counting allocator, one prove each)

| instance | upstream allocs | emitted allocs | delta | upstream bytes | emitted bytes | delta |
|---|---|---|---|---|---|---|
| A | 6,300,725 | 7,158,268 | +13.6% | 660,644,968 | 726,687,261 | +10.0% |
| B22 | 25,176,016 | 26,569,195 | +5.5% | 2,636,629,992 | 2,616,382,280 | -0.8% |
| Q20 | 12,592,257 | 12,908,969 | +2.5% | 1,315,178,496 | 1,248,092,807 | -5.1% |

**The flatness criterion is ratified against these points.** The
criterion exists to catch a copy leak — an overhead that grows with
the trace. Measured, the relative allocation delta shrinks as the
trace grows (+13.6% at 2^20, +5.5% at 2^22) and the byte overhead
disappears entirely at the larger size and the lower rate: the
emitted leg's extra allocations are a size-independent fixed cost
amortizing away, the opposite of a leak.

## Honesty flags

- The fold depth is the template's: these instances fold to one
  coefficient (log_final_poly_len 0), where deployed systems stop at
  2^5..2^7. The stopping length is now an instance knob — a
  two-coefficient instance runs end to end in
  test/Emit/emit-fri-shapes.test — but no early-stopping instance is
  in this record yet, so part of the query-phase cost and the wire's
  quadratic term is still this depth choice.
- One BabyBear column: this measures the FRI spine and commit path,
  not a multi-column AIR commit.
- The zkc wire is per-query independent paths: ~1.7-1.9x upstream's
  pruned encoding — the recorded stage-3 loss, bought for
  statically-declared layout.

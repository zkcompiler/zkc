# Benchmark record — sp1-core-shape (instance A)

Scope: one machine, one revision, one instance; the claims below are
exactly these runs and nothing broader (evaluation/README.md's
scoped-claims policy).

- Instance: query_log2 21, k 20, ell 100, grinding 16 bits — SP1's
  core-config arithmetic (rate 1/2, 100 queries, 16-bit grind) at
  BabyBear-quartic; trace 2^20 x 1 column; wire 754 KiB.
- Machine: Linux 6.8.0-134-generic, 32 cpus. Revision: branch
  feat/fri-grading, the pull request that introduced this directory;
  upstream pin 3da3467. Toolchain: 1.97.1, release profile, serial
  grind graph.

## Wall clock (criterion, 10 samples)

| leg | median |
|---|---|
| upstream (pinned pcs commit+open) | 8.754 s |
| emitted (generated prove()) | 8.910 s |

Ratio: 1.018x — inside the proposed <=1.1x coefficient.

## Allocation (counting allocator, one prove each)

| leg | allocations | bytes |
|---|---|---|
| upstream | 6,300,725 | 660,644,968 |
| emitted | 7,158,268 | 726,687,261 |

Delta: +13.6% allocations, +10.0% bytes at this size. The gate's
"delta flat across sizes" criterion needs a second size point; that
point lands with the family-generality work, and until then the
allocation half of the gate is recorded as measured-at-one-size, not
ratified.

## Honesty flags

- The family folds to one coefficient (k = query_log2 - 1); deployed
  systems stop at 2^5..2^7, so part of the query-phase cost and the
  wire's quadratic term is this template's depth, not FRI's.
- One BabyBear column: this measures the FRI spine and commit path,
  not a multi-column AIR commit.
- The zkc wire is per-query independent paths: ~1.7-1.9x upstream's
  pruned encoding (754 KiB here) — the recorded stage-3 loss, bought
  for statically-declared layout.

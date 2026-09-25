# AIR kernel benchmark

Two binaries over the same KoalaBear configuration, blowup 8 and 32 queries.

`air_baseline` calls the maintained numerical and oracle kernels directly, with
no compiler in the path. It reports prover and verifier time and the canonical
payload size, without framing, at several trace heights. This is the matched
comparison: the same kernels, the same parameters, a hand-written caller.

`upstream_stark` runs one upstream `p3-uni-stark` proof of a Fibonacci AIR. It
is context, not a matched baseline: that workload has no inter-AIR permutation,
and its batching, transcript and framing differ. Its AIR follows the upstream
release's own Fibonacci test, as [the file](src/bin/upstream_stark.rs) says.

```sh
just bench                                        # both, into build/bench
cargo run --release --bin air_baseline -- 16 128  # explicit trace heights
```

The crate reuses two modules from `crates/zkc-backends` by path so that the
baseline and the product call the same code rather than a copy of it. It links
no proving system of its own and makes no security claim.

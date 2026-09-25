# Benchmarks

These crates measure the compiler and runtime against direct implementations of
the same work. They answer a different question from the tests: a test says
whether behavior is right, a benchmark says what it costs. Raw run records stay
outside the tracked tree. Maintained comparison pages summarize selected past
runs; their numbers apply to the recorded inputs and environment.

```sh
just bench                 # default measurements, into build/bench
just bench /tmp/zkc-bench   # or into a directory you choose
just test-bench            # correctness controls in all separate workspaces
```

| Crate | What it compares |
|---|---|
| [range-native](range-native) | An authored range protocol against a direct Bulletproofs implementation over the same curve, with cross-verification in both directions |
| [air-proof](air-proof) | `air_baseline` calls the same numerical and oracle kernels directly; `upstream_stark` runs one upstream `p3-uni-stark` proof for context. The second is not a matched comparison: it has no inter-AIR permutation and different batching, transcript and framing |
| [application-baselines](application-baselines) | Whole direct implementations of the execution-proof and transaction applications, including a matched route that reimplements the same local algorithms without an upstream range-proof call |

The default command runs the range measurement and the two AIR measurements.
The application campaign has its own [commands](application-baselines/README.md),
[matched comparison](application-baselines/MATCHED.md) and
[contextual comparison](application-baselines/COMPARISON.md). It is not included
by `just bench`.

[`protocol_experiment.py`](protocol_experiment.py) measures the compiler's own
stages on bounded authored sources; the test suite uses it through
`compiler/test/frontend_research.py`.

Each crate pins its own dependencies, so a benchmark can use an upstream library
the product does not depend on. That is the point: an unmatched comparison to a
mature library is worth having, as long as the report says which comparison it is.
These are separate Cargo workspaces, so root `cargo test --workspace` and
`just test` do not run their controls. `just test-bench` explicitly runs
`cargo test --locked --all-features` for each benchmark manifest; it may need
additional dependencies and does not run the measurement commands.

## Reading and recording a measurement

A benchmark reports what it measured and nothing beyond it. Prover and verifier
time, payload bytes and allocation are separate numbers; a change that improves
one can cost another. None of these runs establishes a security property, and a
comparison against an upstream library with different framing is context rather
than an overhead figure.

For a retained comparison, record the source revision and any working-tree
changes, dependency locks, actual tool versions, machine/OS, command, inputs,
repetitions and reported statistic. Identify which stages are included: setup,
compilation, candidate checking, proof construction, verification or execution.
Separate warm/cold preparation, reused keys and caches, and peak resident memory
from logical resource counters.

A matched baseline uses the same algorithms, input sizes, protocol work and
preparation policy. State any difference in transcript, batching, framing,
security parameters or verification behavior. A contextual upstream comparison
can still be useful, but it does not isolate compiler overhead.

Keep failed runs and resource ceilings visible. A timeout is not a timing sample,
and a smaller completed input does not replace a failed larger one. Retain raw
records with the campaign's chosen output directory; publish only the summary
whose provenance and limitations are available. Rerun before claiming that a
historical result describes changed code.

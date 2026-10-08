# Runtime-count nested data

The native mathematical path supports ordered sequences of immutable records,
sums and variable-size data. The [profile](../spec/profiles/compiler/nested-data.md)
owns exact semantics, storage, framing and limits. The
[representation decision](../rationale/nested-sequences.md) explains why this uses
`data.sequence` alongside existing numeric tensors.

## Structure

```text
mathematical sequence operations or authored checked local operations
    → existing recipe lowering and local bindings
    → participant program and generic local loops
    → native sequence storage and existing arithmetic/PCS kernels
    → shared typed codec and independent proof participants
```

This adds one data type and four reusable contracts. It adds no IR stage,
protocol-specific executor, whole-prover callback or new matrix abstraction.
Three total operations lower to checked local kernels; dynamic indexing is
checked local execution from the start. Copying, total mathematics, disclosure,
wire admission and setup authorization remain separate properties.

## Executable clients

- [Batched openings](../../compiler/test/fixtures/mathematical/batched-openings.mlir)
  commits one multilinear table, builds a runtime-length sequence of value/proof
  records with an ordinary local loop, sends it, and validates each actual
  received record. The verifier uses its own points and expected count. Empty
  batches succeed only for an independently empty request; this client alone
  claims nothing about a nonempty opening when no request exists.
- [Ragged matrices](../../compiler/test/fixtures/mathematical/ragged-matrices.mlir)
  receives a sequence of matrices with differing shapes, including zero axes.
  It computes and sums actual bilinear forms with independently supplied row
  and column vectors, then checks the terminal scalar.
- A generated challenge-echo client observes the complete nested matrix frame,
  derives a challenge and checks the returned challenge. Independent upstream
  Merlin/Spongefish calculations check the resulting proof bytes. This client
  checks observation semantics; it is not a cryptographic proof system.
- A standalone matrix exchange checks independently supplied dimensions. It
  exercises the same native frame outside a sequence under the single proof
  policy.

[Compiler controls](../../compiler/test/native_nested_data.py) generate compact
programs and deployments in normal, unsimplified and storage-release modes.
The [runtime client](../../crates/zkc-tools/examples/native_nested_data.rs) executes
counts 0, 1, 3, 8 and 17 through independent producer/validator runs. Mutations
cover omissions, repeated/reordered openings, changed empty matrix shapes,
excessive counts, truncation and trailing bytes. Unused out-of-bounds indexing
still stops in each lowering mode. The native proof host checks cleanup on both
success and failure.

[Backend controls](../../crates/zkc-backends/tests/sequences.rs) cover recursive
formation and permissions, canonical nested frames, retained expanded counts,
immutable append, retained cumulative work and nested PCS setup mismatches.
Existing variant and fixed-array controls remain part of the affected coverage.

## Limits and later work

Append copies the immediate element slice. Element validation also traverses
the expanded sequence on each checked invocation because authorization belongs
to the executing backend. Repeated indexing in a loop therefore has quadratic
validation work under this implementation. The runner also charges each local
frame's inputs and outputs against cumulative retained-value bytes. Repeatedly
carrying or capturing a sequence therefore incurs a quadratic cumulative charge
even when its shared live storage fits. In the batched-openings client, count 128
executes and validates, while count 256 stops with `exhausted:output-bytes` at the
producer's value budget under the default limits. Increasing the sequence-work allowance alone cannot remove
this limit; the proof host caps cumulative value bytes at 256 MiB.

Programmatic backends can configure sequence-kernel work through
`NativeBackend::with_sequence_work_limit`; that allowance and the runner's value
budgets remain independent. Work and allocation ceilings bound this behavior.
Persistent chunks, bulk builders or bufferization need measured clients and an
explicit accounting contract before changing storage. Sequence elements use the
installed default representation. The complete logical type remains available to compiler checks,
wire admission and later analyses.

The native proof host binds public sequence inputs using their exact canonical
native frames; the ragged-matrix client's public row/column sequences exercise
that path. Native proof deployment performs public binding at the Host boundary.

These are composed mechanism clients, not full BP+, Groth16 or zkVM libraries.
Selected [authored transcript](authored-transcripts.md) entry boundaries
compose with this data path. Other curves/providers, broad common-data admission
and native Lean checking require their own contracts. The
[roadmap](../roadmap.md) records further native work.

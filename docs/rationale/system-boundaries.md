# Keep meanings, compilation and execution in separate subsystems

The [architecture](../architecture.md) assigns mathematical meanings and proofs
to Lean, the optimization engine to C++/MLIR, and native execution and backend
integration to Rust. Whole compilation requests and finite artifacts cross
these boundaries; individual optimization steps stay with their compiler state.

## Alternatives

| Alternative | Benefit | Assessment for zkc |
|---|---|---|
| Lean library/checking + MLIR/C++ engine + separate Rust tools/runtime | Reusable proofs, rich optimization structure, native integration and independent deployment | Recommended; incurs real schema, decoder and correspondence work |
| Whole compiler in Lean | Direct proved algorithms and fewer independently implemented semantic algorithms | Good for checking and small passes; rebuilding the full optimization ecosystem is not presently justified |
| Rust compiler with MLIR as a subordinate lowering tool | One native implementation language for most product code | Viable if needed optimizations stay in a small Rust IR; otherwise duplicates graph/analysis infrastructure and adds binding maintenance |
| MLIR/C++ as the sole compiler and product implementation | Fewer zkc language boundaries and direct access to MLIR; a standalone C++ runtime remains possible | Strong alternative for C++ consumers/kernels. Selected Rust backends still need adapters and Rust builds; assess ownership and native-proof costs independently |
| Library planner without MLIR | Small integration surface and direct use of established algorithms | Retain as a useful product route and fair baseline; choose it where structured compiler work adds no demonstrated value |

The chosen separation permits independent builds, a small formal foundation and
native deployment without a full compiler installation. Its cost is explicit
source binding, schema/decoder work and correspondence at every boundary.
Sharing a process or programming language would not remove those obligations.

Use proved transformations and source-relative result checking where each is
appropriate. Keeping the optimizer outside the trusted proof core permits
search strategies to change without treating search output as a theorem.
This choice is architectural; it is not a measured comparison of all listed
implementations.

## Reopen when

A real consumer demonstrates that crossing a subsystem boundary dominates its
cost or duplicates required state, or that a simpler library planner supplies
the needed transformations without the compiler infrastructure. Reassess that
boundary with the same semantic contract and client workload.

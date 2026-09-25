# Structured local algorithms

This extension covers collection construction/access, local conditionals, and
finite local loops. Protocol-level dynamic choices and unbounded `while` are
separate future work.

## Design

The mathematical source already has branches and fixed finite state-carrying
iteration (`Zkc.Source.Program` and `Region`). Runtime bounds select a member of
that finite family after checked admission; this is not an unbounded loop
constructor or a proof of raw-adapter adequacy. Native local definitions have previously
been straight-line primitive/helper calls. This work connects structured local
control to that executable path rather than introducing a protocol-specific
algorithm interpreter.

Authoring conveniences elaborate into typed operations and isolated regions.
Vector literals reuse existing empty/append operations; indexing selects the
appropriate typed access. Vectors remain logical collections, not SIMD vectors
or a promise about allocation. `let mut` denotes a source binding whose later
values become SSA values and region results; it does not introduce references,
aliasing, or arbitrary mutable storage. Evaluation is ordered and occurs once.

Local `if` executes exactly one branch. Both branches must form correctly and
return the same ordered types. Local `for i in lower..upper` reads index bounds
once, increments by one, and does no work when upper <= lower. Its explicit
carried state supplies the result, including the initial state for zero trips.
Runtime counts are finite input-selected values with checked limits, not an
unbounded continuation. Exceeding a runtime limit is an explicit failure, not
silent truncation or modular wraparound.

Portable local regions use these records:

```
["if", site, condition, captures, then_body, else_body, outputs]
["for", site, induction, lower, upper, carried, captures, body, outputs]
["yield", values]
```

The frontend computes captures and state merges for ordinary source syntax. The
canonical printer may show explicit capture/carry/yield structure. Portable
source and native verification retain that structure. Protocol `loop` remains a
distinct construct with role-owned ports and a fixed public count.

Affine captures are consumed once upon branch entry; each branch checks its own
uses. A loop's invariant captures must be non-affine; affine state travels in
carried ports. Neither branch speculation nor cloning a captured RNG is an
allowed convenience. Failure, ordered effects and actual occurrence paths remain
observable under the selected execution profile.

High-level FFT, MSM and polynomial operations remain available. A general loop
is an algorithm-authoring tool, not a reason to prematurely expand those
operations. Helper expansion must recurse into regions while preserving their
control, rather than unrolling loops or executing both branches.

## Native representation

`pir.local_if`, `pir.local_for` and `pir.local_yield` retain single-block,
isolated typed regions. MLIR's `RegionBranchOpInterface` exposes entry, branch,
backedge and result mappings; there are no purity or speculation traits. Explicit
capture block arguments keep lifetime and affine admission local to each region.
The loop yield forwards invariants to make the backedge mapping visible to MLIR.

A dedicated representation was selected over immediately emitting `scf.for`:
zkc's index is unsigned 64-bit at the logical stage and a `plan.data` wrapper at
the physical stage. Bounds, failure, retained-value charges and resource custody
must survive lowering. An early SCF conversion would need an additional carrier
and failure translation without helping the current library-call execution path.
This leaves SCF available for a later kernel lowering with an explicit contract.

The [owning profile](../spec/profiles/compiler/local-control.md) defines the
records, formation, limits and observations. Local algorithms expand helpers
inside the regions; participant projection preserves them; physical planning
selects bindings and inserts conversions inside the appropriate region. Storage
release analyzes each isolated block. Rust executes the structure and Lean
independently admits and interprets it. Static-schedule analyses explicitly refuse
unsupported control rather than treating it as straight-line code.

## Basis

- [MLIR SCF](https://mlir.llvm.org/docs/Dialects/SCFDialect/) supplies structured
  region, yield and carried-state conventions. Logical nominal index types and
  zkc failure/resource contracts must still be respected at any lowering.
- [Rust loop expressions](https://doc.rust-lang.org/reference/expressions/loop-expr.html)
  supply familiar authoring notation, not Rust's ownership or iterator runtime.
- Existing zkc typed finite control, affine-use checks and effect observations
  define the semantic boundary. A native lowering is tested/checked against
  those definitions; having the same operation names is not a refinement proof.

## Deferred

Global dynamic branches require a chosen participant, agreement/communication,
branch-sensitive claims and transcript treatment. Unbounded iteration requires
termination/divergence and possibly probabilistic semantics. Neither is admitted
by this local syntax. [Products and structs](../language/data.md) and
[variants](../language/components.md#local-alternatives-and-finite-traversal) are
separate supported data forms. References, closures, iterator traits,
break/continue and kernel parallelization remain outside this local-control profile.

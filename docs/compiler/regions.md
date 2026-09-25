# Compact computation regions

A compact region carries a shared continuation across Lean, actual MLIR and
checked Rust execution. The
[compact region profile](../spec/profiles/compiler/direct-plan.md#compact-region-profile)
owns its formation, meaning and format.

## Why this boundary needed work

`PIR.Proc.bind` already supplied sequential composition. `Source.Program.seq`
proved the right substitution meaning, but represented a continuation by
inserting it at every returning leaf. Repeated branching can therefore grow the
source tree exponentially before an optimization even runs. A correct denotation
alone does not give a useful compiler representation.

`Source.Region.bind body next` stores both pieces once. The body may contain
branches, loops, stopped calls or nested bindings. Its result becomes a typed
input of the shared suffix. For example:

```text
let selected = region {
  if condition then return add(x, y)
               else return add(x, x)
}
record(selected)
return selected
```

The record occurs once in the representation and only after a normal return.
If either chosen path stops, its actual effects survive and the record is
skipped. A body can produce a Boolean from two field inputs without requiring
an arbitrary Boolean initial value.

This is an additional structured source carrier over the same PIR execution
model. It is not a new cryptographic abstraction level. Interactive meaning,
construction interpretation, domain operations and physical realization remain
separate architecture decisions. The existing terminal `choose` remains useful
inside a computation region; `bind` supplies its enclosing result and successor.

## Alternatives and theoretical basis

| Choice | Assessment for this boundary |
|---|---|
| Continue substituting into source trees | Correct semantics; unacceptable continuation growth for this workload |
| Direct computation binding | Selected: typed result, explicit captures, one suffix, existing complete-result sequencing |
| Result-producing `scf.if` | Suitable after explicit outcome/control lowering; ordinary yielded values alone do not represent stopped post-state and propagation |
| General CFG/block arguments or named join points | Greater irregular sharing and control freedom; requires reachability, dominance, loop/termination and certificate design beyond this structured need |
| Encode binding as a one-iteration loop | Requires a needless initial value of the result sort and obscures the distinction between computation and iteration |

[Maurer, Ariola, Downen and Peyton Jones, *Compiling without continuations*,
PLDI 2017](https://www.microsoft.com/en-us/research/publication/compiling-without-continuations/)
studies explicit join points in a direct-style IR. It motivates retaining shared
control structure. Our binding is a restricted structured join; this work does
not implement that paper's calculus or inherit its correctness proofs.

[MLIR SCF](https://mlir.llvm.org/docs/Dialects/SCFDialect/) supplies result-bearing
structured control. We retain logical stops until a lowering accounts for them.
MLIR's [effects rationale](https://mlir.llvm.org/docs/Rationale/SideEffectsAndSpeculation/)
distinguishes memory effects, speculation and non-local control, and does not
claim complete modeling of the last. Generic purity annotations cannot establish
zkc stop propagation. The present control operations remain conservative and
do not advertise an unimplemented `RegionBranchOpInterface`.

Intrinsic typing and renaming provide the binding proof. Algebraic effect
sequencing gives stopped execution and composition. Compositional bounds avoid
expansion during analysis. These are established tools applied here; the new
carrier is engineering progress, not a proposed new PL calculus.

## Implemented connection and proofs

| Layer | Implementation and guarantee |
|---|---|
| Typed source | `Zkc.Source.Region`: generic sorts/operations, explicit binding; `denote_rename`, `denote_flatten`, `run_flatten`, `run_bind_stopped` |
| Formation | `Zkc.Source.RegionEncoding`: complete structural elaboration, typed erasure, `Region.elaborate_erase` |
| Semantic cost | `Zkc.Source.RegionBounds`: `Region.denote_within` under all-argument operation-call bounds; no native cost claim |
| Artifact | `Zkc.Compiler.RegionArtifact`: consumer-bound metadata, actual-body direct checking, `Checked.correct` for any decoding of that candidate |
| MLIR | `pir.bind` / `plan.bind`: isolated body, explicit capture operands/block arguments, flow and value results; actual export reconstructs references |
| Execution | Rust decodes and executes the compact body directly, joins resource bounds, and preserves stopped body effects without executing its suffix |
| Correspondence | Independent Lean execution plus generated native comparisons, independent expectations and malformed/changed-candidate controls |

`Program.toRegion` preserves the meaning of existing finite source.
`Region.flatten` maps back through proved source sequencing. **The decoder,
checker and runtime never flatten.** The old carrier continues to support its
existing clients and proofs; its finite wire profile is unchanged. Metadata
policy is shared explicitly rather than duplicating its admission conditions.

This adds a carrier API that existing source-specific analyses do not yet accept.
They need structural extensions and proofs; a semantic bridge alone does not
make those analyses available on compact input. Do not grow independent policy
implementations in the two carriers. Extend common analysis contracts and retain
this bridge as a regression check when their representations converge.

The native compiler still performs direct logical lowering. Generic CSE can
change pure operations inside a binding and export a well-formed result, but the
installed direct checker refuses it against the retained original source.
Structural optimization support and certified optimization remain distinct.

## Measurements and limitations

A family of `n` successive decisions has `6n + 1` region nodes, proved for all
`n` in `Tests.Regions.decisions_size`. The corresponding tree recurrence is
`T(0) = 1`, `T(n+1) = 3 + 2T(n)`, hence `4·2ⁿ - 3`. At 14 decisions this is
85 versus 65,533 nodes. This compares representations of the same repeated
branching computation, not protocols or third-party implementations.

The measured 14-decision source uses 2,185 bytes, its exported plan 2,006 bytes,
and actual MLIR 28,447 bytes. At 64 decisions these become 9,135, 8,006 and
373,769 bytes. Source/plan formatting differs, so bytes are reported separately.
The larger tree counts are calculated from the recurrence, not allocated trees.

The importer passes every in-scope value as a capture, so capture operand lists
grow quadratically across long chains even though source control nodes grow
linearly; pruning to live-in values is the available repair. The compact form
carries no end-to-end linear-time or runtime claim. Native capacity estimates are
conservative and inspect dormant paths; logical stopping does not guarantee a
bounded native invocation will start.

One result may have any language sort, including a product supplied by its
library; the current native table vocabulary has only its implemented sorts.
General multi-result regions, cyclic CFGs, higher-order functions, source-module
calls and arbitrary protocol libraries are not delivered by this binding alone.

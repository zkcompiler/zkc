# Numerical units and schedules

Closed numerical computations use named `builtin.module` owners, standard
`func.func` entries and the existing mathematical dialects. The
`exec.computation` unit attribute requests zkc's closed-computation profile.
The `kernel` dialect retains only the ordered invocation from Local control.
This boundary introduces no runtime instruction, frame, artifact format or
alternative evaluator.

## Unit and call

```mlir
module @square attributes {exec.computation} {
  func.func @evaluate(%x: !algebra.field<"bls12-381.fr">)
      -> !algebra.field<"bls12-381.fr"> {
    %r = "algebra.field_multiply"(%x, %x)
      : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
        -> !algebra.field<"bls12-381.fr">
    func.return %r : !algebra.field<"bls12-381.fr">
  }
}
```

The standard module provides an isolated symbol table. An admitted computation
unit has exactly one public, defined standard
function. Private standard functions and `data.domain` declarations supply its
dependencies. References resolve within that owner; implicit captures, external
functions, recursive closures and arbitrary operations are refused. Admission
checks every retained definition, including unused ones.

Ordinary MLIR verification checks the module, functions, symbol uses and marker
placement; the marker must be a unit attribute on a named module. It does not
establish closed-computation admission. The enclosing Protocol stage calls
`verifyComputationUnit` after nested MLIR invariants have passed, for every
nested module, including unreferenced modules and modules missing the marker.
Standalone clients must perform both checks. Only the symbol name and profile
marker are admitted module attributes. Entry lookup and profile classification
are inspection helpers, not admission evidence.

The entry has total, non-affine native data ports. Its explicit
`data.preconditions` remain part of its mathematical contract; public visibility
selects the entry and does not assert that its premises hold universally. A scoped
`exec.compute` invocation must discharge those premises using its actual data
operands. Closing or normalizing a helper retains the conditions verbatim.
The retiring `kernel.call` path admits only unconditional entries. Formal polynomials and quotient elements may occur internally but cannot cross
the entry boundary. Private helper conditions are checked against their actual
arguments. The shared `TotalClosure` analysis checks the mathematical vocabulary,
dependency closure, bounded access and polynomial observations. An installed
backend implementation alone does not establish these properties.

`kernel.call @square::@evaluate(%x) {site = "square"}` supplies exact positional
input and result types. It appears inside a `local.func` or its structured Local
control. It is an ordered invocation: it cannot be speculated, merged or moved
across guards, effects or stopping operations merely because its body denotes
total mathematics. The qualified reference must resolve to the public entry of
a sibling unit. The call implements MLIR's standard `CallOpInterface` and
`SymbolUserOpInterface`; these interfaces grant no purity or speculation.
Optional argument and result attribute arrays contain only empty dictionaries.
When realization changes the call's ports, it preserves these arrays' presence
and adjusts their lengths to match the new interface.

## Formation and preservation

Two compiler boundaries use the same unit formation mechanism:

- Preparation replaces a `local.realize` request with its existing Local wrapper
  and an owned numerical closure.
- Participant demand lowering extracts total mathematics at an ordered action
  cut, retaining captures, escaped results and the existing Local invocation.

Guards and partial operations remain in Local control. Relation formulas do not
become executable roots. The compiler checks copied helper and domain bodies,
actual SSA operands and returned aliases. Units retain original helper bodies
and polynomial DAGs until numerical realization; an origin label is not evidence of
equivalence. Preparation and projection freeze and compare the complete units
alongside their Local wrappers.

The `protocol`, `participant` and `exec` profiles may retain logical units.
Physical admission and executable publication refuse every residual unit or
call, including unused definitions. The compiler's internal logical admission
view uses numerical signatures only; it cannot be encoded as `zkc.program/0`.

## Realization

`zkc-lower-kernels` transactionally realizes calls in their existing Local
positions and removes the units. Physical planning uses the same proposal and
independent reader while retaining the original Kernel-bearing subject. Its
checked plan owns the selected Local candidate and the binding, port and
conversion decisions for that candidate. Materialization applies those decisions
without rerunning numerical selection. The [physical plan](../../compiler/representation.md#checked-physical-decisions)
checks both correspondence edges before publishing the physical result.
The same late transaction handles retained pointwise maps and mixed map/Kernel
subjects. Each occurrence has bounded legal alternatives; a missing implementation,
unavailable conversion or attributable program-capacity refusal can advance that
occurrence before publication. Semantic mismatches and malformed bindings remain
terminal. Optional attempts keep cumulative work accounts and a separate reserve
for required construction. The final reader checks the original source and actual
selected body; a record of the selection is not semantic evidence.

Normalization and native recipes use
the existing bounded mechanisms and independent readers; they do not define a
second mathematical semantics. An optional call `policy` records the selected
`[finiteBulk, vectorReductionFusion, collectFoldFusion]` compile-time choices.
Omitted policy uses the lowering request's defaults.

Normalization produces another profiled standard module and retains checked polynomial
origins in that owned subject. Recipe conversion consumes its standard entry
and uses a private builtin module for ordinary MLIR conversion. The completed
Local function and bindings use the existing executable Protocol owner for
closed admission before the body is inserted at the ordered call. This
temporary storage is not another public IR stage. Source helpers resolve
against the numerical owner, while generated bindings belong to the executable
candidate. The independent numerical reader compares the original entry with
actual output and never invokes the recipe producer.

Structural analysis retains numerical call occurrences independently of their
selection policy. An enclosing finite optimization must still honor every
retained call's replacement restrictions. Analysis views borrow immutable source
operations and must be rebuilt after body or interface edits.

Numerical instruction sites derive deterministically from the ordered call site
and normalized operation position. Authored Local sites and protocol event
identities are preserved. No per-operation provenance list is stored in a call.

Inside a total closure, normalization folds static dimensions and exact array
projections and removes unused total arithmetic. Finite computations are not
removed by this cleanup. The independent helper-meaning reader checks the
simplified return coordinates. This is a mathematical realization choice before
executable accounting, not permission to remove an existing Local instruction.

Each authored invocation expands at its ordered position. Compiler-generated
calculation wrappers may expose additional concrete ports to retain numerical
results across action cuts. Only independently identified polynomial-generated
work can reuse an exact earlier producer in the same participant block. A
generated projection may also forward the exact element of a retained concrete
pack. The subsequent port-sharing step keeps concrete operations distinct and
ordered, including unused work in its normalized input. Independent readers
check normalization, actual port wiring, original
return coordinates and unchanged surrounding guards and effects.

Expansion adds no Local frame,
entry/return charge or destruction point. Installed implementation restrictions,
native failure behavior and the [canonical Local accounting](functions.md)
contract remain applicable. Compile-time work is bounded independently of
runtime capacity. Total mathematical meaning does not promise execution under
arbitrary work or memory limits.

The unit remains the logical source. Numerical realization produces a private
scheduled function before its selected Local realization and physical
conversions. The physical plan also checks optional binding-lifetime decisions
before publication. [Native numerical calls](../runtime/numerical.md) use checked
typed storage views and private destinations inside existing installed handlers.
This does not turn nominal scheduled values into addressable buffers.
Compiler buffer lowering and target-specific vectorization remain separate work.
Participant scheduling, transcript state, transport and capability authority
remain with their existing owners.

## Numerical loop schedule

The private schedule uses standard `func.func` and sequential `scf.for` with
nominal field and container values. It is compiler IR, consumed before executable
publication; the VM continues to execute Local control and bound operations.
The schedule must pass ordinary MLIR verification as well as its closed-profile
checks. Local control verifies its isolated frames and logical primitives verify
their bound ports. Bindings resolve within the nearest lexical symbol table;
an enclosing module cannot supply a missing schedule binding. The containing
executable profile owns placement and vocabulary restrictions.

A scheduled loop has unsigned signless `i64` control, unit stride, an explicit
state prefix and invariant captures. Exact `ui64`/`i64` representation bridges
preserve all index bits. No host-sized `index` conversion is permitted.
Zero-trip Local admission checks retain the original lower/upper resource checks
before the SCF loop, including empty and reversed intervals. The closed profile
requires explicit captures, unchanged invariant backedges and unused invariant
result suffixes. Free casts, altered strides and implicit captures refuse.

The finite reader checks the original domain, callbacks and state against the
actual schedule. A separate structural reader checks the actual scheduled
function against the emitted Local function. Neither reader regenerates an
expected candidate. The Local consumer preserves nominal types, operands,
bindings, sites and state order. General SCF canonicalization is not an admitted
transformation of this profile without its own preservation check.

## Collect–fold composition

`--fuse-collect-fold` enables checked streaming composition of an unfiltered total
field-vector or field-sequence collect and its adjacent total fold. It defaults
to false and is independent of finite bulk selection and vector reduction fusion.

The collected vector must be used only by that fold. The consumer domain is
exactly its elements or indices. Element callbacks cannot observe the whole
vector; indexed callbacks may read it only at their current position through
bounded access. Duplicate argument/capture aliases are checked at every use.
The composition retains the producer's complete domain admission and enumeration,
then executes its body followed by the fold step for each item. Original seeds
and ordered state coordinates are preserved, including mixed or empty state
tuples; no associativity law is required.

Shared or escaping collections, filtering, nested finite callback computations
and unsupported whole-vector observations retain the materialized path.
The independent reader compares both original callbacks with the actual composed
traversal. A fusion label or synthetic source fold is not correspondence evidence.
Fixed implementation restrictions and ordered call boundaries remain applicable.

Removing a collection can reduce storage and traversal work, but scalar streaming
may be slower than native bulk kernels. This is an explicit compilation choice
with the usual sufficient-capacity mathematical contract; it does not promise
identical resource exhaustion or faster execution for every workload.

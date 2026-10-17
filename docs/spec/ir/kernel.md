# Logical numerical units

The `kernel` dialect owns closed numerical computations between mathematical
SSA and executable Local operations. It reuses standard `func.func` and the
existing mathematical dialects. It introduces no runtime instruction, frame,
artifact format or alternative evaluator.

## Unit and call

```mlir
kernel.module @square {
  func.func @evaluate(%x: !algebra.field<"bls12-381.fr">)
      -> !algebra.field<"bls12-381.fr"> {
    %r = "algebra.field_multiply"(%x, %x)
      : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
        -> !algebra.field<"bls12-381.fr">
    func.return %r : !algebra.field<"bls12-381.fr">
  }
}
```

A unit is an isolated symbol table with exactly one public, defined standard
function. Private standard functions and `data.domain` declarations supply its
dependencies. References resolve within that owner; implicit captures, external
functions, recursive closures and arbitrary operations are refused. Admission
checks every retained definition, including unused ones.

The entry has total, non-affine native data ports and must discharge its own
mathematical premises. Formal polynomials may occur internally but cannot cross
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
positions and removes the units. Physical selection invokes this checked edge
before constructing a representation plan. Normalization and native recipes use
the existing bounded mechanisms and independent readers; they do not define a
second mathematical semantics. An optional call `policy` records the selected
`[finiteBulk, vectorReductionFusion]` compile-time choices. Omitted policy uses
the lowering request's defaults.

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

The current unit is logical. Explicit loop schedules, buffer layouts and
cross-operation numerical planning are later refinements of this boundary.
Participant scheduling, transcript state, transport and capability authority
remain with their existing owners.

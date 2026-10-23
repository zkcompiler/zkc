# Numerical compilation and storage ownership

The [native numerical contract](../spec/runtime/numerical.md) keeps nominal
field operations and immutable collection inputs through checked realization.
The compiler emits typed numerical expressions or existing provider calls.
Standard MLIR structured operations are not a replacement for this executable
boundary. Their useful prospective role is inside a native provider's code
generation, where the provider can establish a machine representation and
honor the same storage contract.

## What standard representations offer

[Linalg](https://mlir.llvm.org/docs/Dialects/Linalg/) separates iteration maps
and parallel or reduction dimensions from the scalar calculation. Tensor values
allow producer-consumer fusion before storage selection. Vector operations and
Affine loops then support target-specific execution. These are useful reusable
mechanisms, including for modular arithmetic when the scalar calculation is
lowered correctly. They need not own the source domain to provide that value.

An elementwise modular product followed by an addition can use two
`linalg.generic` operations. Elementwise fusion combines their scalar bodies
into one traversal. A scalar dot product can use a reduction iterator. Neither
requires an owned replacement for the Linalg dialect. Explicit modular scalar
operations make the arithmetic available to standard lowering; custom scalar
operations preserve the domain longer but still need their own machine
lowering and vectorization support.

zkc already retains the corresponding scalar expression, scalar broadcasts,
ordered row domain and map/reduction choice. Its current realization fuses a
complete scalar expression and selected map/reduction pairs, with an independent
reader and provider execution. Importing that expression into Linalg and reading
it back into the same native expression would add a conversion and another
reader without removing the current execution or domain implementation.
Cross-map fusion is a possible additional capability, but cannot erase an
unused input's shape check or reorder reached failures merely because its
scalar body is unused.

## Machine arithmetic is an additional boundary

An unsigned coefficient is not automatically a machine implementation of its
field. For example, `65536 * 65536 mod 65537` is one, whereas multiplying in
32 bits before taking the remainder gives zero. Widening both operands to
64 bits first handles this example. General accumulation still needs an
explicit range bound or intermediate reduction. Signed remainder, centered
representatives, Montgomery coordinates and binary extension fields require
their own interpretations.

zkc's eight installed field families include prime, extension and binary
fields. Replacing their scalar operations with ordinary integer arithmetic
would require maintained lowerings for each representation and a connection
to their provider encodings. Keeping custom field operations in a structured
loop avoids that replacement but does not itself supply efficient native code.
Existing provider arithmetic remains the selected implementation at this
boundary; a new backend must justify its additional domain implementations
through a concrete target and reusable workloads.

## Bufferization does not grant input ownership

[One-Shot Bufferization](https://mlir.llvm.org/docs/Bufferization/) selects
storage for tensor programs using aliasing and read-after-write analysis.
Function arguments are writable by default. A direct native caller that
passes the same immutable buffer into two arguments cannot rely on a tensor
caller's copy insertion. Even a last use in the compiled function does not
permit changing a zkc input that another published value retains.

Read-only argument handling can force a private allocation and preserve
aliasing inputs. That makes standard bufferization usable under a suitable
adapter; it does not replace the adapter. The
[`restrict` promise](https://mlir.llvm.org/docs/Dialects/BufferizationOps/#bufferizationto_tensor-bufferizationtotensorop)
on separate buffer-to-tensor conversions must not be asserted for two
possibly aliasing inputs. A provider can instead expose an admitted function
boundary, coalesce known aliases, or use a conversion whose alias conditions
it actually establishes.

Storage selection also does not establish numerical admission. A generated
`memref.alloc` has no knowledge of complete-tuple output allowance, initialized
private destinations, scratch reservation, staging/final overlap or work
charges. One-Shot Bufferization itself does not insert deallocations. Its
ownership-based deallocation pipeline solves a distinct lifetime problem.
Any generated native provider must connect these mechanisms to the owning
runtime scope, including failure without partial publication.

## Selected boundary and remaining cost

Retain typed source mathematics, checked numerical expressions and managed
provider calls as the common compiler/runtime route. This keeps independent
program admission possible without loading generated machine code and shares
the field implementations across maps, reductions and polynomial consumers.
It also means maintaining zkc's specialized realization and fusion logic;
standard loop optimizations do not automatically apply to the native calls.

A native provider backend can use Linalg, Tensor, Vector, MemRef and Affine
directly when it has an actual code consumer. That backend needs an explicit
code-admission or trusted-build boundary, exact field representations, immutable
input handling, managed destinations, checked dimensions and whole-workload
comparisons against the existing provider. The reason to introduce it is a
reusable execution target or transformation capability. Merely reproducing a
scalar loop or reducing an operation count does not offset a second execution
and arithmetic implementation.

This choice does not constrain structured quotient arithmetic to scalar native
calls. Its [HEIR integration](quotient-rings.md) exposes a different missing
capability: compound ring calculations and transform placement, checked before
lowering to managed operations. Numerical storage ownership is shared by both
paths, while each retains the mathematical representation its consumers need.

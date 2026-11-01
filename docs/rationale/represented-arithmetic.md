# Represented arithmetic ownership

zkc owns the small canonical [Residue boundary](../spec/ir/residues.md) and uses
standard MLIR for machine arithmetic and private shaped computation. Algebra
and Poly retain mathematical identities; Runtime and target selection own
[physical numerical plans](../spec/runtime/numerical-plans.md). This preserves
one owner for each meaning without making provider storage a mathematical type.

## Standard transformations and independent admission

A canonical residue modulo `q` has a bounded unsigned representative. Addition
and subtraction need a carry bit; multiplication needs twice the operand width.
Reducing a wrapped machine product does not generally recover the mathematical
product, including for a prime just below `2^64`. The owned boundary fixes these
laws before lowering to Arith. It also distinguishes unsigned projection from
strict byte decoding, and centered lifts from ordinary unsigned lifts.

Static pointwise candidates use Linalg vectorization and One-Shot Bufferization.
Their success is a proposal, not evidence of zkc bounds, custody or allocation
behavior. An independent reader checks actual Vector/MemRef accesses, poison
isolation, initialization, aliases and release, and reconstructs the scalar
expression. This admits a deliberately closed subset. General aliasing, masked
memory and arbitrary effects need additional readers before becoming available.

The checked expression, lane bound and independently admitted scratch assignment
reach the installed CPU provider. This retains packed resident arithmetic and
the existing fallible numerical scope. A generic word-bytecode interpreter would
add another execution language; AOT would add a deployment and object-code
boundary. Neither is needed to consume these plans. Conversely, generating a
word candidate and then executing an unrelated earlier expression would lose the
optimization and its correspondence argument.

A provider value relation remains explicit. A canonical integer, a Montgomery
limb array and an extension coordinate vector are not interchangeable storage.
Complete nominal domain and basis information survive until provider selection;
non-prime and extension cases can select their existing opaque implementations.
These are supported representations of current mathematics, not compatibility
readers for the retired executable Ring parameter.

## Why not depend on HEIR here?

[HEIR ModArith](https://heir.dev/docs/dialects/modarith/) and
[Polynomial](https://heir.dev/docs/dialects/polynomial/) are useful design and
experimental references. Their broader polynomial/RNS ecosystem is attractive
when its transformations are the intended consumer. Importing only their core
while maintaining zkc-specific lowering and independent interpretation would
retain much of the adapter cost while foregoing most of that benefit.

The explored source was
[`e18c51f3f92a1100cdbce528494a00a30fb49f0f`](https://github.com/google/heir/tree/e18c51f3f92a1100cdbce528494a00a30fb49f0f).
An isolated core build against MLIR 23 required three assembly-format setting
edits; this compatibility cost alone did not decide the architecture. The full
scalar conversion also names HEIR encryption-related conversion utilities.
zkc still needs its own exact full-width/composite-modulus, codec, non-two-adic
quotient, refusal and resource contracts, regardless of the imported operations.

The bounded adapter experiment obtained 976 folded results agreeing with an
independent integer oracle; eight composite products remained unfolded. A
separate full-width polynomial-addition case exposed an intermediate-width
mismatch in that pinned path. This limits an unrestricted adapter, not HEIR as
a whole. It is not an end-to-end HEIR runtime or NTT conformance result.

The production decision is therefore an owned narrow boundary and upstream
MLIR transformations, with no optional HEIR execution route. Reconsider importing
HEIR when a concrete consumer needs enough upstream polynomial/RNS optimization
to justify maintaining its adapter and independently checked semantics.

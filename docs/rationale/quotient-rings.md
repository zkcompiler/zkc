# Structured quotient arithmetic reuses external compiler machinery

The selected direction is to reuse HEIR's Polynomial and ModArith dialects for
structured lattice arithmetic, with a separate checked native RNS realization for exact signed-digit
module products. zkc retains the source contract, independent transformation readers
and runtime admission. The [numerical execution decision](numerical-execution.md)
explains why structured selection currently targets managed native providers. The [roadmap](../roadmap.md#compile-structured-quotient-arithmetic)
orders integration; [status](../status.md) distinguishes this direction from
the installed coefficient operations.

The [quotient-ring contract](../spec/domains/quotient-rings.md) keeps exact
canonical coefficients and ring parameters at a checked boundary. A source
`Polynomial<Q,N>` prevents accidental mixing of moduli or degrees; native
handlers independently check raw operands. This boundary remains useful when
the compiler changes how a compound arithmetic region executes.

## Preserve structure across operations

Lattice computations include ring dot products, module matrix-vector products,
repeated public matrices, and exact integer observations. Transforming every
product independently loses opportunities to share forward transforms and keep
an accumulated result in evaluation form until its final inverse transform.
For a four-term ring dot product, separate NTT products use eight forward and
four inverse transforms; a compound implementation needs eight forward and one
inverse transform under the same supported ring profile.

A handwritten native compound kernel can obtain the same saving. The reason
to retain compiler structure is to apply such choices across source programs
without defining a new opaque kernel for every combination. Prepared native
arithmetic remains a useful realization and reference. Its existence does not
remove the need to represent the computation that selects and composes it.

This is a concrete interface requirement in lattice applications.
[ML-DSA verification](https://doi.org/10.6028/NIST.FIPS.204) generates its public
matrix in a specified NTT representation and combines module products before
returning to coefficients. The benefit to zkc therefore extends beyond the
cost of a single Falcon multiplication.

## Reuse the arithmetic vocabulary

[HEIR's Polynomial dialect](https://heir.dev/docs/dialects/polynomial/) already
represents polynomial quotient rings and coefficient/evaluation forms. Its
transform placement, modular arithmetic and RNS machinery provide reusable
compiler infrastructure. The
[HEIR design](https://arxiv.org/abs/2508.11095) separates these low-level
mathematical layers from encryption schemes and ciphertext management.

The selected boundary uses admitted HEIR operations directly inside compiler
arithmetic regions. The source facade and enclosing zkc contracts provide the
boundary; a second dialect mirroring every external operation would duplicate
maintenance. An owned operation is appropriate when it adds a distinct meaning,
such as an exact integer observation or a representation unsupported upstream.
The source-level quotient type in `algebra` records backend-independent
mathematical values and total projection from arbitrary finite coefficient
sequences. It has no evaluation-form type, NTT operation or placement solver.
This small source vocabulary keeps partial canonical validation distinct from
total mathematics, and supports general moduli even outside the qualified HEIR
transform profile. HEIR remains the selected owner of structured representation
changes inside an admitted arithmetic region.
Integration must retain compound regions rather than lower each product into
an isolated external function.

Existing zkc field-polynomial expressions, multilinear extensions and evaluation
tables keep their separate meanings. A finite quotient-ring value is not an
ordinary formal polynomial, and a quotient ring need not be a field. Reusing
HEIR for this domain does not select its FHE stack as the protocol compiler.

## Own the interpretation and check the result

External types and verifiers do not establish correspondence with a zkc source
operation. Each accepted profile needs an explicit interpretation of ring
parameters, coefficient order, transform coordinates, integer lifts and storage.
The existing [candidate discipline](mathematical-ir.md) retains an immutable
source while a separate reader inspects the actual transformed candidate.
HEIR requires new reader coverage within that discipline.

For a primitive `2n`-th root `r`, one possible transform convention is
`A[k] = sum_j a[j] r^((2k+1)j)`, with natural `k` order and inverse-transform
attribute `r^-1`. A helper using bit-reversed coordinates or a different inverse
convention needs an explicit conversion. An evaluation-form label alone cannot
establish that two arrays use the same roots, ordering or normalization.
Constant folding, canonicalization and generated execution must agree on the
same interpretation.

The supported transform profile also matters. For `q=3329,n=256`, a scalar
512th primitive root does not exist in the coefficient field. ML-KEM uses
quadratic components, as specified in
[FIPS 203, section 4.3](https://doi.org/10.6028/NIST.FIPS.203). It needs a different
representation and product law from the full scalar NTT used for Falcon and
ML-DSA. The current coefficient implementation can still evaluate that ring.

RNS reconstruction introduces another obligation. If each output coefficient
is an integer sum of `k` negacyclic products of degree `n`, with input magnitudes
bounded by `A` and `B`, the sufficient condition `P > 2*k*n*A*B` for the odd CRT
product `P` makes centered reconstruction exact. Without that bound, converting
between residue bases can return the correct centered residue of a different
integer. Norms, digit decomposition and byte encodings must observe the intended
integer or coefficient value. They cannot be moved into evaluation coordinates
using ring homomorphism laws alone.

Runtime integration also preserves storage width, normalization, failure order,
preparation, aliasing and charged scratch. Transform minimization does not by
itself minimize latency or retained memory. Compiler work limits and the
runtime's resource contract remain independent obligations.

## Why selective adoption

| Choice | Benefit | Remaining responsibility |
|---|---|---|
| Native kernels alone | Simple execution ownership and reusable optimized code | Cross-operation structure becomes manually maintained compound kernels |
| Owned structured arithmetic IR and external libraries | Full control of the representation | Rebuild quotient types, transform planning and conversion infrastructure |
| HEIR arithmetic IR with a zkc interpretation | Reuse structured operations and qualified transformations | Maintain accepted profiles, independent readers, version compatibility and runtime integration |
| Whole HEIR FHE stack | Support encrypted-computation compilation | Adds scheme semantics that do not implement zkc's protocol responsibilities |

Selective arithmetic reuse fits the intended protocol families. HEIR is a
replaceable implementation choice; retaining structured arithmetic is the
architectural requirement. Source contracts and coefficient fallback keep that
choice replaceable without discarding the compiler's mathematical subject.

The dependency needs an owning pin, a compatible LLVM/MLIR toolchain, selected
build targets and a regression corpus for the admitted semantics. Registering a
dialect does not admit every upstream pass. Compiler-side reuse also does not
require a HEIR runtime library: lowering can produce generated code or calls to
qualified native arithmetic implementations.

Native integration can proceed independently of the Lean redesign. Formal work
can later interpret the retained source and selected realization under the new
Lean owners. Native tests and transformation readers remain distinct from that
formal correspondence and from protocol security proofs.

## Exact module products and RNS admission

The [prepared matrix contract](../spec/domains/quotient-matrices.md) separates
protocol modulus, compute-prime basis, integer bounds and retained storage.
The representation has private immutable ownership: input transforms may be
reused, but a caller cannot relabel coordinates with a different basis or bound.
This uses the existing Polynomial domain for a local provider value; no owned
RNS dialect mirrors HEIR. A general module-expression source vocabulary should
be added when an actual compiler transformation consumes it, with source-relative
comparison and the same integer-lift obligations.

Chunking an accumulation before the centered CRT lift is established prior art,
including the [Akita overflow correction](https://github.com/LayerZero-Labs/akita/commit/0a36011).
The contribution here is the checked source/native contract, private retained
representation, actual digit-bound validation and managed execution. The bound
and algorithm are not claimed as new cryptography. Compute primes permit exact
work over protocol rings without a full scalar NTT, including even and composite
moduli. Direct transforms in a supported protocol ring remain a useful cheaper
alternative; RNS is not the default replacement for every ring multiplication.

HEIR's [RNS conversion](https://heir.dev/docs/dialects/rns/) remains outside the
admitted compiler profile. The selected revision's conversion supports odd
bases, whereas the native matrix contract also permits even protocol moduli.
Its ModArith storage additionally needs a spare sign bit. Qualification with
128-bit storage and target modulus `2^64-59` matched independent centered CRT
results for one and two compute primes. The three-prime boundary control
`x=(P-1)/2` disagreed with independent integer reduction after generated LLVM
execution. Correcting the isolated Horner multiplier in the emitted arithmetic
restored agreement for all seven signed boundary controls.

The inspected [mixed-radix builder at the pinned revision](https://github.com/google/heir/blob/v2026.10.01/lib/Dialect/RNS/IR/RNSOps.cpp)
uses the current limb modulus as the inner Horner multiplier, where the preceding
basis modulus is required. This makes the prior coefficient contribution vanish
modulo the current limb. The finding is specific to that revision and profile;
it is not a conclusion about every HEIR arithmetic transformation. Existing
Polynomial/ModArith region integration remains admitted under its independent
reader. A future RNS admission must repair and qualify conversion, define exact
integer capacity and even-target behavior, and compare the actual candidate.
Registering upstream RNS operations in the development optimizer grants none
of those obligations automatically.

Prepared RNS execution also has fixed costs. Exploratory comparisons include
preparation, repeated calls, retained storage and scratch, with ordinary
schoolbook and manually shared protocol-modulus NTT controls. The direct NTT
control is cheaper where its root profile applies; tiny chunked matrices can
favor schoolbook arithmetic. Source-to-CLI measurements include preparation,
serialization and process startup, so they are kept separate from kernel costs.
No universal speedup or constant-time implementation is claimed.

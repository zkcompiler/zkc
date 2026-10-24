# Native numerical calls

This contract connects checked Kernel realization and physical bindings to
synchronous native numerical handlers. It uses the existing `plan.apply` and
`zkc.program/0` operation path; there is no separate numerical executable format.

## Types and storage

The compiler owns exact nominal and structural port types, representation
selection and explicit conversions. Physical validation checks the actual ports
and retained Kernel/Local correspondence. The VM independently admits the
physical program and links independently advertised backend signatures.

A representation identity does not specify a foreign memory ABI. A numerical
adapter must interpret the exact selected representation and actual operands.
Typed field elements preserve their nominal field, including extension and
binary-field arithmetic. Equal size does not permit reinterpretation between
fields, or between a field element and its encoded coordinates.

Native dense inputs are borrowed immutable slices. A row-major view admits
`rows * columns == elements.len()` with checked arithmetic; zero dimensions
remain distinct from unknown dimensions. Transposition changes indexing without
copying storage. Multilinear tables retain their owning library's storage order:
first-coordinate folding pairs adjacent LSB elements and corresponding MSB
half-table elements. Storage constructors preserve that order.

Repeated aliases are allowed. Input borrows end when the synchronous call
returns; published results own their backing references. A physical release,
last use or reference count grants no permission to overwrite published inputs.
Sparse matrices, diagonal views, keys and capabilities do not acquire dense
access through this contract. Their existing adapters and explicit conversions
retain their own obligations.

## Invocation and completion

Installation resolves immutable bindings and signatures. Operand shapes,
attributes and capacity are checked at the reached call, after the existing VM
and native admission. Numerical construction receives policy and the fresh-result
allowance, without resource stores, randomness, transcript state or interpreter
environments. It does not create an additional frame or instruction charge.

Results are built in initialized private destinations. The adapter fixes their
extents before allocation. Scoped typed buffers expose mutable slices; provider
builders initialize their reserved final storage without growing it. Freezing consumes
the destination through its owning representation constructor. Native output
validation and the VM still check the complete returned tuple and its retention.
Results become observable only after successful completion; a failed operation
returns no partial result tuple. Failure does not roll back prior effects or
refund spent work. All internal work must finish before returning.

## Managed construction

`zkc-kernels::numerical` provides the VM-independent scope. Native adapters
select its limits from invocation policy and map failures before publishing
concrete values. The scope reserves:

- The aggregate conservative charge of fresh results against the invocation's
  output allowance and the backend's complete-tuple `max_value_bytes` ceiling.
- Simultaneously live scratch and destination staging storage, plus reserved
  final representation storage, against `Policy::max_numerical_bytes`.
- A conservative evaluation-admission score against `Policy::max_numerical_work`.

Scope reservations precede managed allocation and use checked arithmetic.
Staging and final storage are both counted while freezing can overlap them.
An explicit `output_owned` reservation instead counts one buffer when its
trusted constructor adopts the supplied Vec without growth, reallocation or
a second element buffer, including on error and unwind. Its output and memory
charge is the maximum of the typed payload and the caller's complete retained
bound. This contract is audited at each adapter; it is not inferred from an
arbitrary Rust type. Native flat dense values use immutable `Buffer<T>` owners
that adopt initialized vectors without moving their elements. Their retained
charge includes spare capacity; clones and mathematical views retain the same
complete owner. Ordinary output paths keep their conservative staging-plus-final
reservation even when publication adopts the vector. Explicit `output_owned`
paths retain their single-buffer contract.
Finished results remain charged until the scope ends. Scratch and abandoned
destinations release their reservations when dropped. Scratch exposes only
borrowed slices and cannot be frozen through the result API. Accepted work
charges are not refunded.

Provider builders couple their storage and memory-only reservation in one
destination owner. Abandonment destroys storage before releasing its charge;
freezing retains the charge through the trusted constructor and, on success,
until call end. Their existing shape, output and complete-tuple checks remain
with Native. Optional scaling scratch shares the destination's live memory
allowance; it cannot independently consume a second call allowance.

The defaults are 256 MiB of managed memory and 2^26 numerical work units per
call. These native policy fields are included in preparation compatibility;
reusing a cached computation cannot bypass a changed policy. They are distinct
from the CLI capacity record and existing VM instruction, iteration, logical-byte
and retained-value ledgers. Existing shape and output refusal precedence is
preserved before the new numerical exhaustion checks.

Managed memory bounds requested typed payload storage and conservative final
representation storage. They do not bound allocator overhead, total process
memory or allocations hidden inside provider libraries. Freezing and native
arithmetic remain trusted adapter code; an infallible provider allocation can
still encounter process allocation failure. Work units are not elapsed time,
bit-operation complexity or a constant-time guarantee.

## Implemented consumers

The scoped path covers dense vector addition, subtraction, multiplication,
scaling, filling, geometric sequences, sums, products, dot products, matrix-vector
products and splitting over all installed field families. It also covers
ordinary and fixed-vector dot products (including resident scalar storage),
`poly.fold` for BLS LSB/MSB tables and
`poly.opening_quotient` for the
[registered residue fields](../domains/values.md#registered-residue-fields).
The quotient uses scoped denominator scratch and its unpublished output for
batch-inversion prefixes. Other operations keep their existing provider checks;
DFT preparation and hidden provider scratch are not certified by this scope.

Arkworks curve vector scaling reserves optional projective, Z-coordinate and
inversion-prefix scratch, in chunks of at most 256 points. The existing output
checks and allocation precede scratch admission.
Insufficient scratch allowance or a failed optional allocation selects the
existing per-point path before writing results; these calls acquire no new
numerical work or mandatory memory floor. Both paths retain affine-base scalar
multiplication and private complete-output publication. Dalek scaling keeps its
existing constant-time provider calls and does not use this scratch.

`blst/resident/*` and `halo2curves-axiom/resident/*` alternatives operate on
selected BLS12-381 and BN254 scalar, G1 and G2 storage, respectively.
Canonical bridges and subgroup checks occur in reached
`representation.convert` calls. Linking checks the conversion endpoints;
arithmetic reuses those admitted signatures without parsing them again.
Imports adopt their provider buffers; bulk exports to Arkworks keep staging
and final storage reserved together. There are no implicit operand imports.

Resident shared-scalar and elementwise vector scaling call the typed bulk
kernels, borrowing the original scalar storage and filling one reserved point
buffer. BLST splits independent multiplications; Halo additionally uses optional
bounded projective/affine scratch for batch normalization. Insufficient scratch
or a failed optional allocation selects Direct before numerical writes. Both
paths keep the existing work charges and mandatory destination bounds.

Resident field/vector arithmetic uses the shared dense adapter. Resident curve
arithmetic uses the shared curve adapter; it does not inherit the admission
weights of the earlier bridge-per-operation implementation. Both providers
admit explicit MSM and pairing workspace. Their work scores are:

| Provider | MSM, `n` points | Pairing check, `n` pairs |
|---|---|---|
| BLST | `256*n + 1` | `8192*(n + 1)` |
| Halo2curves | `32*n + (n + 2*b + w)*q + 1` for `n > 0`; zero for empty input | `182*n + 8192` for `n > 0`; zero for empty input |

For Halo2curves MSM, `w` is 1 when `n < 4`, 3 when `4 <= n < 32`,
and `ceil(ln(n))` otherwise; `b = 2^(w-1)` and `q = floor(256/w) + 1`.
The input length must fit `u32`. The score bounds scalar-byte scanning and the
pinned serial Pippenger schedule independently of scalar values. Pairing counts
91 preparation and 91 Miller coefficient steps per pair, plus the fixed
final-exponentiation allowance. For one point, the Halo2curves MSM score is
1061; for one pair, its pairing score is 8374.

Conversion admits `4096 * max(elements, 1) + 1` units. These are conservative
admission scores, not runtime predictions. Input aliases remain immutable and any refusal
publishes no result. Provider-internal allocation failure can still abort the
process. Every invocation checks current implementation permission before
charging work, including a retained prepared handle after idle policy changes.
Selection does not establish a constant-time guarantee; MSM is variable-time.
Canonical ports and Contracts defaults remain Arkworks; the compiler's
[Target preferences](../../compiler/representation.md#resident-providers) may
select resident G2 scaling and pairing checks with explicit conversions.

`poly.coset_extend` also uses this scope on BN254 Fr and the registered residue
fields. Shape and domain checks precede numerical admission;
the whole input/output vectors must fit the element policy. Work admission
counts both transform lengths, base coordinates, complete extension shift
arithmetic and construction. Adapter-owned transform payloads are reserved
before allocation without allocating duplicate accounting buffers. The private
output includes its staging/final overlap. Provider twiddle caches, hidden
provider scratch and allocator overhead remain outside that reservation.
Every column must succeed before publication, including when a later column
fails a shrinking-degree check. The operation has its own resource profile;
the library's use of it does not promise the exhaustion point of separate calls.

`poly.coset_evaluate_batch` uses this scope on the same fields for exact
column-major coefficient blocks. Let `w` be the number of columns, `h` the
coefficient height, `n` the output height, `I=w*h`, `O=w*n`, `d` the extension
degree over the installed base field and `e=sizeof(F)`. Retained output is
`R=256+O*e` bytes. Zero width costs one work unit and 256 managed bytes, and
does not inspect unused domains. For positive width, the conservative score is
`16*d*O*log2(n) + (I+O)*(8*d*d+16) + (w+1)*4096*d*d`.
Coefficient height zero is admitted without taking its logarithm.

Typed operands and checked exact extents precede structural domain admission
(size, installed element bound, nonzero shift), whole-vector and fresh-output
admission, then discarded-tail validation. Numerical work is admitted next,
followed by explicit workspace and destination reservations. Domain powers,
provider setup and transform arithmetic begin only after these checks.
All size, byte and work calculations use checked arithmetic. A failed call
publishes no result. Existing operations keep their own resource floors.

Plonky3 scales a row-major matrix by powers of the full extension-valued shift,
sharing each power across columns, and calls the pinned algebra batch DFT.
The matrix reserves `O*e` bytes; staging/final output overlap gives a managed
bound of `256+3*O*e`. BN254 reuses one capacity-preserving `n`-element vector for
all columns and the existing Arkworks FFT, for `256+(2*O+n)*e` managed bytes.
Provider-internal conversions, transform scratch, twiddle caches and allocator
overhead remain outside managed storage. No value-dependent preparation survives
the call. Source quotient splitting supplies its own interpolation, capacity
check and coefficient padding, then calls this authored operation once; this
does not assert identical exhaustion behavior to the former sequence of calls.

`poly.coset_evaluate_at` uses the same scoped output ownership on those
fields. Its exact column-major shape and domain are checked before numerical
admission. One result per column is constructed privately; point-dependent
weights and adapter-owned inversion scratch are call-local and charged before
allocation. Plonky3 uses two managed arrays; BN254 uses one managed weight array
and Arkworks' serial inversion routine. Arkworks' internal prefix products remain
provider-owned and outside the managed reservation.
The work bound covers domain traversal, inversion setup and all column products,
including extension arithmetic. On-domain evaluation returns the selected row;
it is a mathematical case of the operation, not a constant-time guarantee.
The operation does not retain values or weights across invocations.

`poly.opening_quotient_sum` constructs one weighted sum of selected off-domain
column quotients on those same fields. All descriptors, including zero
weights, must pass column and pole checks before result construction. Complete
input vectors pass element and byte admission first. Domain construction and the
ordered column/pole scan then precede numerical work admission; a zero work
allowance does not prevent this bounded validation arithmetic. An invalid
descriptor takes precedence over output, workspace or execution-work exhaustion.
The scan costs `O(m log n)` field operations for `m` admitted descriptors and
height `n`. The adapter borrows selected columns and owns one private result plus
two height-sized arrays, reused across terms. Both providers account for prefix
storage explicitly; there is no per-term vector publication. Consecutive equal
points reuse the inverse vector in that workspace. A changed point replaces it;
nonconsecutive repeats are recomputed, without sorting or retaining a point map.
Reuse depends on point equality; descriptor order and conservative work admission
are unchanged. Empty descriptors copy initial after shape and input admission
without interpreting an unused domain. Managed storage includes result staging/final overlap:
`4*n*sizeof(F)+256` bytes for nonempty descriptors,
`2*n*sizeof(F)+256` otherwise. Work uses bounded native-field operations and scalar
loop steps, as for the single-opening operation; it is not elapsed time or a
constant-time claim. This authored operation has its own admission profile.

## Pointwise expressions

The compiler-generated `numerical.map`, `numerical.sum` and
`numerical.product` contracts execute a pure field expression over a row domain.
They use ordinary installed bindings and operation parameters:

| Part | Contract |
|---|---|
| Binding arguments | `[F, M]`: an exact installed field and an ASCII `0`/`1` operand mask |
| Inputs | Row count (`index`), followed by one `field<F>` for each `0` and one `vector<F>` for each `1` |
| Parameters | One canonical `zkc.ring/0` expression, at most 4096 decoded UTF-8 bytes |
| Expression | Exactly `M.length` inputs, one output, every node in `F`; constants, input, addition, multiplication and negation |
| Result | `vector<F>` for map; `field<F>` for sum or product |
| Installation | `arkworks/numerical.*`, `dalek/numerical.*` or `plonky3/numerical.*`, according to the owning field provider |

The mask has at most 1023 positions. Leading zeros are significant; the empty
mask permits a constant expression. The row count is at most 1,048,576. Every
vector operand must have exactly that length, including operands unused by the
expression. Scalars are broadcast mathematically without allocating vectors.
Empty maps return an empty vector; empty sums and products return zero and one.
An authored reduction seed is combined outside the operation.

All eight installed field families have native consumers. Cross-field embedding
is outside this expression contract. Natural constants denote prime-subfield
elements; general extension elements arrive through typed operands. Binary-field
constants retain the Ring carrier's restrictions: only the prime-subfield
naturals `0` and `1` are accepted; `2` and hexadecimal bit patterns are refused.

Program admission checks the static expression and binding independently of
native installation. Direct native calls repeat the checks when reached. The
backend retains immutable typed preparation only for equal declarations, exact
physical signatures and attributes. Shapes, live values and policy remain
invocation checks. Bounded parsing, canonicalization and immutable preparation,
including typed constants and the retained preparation key, happen before
per-evaluation scope admission. A cold call may therefore populate its preparation
slot before a work refusal, including with zero work allowance. The numerical
work policy does not provide a pre-execution admission guarantee for this
preceding preparation.

Preparation has separate bounds: a 4096-byte decoded UTF-8 body, 1023 operand
slots and 1 MiB of conservatively charged immutable metadata per prepared call.
The metadata charge includes copied keys, Ring inputs/nodes/facts/roots, typed
constants, the positional mask and invariant/varying node schedules. Parsing
scratch is bounded by the carrier size. These bounds are separate from managed
row scratch and result construction;
they do not bound allocator overhead or process RSS. No Host relation asset or
process-wide expression cache is used.

For each evaluation, the work admission score is
`W = 8B + 2I + 2N + 1 + R(3N + 3)`, where `B` is the body byte length, `I` is the
operand slot count, `N` is the Ring node count and `R` is the row count. The fixed
setup surcharge `8B + 2I + 2N + 1` is identical for cold and cached calls, including
empty domains. This is a conservative evaluation-admission score, not a meter of
preparation already performed. After live shape and output checks, the scope
admits this score before allocating managed scratch or results and evaluating
rows. Cache warmth does not reduce the required allowance.

The prepared plan classifies row dependence from the positional mask. Scalar-only
subexpressions are evaluated from the current invocation's captures once, when
the first row is reached; an empty domain evaluates no arithmetic. Only varying
nodes run for each later row. Captured values never enter immutable preparation.
The conservative work score remains unchanged by this optimization.

Evaluation may process contiguous row chunks in a node-major scratch slab.
Chunk width is an invocation detail, bounded by the remaining managed-memory
allowance. The minimum admission requirement remains one element per Ring node,
typed operand views, map staging when present, and the conservative result charge.
A tighter allowance reduces chunk width down to one row. All scratch remains
charged; this preserves policy admission, not allocator success or process RSS.
Only the remaining rows are evaluated in the final chunk. Sum and product consume
roots in row order, and results are published only after the complete call.

Expression nodes and ordinary dense vector operations share destination-slice
arithmetic. Each field uses its provider-declared packing for native element
slices, preserving every extension coordinate. Scalar tails and fields whose
provider declares scalar packing use the same field operations. Packing introduces
no new binding, representation, work discount or permission to reorder effects.

Kernel schedules continue to lower to Local control and installed operations.
These consumers do not implement arbitrary scheduled control or establish a
native/source correspondence theorem. MLIR memory and bufferization interfaces
apply to lowerings that provide concrete storage and alias semantics.

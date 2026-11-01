# Structured native mathematics

This profile extends [mathematical protocols](protocols.md) with
formal polynomial and quotient SSA and static field data. Mathematical meaning belongs to
[tables and polynomials](../domains/polynomials.md). It retains
the profiles `protocol → participant → exec → physical`; an analysis or
lowering does not introduce another editable mathematical graph.

## Types and total operations

`!poly.polynomial<"F", n>` denotes the formal ring `F[X0,...,X(n-1)]`.
`F` is an installed field and `0 ≤ n ≤ 32`. Zero arity denotes `F`.
This is a compile-time mathematical value. Transparent, acyclic private helpers
may produce it; protocol inputs, outputs, messages and executable bindings may
not contain it. Helper preparation exposes constructors before degree analysis.
It is distinct from the existing normalized concrete `!poly.univariate` object.

`!poly.quotient<q,n>` denotes `(Z/qZ)[X]/(X^n+1)`, for `2 <= q <= 2^64-1`
and `1 <= n <= 2^64-1`. It is a total mathematical value with exact ring identity;
composite moduli and zero divisors are allowed. It has no executable port,
message or wire encoding. Transparent mathematical helpers may carry it.
`poly.quotient_project` reduces an arbitrary finite `!data.indices` polynomial
into the ring; `poly.quotient_coefficients` observes exactly `n` canonical
ascending coefficients. `poly.quotient_add`, `poly.quotient_subtract` and
`poly.quotient_multiply` require identical modulus and degree on all ports.
Multiplication is negacyclic convolution, not coordinate-wise multiplication.
No field inversion, cancellation or FFT capability follows from this type.
The [quotient contract](../domains/quotient-rings.md) defines these meanings.

Concrete field arrays use `!data.field_array<"F", N>`, with exact nominal
field identity and `0 ≤ N ≤ 1048576`. Logical encoding remains
`field_array<F,N>`; field and length survive physical selection. The type has
rank one and an intrinsic extent of `N`. A field vector with proven length `N`
retains `!data.field_vector<"F">` and cannot substitute for a field array.
Builtin tensors have no compatibility alias. Source `[T; N]` and
`!data.fixed_vector<T, N>` remain distinct. A field array does not denote a
polynomial until an operation supplies that interpretation.

The following flat operations are total on their verified types:

| Operation | Signature and judgment |
|---|---|
| `algebra.group_identity` | No operands; identity of the nominal result group with scalar action |
| `data.index_less` | Two `ui64` indices to their strict order comparison |
| `data.index_power_of_two` | Indices `(n,r)` to `n = 2^r` over naturals; false for every `r >= 64` on the native index domain |
| `data.dim` on a field vector, axis zero | Field vector to its length as an index |
| `algebra.constant` | Typed `#algebra.literal<F, value>` to a scalar in exactly `F` |
| `algebra.field_subtract` | Two scalars in one field to their difference |
| `data.array_from_elements` | Exactly `N` ordered operands of field `F` to `!data.field_array<"F", N>`; empty construction is allowed |
| `data.array_at` | Static array and constant `index` attribute; `0 ≤ index < N` |
| `poly.constant` | Scalar to a polynomial of the declared arity |
| `poly.from_coefficients` | Positive array to univariate, ascending powers; trailing zeros allowed |
| `poly.mle` | Length `2^n` array to arity `n`, high-bit Boolean order |
| `poly.add`, `poly.multiply` | Same field and arity; formal sum/product |
| `poly.fix` | Polynomial plus ordered scalar prefix; removes exactly those leading axes |
| `poly.sum_suffix` | Sum over `count` trailing Boolean axes; removes them |
| `poly.evaluate` | Polynomial plus exactly `n` ordered scalars to scalar |
| `poly.coefficients` | Univariate to positive static array; known degree bound must be below output length |
| `poly.evaluate_domain` | Univariate to array matching ordered `points` |
| `poly.interpolate` | Array matching ordered `points` to their univariate interpolant |
| `poly.fix_table` | Power-of-two table and prefix to the remaining power-of-two table |

`algebra.multilinear_restrict_prefix` takes two dynamic field vectors and
returns a vector of the same nominal field. It is total, with the
[vector restriction meaning](../domains/polynomials.md#total-vector-prefix-restriction),
and has no attributes. Both operands are ordered mathematical dependencies.
Its checked execution recipe uses `exec.apply`
bound to `multilinear.restrict_prefix<F>`, with exactly two vector inputs,
one vector output and no parameters. The independent recipe reader checks
that exact binding, field and operand order. Native execution separately
admits resource limits before allocating scratch and publishing the result.
The existing fixed-arity polynomial restriction requires a static shape, and
checked `vector.split` refuses odd or empty inputs. Current finite Math
operations lack total dynamic halving and truncating access, so this operation
uses one direct vector recipe within the existing lowering checker.

Every operand and result of a mathematical polynomial operation uses one field.
An empty fixing prefix and a zero suffix count are identities. Fixing all axes
produces arity zero, or a length-one table. Zero-length data arrays are admitted,
but polynomial constructors and coefficient observations require positive arrays.
Coefficients pad with zeros to their static output length. Array packing retains
the `ArrayFromElements` mathematical identity and depends on every operand in
order. Its executable recipe uses vector construction followed by
`field_array.from_vector`; static access uses `field_array.at`. This changes
neither the native carrier nor the field-array codec below. The structural
collection interface grants no polynomial interpretation or operation admission.

`points` contains 1–64 distinct canonical field literal strings. Its order is
observable. There is no implied FFT, root or coset capability: a coset client
supplies its actual ordered points. Interpolation returns degree less than the
point count. Evaluation followed by interpolation does not preserve an
arbitrary higher-degree formal polynomial.

Per-axis degree upper bounds are derived from SSA: constant zero, MLE one,
coefficient/interpolation length minus one, addition maximum, multiplication
sum, and axis deletion for fixing/summation. Overflow and missing required
bounds refuse. Required coefficient bounds are checked even for unused
observations, before simplification. Bounds are conservative under cancellation.

These operations also occur inside [structured iteration](iteration.md).
Nested degree requirements are checked before dead-code elimination. Generic
tensor casts/generation and opaque polynomial callbacks have no admission grant.
[Polynomial recipes](polynomials.md) cover runtime arity through explicit
realizations; they do not change the static polynomial type.

### Formation diagnostics

`algebra.constant` requires a native field-literal attribute and the exact same
nominal field on its result. A mismatched result uses `mathematical-formation`;
malformed literal presentations or values use `field-literal`. Static
`data.array_at` extraction uses `mathematical-formation`. Polynomial operation
and domain formation use `polynomial-formation`. Evaluation and interpolation
points are ordered native field literals with distinct values and the same field
as their polynomial. These native operations do not parse decimal strings.

Pure index and field constants implement `ConstantLike`, exact attribute folding,
and dialect constant materialization. The field attribute implements MLIR's
`TypedAttr` interface with its nominal field type. These hooks expose immutable
values to generic MLIR analysis; they do not authorize algebraic reassociation or
rewrites of reached execution calls. External source and byte literal spellings
are translated at their respective boundaries.

## Realization

### Structured tensor computations

Retained scalar maps and their selected sum reductions pass through a private
standard `func.func` with `tensor` and `linalg.generic` operations. Rowwise
arguments have type `tensor<?x!algebra.field<"F">>`; scalar arguments remain
exact Algebra field values. Every input coordinate remains in the function
signature, including unused columns. The execution boundary checks all rowwise
lengths in source order before evaluating the computation. Equal lengths are a
domain premise of this internal tensor profile, never inferred from the tensor
type or from the inputs actually read by the scalar formula.

A map has one parallel iterator, identity maps for rowwise inputs and output,
and empty maps for scalar broadcasts. Its `tensor.empty` extent comes from the
first rowwise input. The scalar region cannot read the uninitialized destination.
A sum has one reduction iterator and a rank-zero destination initialized to the
exact field zero. Its region adds each term to the accumulator; the function
extracts and returns that same reduction result. Empty input therefore yields
an empty map or a zero sum. These are exact field laws, not floating-point
reassociation or machine-overflow assumptions.

The canonical sum candidate retains a pointwise map followed by a reduction.
Upstream elementwise fusion combines their actual regions, then scalar-region
CSE/DCE shares repeated work. The independent reader admits both the original
tensor graph and the fused form, reconstructs a scalar formula from actual
pointwise SSA edges, and compares it with the original scalar DAG by ordered
labelled bisimulation. Every operation, including unused work, is admitted.
A bounded structural check rejects nested packets before recursive MLIR
verification. It checks nominal fields, literals, input coordinates, iteration
kinds, indexing maps, seeds, captures and the actual returned value. Unknown
operations/attributes, nonmatching maps, extra work outside the admitted packet,
and changed formulas refuse with `structured-computation`. The reader does not
rerun the producer, fusion or CSE, and approval does not survive candidate mutation.

`Analysis/StructuredComputation.h` owns complete packet interpretation and
source comparison in the IR component. Reading without a source establishes
profile admission only; consumption checks correspondence and returns the actual
scalar interpretation from that same read. No producer or optimizer is linked
into this semantic owner.

The production lane adapter uses this profile for row-bearing native maps and
selected sums. Products use its pointwise map stage while retaining the native
product aggregate. Row-free fills retain a direct scalar payload because this
profile requires a tensor input to supply an extent; identity maps can borrow an
existing input after their ordered guards. Explicit vector selection bypasses
the tensor profile. These are distinct admitted cases, not recovery after a
failed semantic comparison.

The adapter charges closure construction and structured work to the enclosing
lane budget before building a candidate. A capacity decline emits nothing and
may select an already admitted vector/ordered alternative; a failed profile or
source comparison is terminal. No alternative replenishes optional work.

The executable adapter reads the admitted candidate's scalar body into the
existing typed native map/reduction handlers. The original-to-executable
numerical reader still checks the actual final payload and all length guards.
The private tensor program grants no general Tensor/Linalg admission, buffer
ownership, vectorized machine representation, native correspondence theorem,
or permission to change runtime refusal behavior.

This is a checked compilation of total mathematics into a selected executable
program. The observation relation requires equal returned mathematical values
and preserves the surrounding ordered action/capture boundary. Each emitted
program retains actual runtime work, scratch, fresh-output and retained-storage
checks; no result is published after a stop. Fusion and scalar sharing need not
preserve the budget threshold of a different emitted program. They grant
neither same-artifact metering changes nor permission to classify malformed
domain/codec inputs as resource exhaustion. Completeness is conditional on the
selected program's resources; exact metering equivalence and native execution
correspondence remain separate obligations.
`data.index_power_of_two` uses a total word circuit:
`(n & (n - 1 mod 2^64)) == 0 && logical_shift_right(n,r) == 1`.
A nonzero word passes the first condition exactly when it has one set bit;
the second selects that bit's exponent and excludes zero. Shift counts at
least 64 return zero, so unrepresentable exponents remain false. The circuit
uses two constants and six operations from the existing total word, equality
and Boolean contracts. The independent recipe reader checks every constant,
contract and SSA edge. Vector length and index comparison reuse their existing
executable contracts. These Math additions do not extend the executable
operation catalogue.

The nullary `algebra.group_identity : !algebra.group<"G">` lowers to
`exec.apply` bound to `curve.identity<G>`. The producer reads
`G` from the result type; the independent recipe checker verifies the exact
contract, nominal group, empty operands/parameters and result. Provider selection
then applies ordinary group representation restrictions. See the
[group identity laws](../domains/values.md#group-identity).

`zkc-eliminate-polynomials` operates on a verified participant candidate. It
realizes observations through field arithmetic, static extraction and packing,
then removes formal polynomial values. It caches actual SSA inputs and prefixes.
Coefficient multiplication uses convolution, evaluation uses Horner or
multilinear folding, Boolean summation enumerates the selected suffix, and
interpolation uses compile-time Lagrange coefficients in a supported prime
field. Interpolation refuses unsupported nondecimal/extension-field constants.

The elimination budget is 100000 work units across the module, with recursion
depth 128. Degree analysis has its own 100000-operation block limit.
The later math-lowering verifier has a separate 1000000-work limit; satisfying
one bound does not promise the next stage will succeed.
Domain formation and executable expansion have separate limits. In particular,
64-point interpolation is well formed but exceeds the current scalar
elimination budget even in isolation. The 64-point formation ceiling is not
an execution guarantee. The same limit applies when coefficient extraction
uses interpolation internally; an admitted degree bound is not a promise that
coefficients fit the executable budget. Improving this algorithm does not
require a change to the mathematical meaning of interpolation.
All transformations build and verify a candidate before replacing their input.

`zkc-fix-polynomial-factors` is optional. It distributes prefix substitution
through sums/products, combines nested prefixes, preserves shared factors,
and exposes smaller MLE tables with `poly.fix_table`. Its limits are 10000 work
units per participant block and depth 128. It validates required bounds before removing dead fixing
operations. The native compiler enables it only with `fixPolynomialFactors`
or CLI `--fix-polynomial-factors`.

`zkc-lower-math` forms owned [Computation units](computation.md) under the demand-based
scoped outlining contract. Checked numerical realization supplies executable recipes.
Static extraction becomes `field_array.at<F,N>` with its index attribute;
packing uses existing vector construction followed by
`field_array.from_vector<F,N>`. The latter checks exact length.
The executable access contract can fail for an out-of-bounds attribute;
mathematical static access has already ruled that out. These bound kernels are
not assigned mathematical purity.

Packing is a reference implementation: repeated immutable vector append can
copy quadratically. This profile promises bounded executable meaning, not a
scalable polynomial backend or preservation of resource failures under every
mathematical rewrite.

## Native array boundary

The default BLS array representation is
`field_array<bls12-381.fr,N>@arkworks.field-array/0`. Native also installs
`field_array<bls12-381.fr,N>@blst/field-array[blst/fr]`, whose dense storage owns
resident blst scalars. The complete child layout and extent are checked
independently in C++ and Rust. Existing array operations specialize one complete
container layout; construction and access preserve its scalar layout. There is
no implicit aggregate conversion. Other fields can have mathematical formation
without an installed Native array provider.

`field_array.get<F,N>(array, position)` is ordinary checked execution with a
dynamic `index` operand and no attributes. It returns the element of `F` at
`position` when `position < N`, otherwise refusing with `field-array-index`.
Length zero has no valid access, and large indices cannot wrap into range.
`field_array.at<F,N>` remains the separate checked kernel with a static index
attribute used by mathematical lowering. Neither executable kernel establishes
total mathematical access; the mathematical static operation has its own bound
premise. `field_array.from_vector<F,N>` checks exact length before construction.

Arrays use immutable shared storage. Their generic custody declaration is
`PrivateImmutable` (copy and drop); codec support is an independent property.
This classification does not assert secrecy. The mathematical profile permits
role sharing through the native array wire codec. `fixed_vector` has its own
custody and codec rules.

One array exchange is one frame: the six bytes `ZKCV`, byte `0`, tag `64` (`0x40`),
followed by exactly `N` canonical 32-byte little-endian BLS scalar encodings.
The length is obtained from the expected complete type, not from an untrusted
length prefix. Total frame size is `6 + 32*N`.

Decoding checks exact width, header/tag, policy and canonical field elements.
Retained-value accounting is `32*N + 1280` bytes. The decoder preflights
`64*N + 1280` bytes for the temporary vector and resulting shared allocation.
Encoding enforces the same element-count limit and charges the retained value;
it does not allocate the decoder's temporary vector. Equal resource policies can
therefore admit encoding and refuse decoding. Successful encoding does not
promise that a receiver has enough memory. The decoder also enforces element
and wire limits before allocation. These are explicit
policy charges, not a claim to account for every allocator byte or to convert
process-level allocation aborts into typed failures.
Default host wire caps still apply; formation at the maximum length does not
promise admission under a particular run's resource policy.

## Independent reduction requirements

The optional checker recognizes the closed polynomial family
`boolean-sum-to-point/0` and the relation-pinned
[R1CS specialization](composition.md#independently-specified-r1cs-client). Requirements are supplied separately from the candidate:

```json
{
  "format": "zkc.polynomial-requirements/0",
  "requirements": [{
    "id": "public-sumcheck",
    "family": "boolean-sum-to-point/0",
    "reduction": "reduction", "terminal": "terminal", "recipe": "recipe",
    "verifier": "V", "terminal_role": "V",
    "subjects": [0, 1], "claim": 2, "service": 3,
    "residual_subjects": [0, 1], "residual_point": [2, 3], "residual_scalar": 4,
    "terminal_subjects": [0, 1], "terminal_point": [2, 3],
    "terminal_scalar": 4, "decision": 0
  }]
}
```

Indices identify original protocol input/output ports, not candidate-local SSA
numbers. Requirements are bounded to 1 MiB, nesting 64, 1–64 records, indices
below 4096, and nonempty strings of at most 4096 bytes without NUL.
Unknown/missing keys and duplicate record IDs or terminal targets refuse.
Each list contains 1–32 distinct indices.
Numeric values use canonical unsigned decimal integer tokens. Signs (including
negative zero), leading zeros, decimal points and exponents refuse in scalar
indices and index arrays. Duplicate decoded object keys refuse at every depth,
including differently escaped spellings of the same key. Strings require valid
UTF-8 and Unicode scalar escapes; unpaired UTF-16 surrogates refuse. Whitespace,
object key order and equivalent string escapes preserve the typed requirement.
The authoritative requirement is the checker's typed canonical reserialization,
echoed and hashed in its report. The raw input digest records the supplied bytes.

The retained original module defines one private, flat recipe from subject
field scalars or positive static field arrays using MLE, polynomial constants,
addition and multiplication. The closed recipe vocabulary also includes field
constants/add/multiply/subtract, static array extraction and `data.array_from_elements`.
Subject lengths need not equal the Boolean domain size; each actual recipe
argument and terminal subject must still have exactly the original subject type. The
recipe has positive arity and per-axis degree below 64.
The original terminal calls that recipe and checks its evaluation at its actual
point inputs against its actual scalar input. The checker compares the expanded
candidate DAG to that definition; a matching author hash is insufficient.

The reduction has two roles. The verifier owns the declared BLS random service
and its residual output ports exclusively. In each ordered round it:

1. Receives exactly `degree + 1` coefficients and constructs that received
   polynomial.
2. Guards `q(0) + q(1) = current_scalar`.
3. Queries the declared service's argument-free `draw` after the guard.
4. Sends that challenge and uses `q(actual_draw)` as the next scalar.

The residual returns the actual verifier subjects, all ordered draws including
the last, and the last scalar. The one-role terminal has no actions and only
admitted total mathematics. Its actual decision compares the required recipe
evaluation against that scalar. The checker derives a complete typed bijection
from verifier output ports to terminal input ports.

Ports and ownership are recomputed from the retained original. Projection
metadata is cross-checked, never accepted as the source of meaning.
The original is independently projected without simplification and checked
before the separately supplied candidate is checked. A well-formed candidate
cannot rescue an original with the wrong guard or terminal.

This is a structural correspondence check for the interpreted reduction
contract in [relations](../relations.md). It supplies no general
algebraic equivalence procedure. Transparent expansion and factorwise fixing of the selected client's prover
calculations are supported; arbitrary equivalent verifier rewrites can refuse.
The fixing pass itself operates on all participant blocks, not just a designated
prover role.

## Checked compilation and report scope

The public C++ entry is `checkPolynomialReductions(original, candidate, text)`.
CLI inspection uses
`protocol-check-reductions SOURCE.mlir REQUIREMENTS.json CANDIDATE.mlir`.
It binds the canonical original and candidate IR and canonical requirement
digests. Its report is not an executable certificate.

`protocol-checked-bundle FILE --requirements=FILE --entry=NAME` freezes the
original, projects without simplification, checks correspondence, then applies
the selected simplification/fixing, polynomial elimination, math lowering and
physical selection. Missing or empty requirements cannot select unchecked mode.
The selected entry must belong to a checked reduction/terminal pair or its
[checked static composition](composition.md#checked-reduction-and-terminal-application).

The wrapper `zkc.checked-run/0` contains the exact ordinary
`zkc.run/0` bundle JSON as a string plus `correspondence` and `public_coin`
reports. An unrequested report is null. The correspondence
report binds the exact selected bundle bytes, both companion bundle byte
digests, source/requirements, selected entry and post-check passes.
Consumers composing the pair must validate both bundle identities and use the
derived connector. A report for one bundle does not authorize an unrelated
terminal.

The example harness passes actual returned values through that connector only
after reduction completion. Rejection, returned terminal false, decoding failure
and resource failure remain distinct. Faithful handoff is a harness obligation;
the compiler report does not enforce it in arbitrary host code.

Exec/physical lowering remains trusted and tested. The report is neither a Lean
proof nor a cryptographic security certificate. Quantitative Sumcheck bounds
additionally require a declared challenge experiment; action order alone does
not establish uniformity. New native Lean interpretation, private PCS terminals
and dynamic protocol composition are deferred. Static native applications and
selected composed entry checking are specified in [composition](composition.md).

### Scalar selection realization

Admitted `arith.select` over Boolean, unsigned index, nominal field or nominal
group values lowers to one exact `bool.select`, `index.select`, `field.select`
or `curve.select` invocation. The independent recipe reader compares the
condition, ordered alternatives and domain arguments against actual source SSA.
This replaces the outlined conditional recipe for the complete admitted scalar
profile. Source conditionals retain their separate scoped execution meaning.

# Structured native mathematics

This profile extends [mathematical protocols](mathematical-protocols.md) with
formal polynomial SSA and static field data. Mathematical meaning belongs to
[tables and polynomials](../../domains/polynomials.md). It retains
the profiles `protocol → participant → exec → physical`; an analysis or
lowering does not introduce another editable mathematical graph.

## Types and total operations

`!poly.polynomial<"F", n>` denotes the formal ring `F[X0,...,X(n-1)]`.
`F` is an installed field and `0 ≤ n ≤ 32`. Zero arity denotes `F`.
This is a compile-time mathematical value. Transparent, acyclic private helpers
may produce it; protocol inputs, outputs, messages and executable bindings may
not contain it. Helper preparation exposes constructors before degree analysis.
It is distinct from the existing normalized concrete `!poly.univariate` object.

Concrete data uses `tensor<Nx!algebra.field<"F">>`, with no encoding attribute,
rank one and `0 ≤ N ≤ 1048576`. Logical encoding is `field_array<F,N>`.
This shape is part of complete type identity through physical selection.
Dynamic field vectors retain their existing meaning. A static array does not
denote a polynomial until an operation supplies that interpretation.

The following flat operations are total on their verified types:

| Operation | Signature and judgment |
|---|---|
| `algebra.constant` | Canonical field literal string to scalar |
| `algebra.field_subtract` | Two scalars in one field to their difference |
| `tensor.from_elements` | Exactly `N` field operands to the static array |
| `algebra.array_at` | Static array and constant `index` attribute; `0 ≤ index < N` |
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

Every operand and result of a mathematical polynomial operation uses one field.
An empty fixing prefix and a zero suffix count are identities. Fixing all axes
produces arity zero, or a length-one table. Zero-length data arrays are admitted,
but polynomial constructors and coefficient observations require positive arrays.
Coefficients pad with zeros to their static output length.

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

These operations also occur inside [structured iteration](structured-iteration.md).
Nested degree requirements are checked before dead-code elimination. Generic
tensor casts/generation and opaque polynomial callbacks have no admission grant.
[Polynomial recipes](polynomial-recipes.md) cover runtime arity through explicit
realizations; they do not change the static polynomial type.

### Formation diagnostics

Invalid `algebra.constant` literals and `algebra.array_at` extraction use
`mathematical-formation`; this replaces their earlier `polynomial-formation`
code as finite-data formation moves to Algebra. Polynomial operation and domain
formation continue to use `polynomial-formation`. Algebra currently reuses the
installed `field.constant` contract to validate canonical literals; a separate
domain literal contract is not part of this implementation.

## Realization

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

`zkc-lower-math` then uses the existing demand-based local outlining contract.
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

The installed array representation is
`field_array<bls12-381.fr,N>@arkworks.field-array/1`, with an empty extra nominal
identity. This complete identity is checked independently in C++ and Rust.
Other fields can have mathematical formation without an installed native array
provider.

Arrays use immutable shared storage. Their generic custody declaration is
`PrivateImmutable` (copy and drop); codec support is an independent property.
This classification does not assert secrecy. The mathematical profile permits
role sharing through the native array wire codec. `fixed_vector` has its own
custody and codec rules.

One array exchange is one frame: the six bytes `ZKCV`, version `01`, tag `40`,
followed by exactly `N` canonical 32-byte little-endian BLS scalar encodings.
The length is obtained from the expected complete type, not from an untrusted
length prefix. Total frame size is `6 + 32*N`. Existing Boolean/scalar/group
frames are unchanged.

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
`boolean-sum-to-point/1` and the relation-pinned
[R1CS specialization](protocol-composition.md#independently-specified-r1cs-client). Requirements are supplied separately from the candidate:

```json
{
  "format": "zkc.polynomial-requirements/1",
  "requirements": [{
    "id": "public-sumcheck",
    "family": "boolean-sum-to-point/1",
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
constants/add/multiply/subtract, static array extraction and `tensor.from_elements`.
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
contract in [relations](../../properties/relations.md). It supplies no general
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
[checked static composition](protocol-composition.md#checked-reduction-and-terminal-application).

The wrapper `zkc.checked-run/1` contains the exact ordinary
`zkc.run/1` bundle JSON as a string plus `correspondence` and `public_coin`
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
selected composed entry checking are specified in [composition](protocol-composition.md).

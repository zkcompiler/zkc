# Vectors and linear combinations

Native MSM, matrix contractions and vector kernels use these ordered value contracts.
This chapter states shared laws; a native implementation claim needs its
actual instance and evidence. Independent formal examples retain their own
[model scope](../../../lean/docs/README.md).

For a carrier `X`, `Vector X n = Fin n → X`. A dynamically sized vector carries
its length together with that indexed value. Length zero is permitted. Element
order is part of the value; equal byte widths or element counts do not identify
different scalar fields, groups, coordinate points or polynomial tables.

An operation on raw sequences checks every required length before interpreting
them as indexed vectors. A truncated zip or a zero-default lookup is not a
meaning for mismatched inputs. A checked conversion to a Boolean table requires
exactly `2^n` cells and the [declared coordinate order](polynomials.md#flat-table-indexing).
A conversion to a point preserves the declared coordinate order and dimension.

## Linear combinations

Let `R` be a semiring and `M` an additive commutative monoid with an `R`-module
structure. Define:

```text
combine(w,x) = sum_i w[i] • x[i]
```

Here `w : Vector R n` and `x : Vector M n`. With `M = R` this includes a scalar
dot product. With a suitable group and its scalar action it includes multiscalar
multiplication. Empty combinations are zero. Using a concrete cryptographic
group requires its declared scalar action; a generic group operation name does
not establish that instance.

For `A : Fin m → Fin n → R`, define:

```text
apply(A,x)[i] = sum_j A[i,j] • x[j]
pullback(w,A)[j] = sum_i w[i] * A[i,j]

combine(w,apply(A,x)) = combine(pullback(w,A),x)
```

The coefficient order in the pullback is significant over a noncommutative
semiring. The scalar case is the matrix/dot-product associativity law; the
module case also permits group-valued entries. In particular, a diagonal map
gives:

```text
combine(w, fun i => d[i] • x[i]) = combine(fun i => w[i]*d[i], x)
```

These are value equalities under the stated algebraic and shape premises.
The current protocol-focused formal package does not claim a general native
vector-map or reduction correctness theorem.

## Matrix and sequence operations

A flat matrix declaration identifies its row count, column count and index
mapping. Row-major storage places `(i,j)` at `i*columns+j`. Transpose selection
changes which index is contracted; it does not authorize applying the forward
map a second time. Kronecker products similarly declare their pair-index order.
Representations may implement these meanings without storing a dense matrix.

Sequence splitting returns ordered, contiguous halves under the stated nonempty,
even-length precondition. This alone does not assert a power-of-two length or a
protocol's round count. Concatenation, gathering and polynomial/point conversions
retain their own bounds and index obligations.

A first-class dynamic matrix carries row and column dimensions and its
coefficient map over one nominal field. `matrix.mul_vector(M,x)` requires
`length(x) = columns(M)` and returns the row-indexed product.
`matrix.transpose_mul_vector(M,u)` requires `length(u) = rows(M)` and returns
the column-indexed pullback. `matrix.bilinear(M,u,x)` requires both shapes and
returns `dot(u,M*x)`. `matrix.shape_check` compares both actual dimensions with
its declared natural attributes. Zero dimensions have their ordinary empty-sum
meaning. Storage and library choices belong to the physical representation.

`matrix.get<F>(M, row, column)` takes two dynamic `index` operands, no
attributes, and returns a field element of `F`. It requires `row < rows(M)`
and `column < columns(M)`. Failure of either check refuses with `matrix-index`;
large indices must not wrap or truncate into the shape. A matrix with either
dimension zero has no valid element access. Within the shape, an absent sparse
COO entry denotes the zero of `F`, and a present entry yields its coefficient.
This is checked execution, not total mathematical access for arbitrary indices.

`matrix.row_dot<F>(M, x, row)` and `matrix.column_dot<F>(M, y, column)`
take a matrix, a vector and a dynamic `index`, with no operation attributes,
and return one scalar of the same nominal field `F`. Their equations are

\[
\operatorname{row\_dot}(M,x,r)=\sum_{j=0}^{\operatorname{columns}(M)-1} M_{r,j}x_j,
\qquad
\operatorname{column\_dot}(M,y,c)=\sum_{i=0}^{\operatorname{rows}(M)-1} M_{i,c}y_i.
\]

Row contraction first requires `length(x) = columns(M)`, then
`row < rows(M)`. Column contraction first requires `length(y) = rows(M)`,
then `column < columns(M)`. A length mismatch refuses with `matrix-shape`;
an invalid selected index refuses with `matrix-index`, without wrapping or
truncating the index. These checks apply even when the matrix has no nonzeros.
A zero inner dimension returns zero for a valid selected index: an `R x 0`
matrix has `R` valid row contractions and a `0 x C` matrix has `C` valid column
contractions. A zero selected dimension has no valid contraction. The SDK
exports these operations as `zkc::matrix::row_dot` and `zkc::matrix::column_dot`.

The installed native implementations use canonical COO sorted by `(row,column)`.
Row contraction locates its contiguous range by binary search and traverses only
that range, taking `O(log(nnz + 1) + row_nnz)` work. Column contraction scans
the existing `nnz` entries, taking `O(nnz)` work. Both use constant auxiliary
storage and compute only the requested scalar, without materializing a row,
column or whole matrix-vector product. These are kernel-body bounds; admission
and [capacity accounting](../runtime/capacity.md) retain their own work.

Bindings retain their explicit implementation choice and field identity:
`arkworks` supports BLS12-381 Fr and BN254 Fr, `dalek` supports Ristretto255
scalars, and `plonky3` supports KoalaBear and its installed octic and quartic
extensions, and the [binary fields](values.md#binary-fields) GF(2^64) and its
cubic extension.
Native scalar output preflight reserves the existing 512-byte retained charge
before arithmetic or shape/index checks, including zero results. Insufficient
per-value or invocation output allowance reports `exhausted:output-bytes`.
The result has no shared vector backing; operands retain their full logical
read charge. The existing matrix dimension cap of 65,536 and nonzero cap of
1,048,576 still apply, along with input and aggregate capacity limits.

`matrix.identity_check<F>(M) [digest]` compares SHA-256 of a canonical
mathematical encoding with one lowercase 64-character hexadecimal attribute.
The encoding is compact UTF-8 JSON
`["zkc.matrix/0", fieldName, [rows, columns, entries]]`, with naturals and
coefficients as canonical decimal strings. Entries are ordered `[row,column,value]`
triples; zero coefficients are omitted. Prime-field values use least nonnegative
representatives. The installed octic and quartic extensions encode their
ascending coordinates as the integer `sum(c_i * p^i)`. A binary-field value is
the same integer with `p = 2` over its coordinates in `F_2`: the unsigned
integer of its [bit pattern](values.md#binary-fields). Thus shape, nominal field and coefficients all
contribute. The result is Boolean; a consuming guard decides whether to reject.
This is a content-binding contract under the stated hash assumption, not a
proof of source-compiler adequacy or prepared-key derivation.

Sparse coordinate storage denotes a coefficient by summing its entries at that
coordinate. Its selected canonical codec uses strictly increasing `(row,column)`
pairs, nonzero coefficients and exact field encodings. An internal algebraic
view may contain duplicate contributions without being a canonical input value.
The [constraint view](constraints.md#sparse-representations-and-views) uses this
distinction for challenge-dependent row contractions.

`vector.constant` returns the ordered field values of its attributes. Generic
source naturals reduce in the instantiated field; bound operations contain only
canonical field values. `vector.scatter_sum(values)` declares an output length
and one destination index per input value. Every destination must be in range;
output coordinate `j` is the sum of all inputs whose destination equals `j`.
Repeated destinations add, and absent destinations yield zero. Shape and index
checks occur even for an empty result; this operation never silently drops an
out-of-range contribution.

## Static parameters and bulk operations

Attributes below are canonical natural numbers. They select a mathematical
operation at compilation time; they do not create extra executed index values.

| Contract | Value and preconditions |
|---|---|
| `vector.at(v) [i]` | Zero-based element `v[i]`; refuse if `i >= length(v)` |
| `vector.length_check(v) [n]` | Boolean `length(v) = n`; a false result does not itself reject execution |
| `vector.splat(x) [n]` | `n` copies of `x`, including an empty result at zero |
| `vector.powers(x) [n]` | `[1,x,...,x^(n-1)]`, empty at zero |
| `vector.gather(v) [i0,...,ik]` | Ordered selected elements; repetitions allowed, every index checked; empty index list gives an empty result |
| `vector.add/sub/mul(a,b)` | Elementwise operation, requiring equal lengths |
| `vector.scale(v,x)` | Ordered scalar multiples, preserving length |
| `vector.sum(v)` | Sum of entries; empty sum is zero |
| `vector.product(v)` | Product of entries; empty product is one |
| `vector.dot(a,b)` | Sum of pairwise products, requiring equal lengths; empty sum is zero |
| `vector.kronecker(a,b)` | Left-major products: result at `i*length(b)+j` is `a[i]*b[j]` |
| `vector.matvec(A,x) [rows,columns,transpose]` | Flat row-major matrix with exactly `rows*columns` entries; `transpose` is `0` or `1`. Forward input has `columns` entries; transposed input has `rows` entries. Returns the ordinary product or pullback, including empty-sum cases |

All shape, checked-size and output-budget conditions remain observable. Static
and dynamic access/fill/power forms share a value law after substituting the
parameter. Replacing a static attribute by a new `index.constant` instruction
also introduces an occurrence and resource charges, so that replacement is not
an unconditional execution-preserving canonicalization. Similarly, replacing
flat `matvec` with a matrix constructor and contraction requires a stated shape,
failure-order and resource relation.

`vector.product<F>` takes exactly one vector and returns one scalar of the same
nominal field, with no operation attributes. It is distinct from pairwise
`vector.mul(a,b)`, which returns a vector and requires equal lengths, and from
`prefix_product`, which returns every inclusive prefix. Product accepts zeros,
singleton and repeated entries. Empty input still produces and charges a scalar
output through ordinary native resource admission.

## Dynamic sequence operations

`vector.get<F>(v,i)` selects the actual element at the checked `index` operand;
`vector.length<F>(v)` returns an `index`. Static-attribute `vector.at` remains a
separate constant-position operation. Missing elements never become zero.

`vector.slice<F>(v,start,length)` returns the contiguous ordered subsequence
beginning at the dynamic `index` operand `start`, with exactly `length` entries.
It has no attributes. It requires `start <= length(v)` and
`length <= length(v) - start`; checked-size and allocation limits also apply.
An empty slice at the end is valid. Out-of-range slices refuse rather than
truncate, wrap, or pad. The bounds, length and coordinate laws are native obligations. The current
scalar PIR-to-Lean import profile does not cover vector slicing.

`vector.transpose<F>(v,rows,columns)` changes a flat row-major `rows × columns`
matrix into the flat row-major transpose. It requires exactly `rows*columns`
entries, with checked multiplication, and takes no attributes. The coordinate
law is `result[column*rows + row] = v[row*columns + column]`. Zero extents admit
only an empty vector and return immediately, even if the other extent is large.
Transposing again with exchanged extents restores every coordinate. The selected
realization visits each element once and checks shape and allocation limits
before copying. This checked layout operation preserves field identity and
values; it supplies neither polynomial interpolation nor a change of domain.

`curve.get<G>(xs,i) : groups<G>, index → group:G` selects the group at
zero-based position `i`; `curve.length<G>(xs) : groups<G> → index` returns
the actual sequence length, including zero. Both take no operation attributes.
They preserve the exact nominal group binding and require its installed
`ScalarAction(G)` contract, consistently with the other `curve` operations.
`curve.at<G>` remains the distinct static-position operation with one canonical
natural attribute. Both accessors refuse missing elements with `group-index`;
neither substitutes the identity, wraps an index, nor converts a field element
to an index. No generic container or resource-sequence operation follows from
these contracts. Native output and retained-value budgets still apply.

These operations let a local verifier inspect a runtime commitment batch and
check a selected equation with the existing group operations. Combining that
check with `or(not(enabled), equation)` changes the returned predicate only:
even when disabled, the selection and equation have already executed.

`vector.rotate<F>(v,k)` rotates left by `k`, requiring a nonempty vector and
`k < length(v)`. `vector.interleave<F>(a,b)` requires equal lengths and produces
`[a[0],b[0],a[1],b[1],...]`. Empty equal-length inputs are admitted.
`prefix_sum` and `prefix_product` return inclusive prefixes, with the same length
as their input; their empty result is empty. `vector.inverse` requires every
entry to be nonzero. Prefix products permit zeros and never divide.

`vector.bit_reverse<F>(v)` requires a length `n = 2^k` with `k >= 0` and
returns `result[i] = v[rev_k(i)]`, where `rev_k` reverses the `k` low bits of
`i`. `vector.bit_reverse_rows<F>(v,w)` treats `v` as a flat row-major table of
width `w`; it requires `w > 0`, `length(v)` divisible by `w`, and a height
`h = length(v)/w = 2^k`, and returns row `i` of the result equal to row
`rev_k(i)` of the input, with the order within each row unchanged. A width of
one is the element permutation. Both are involutions and preserve field
identity and values. They refuse an empty or non-power-of-two height with
`vector-bit-reversal` and a zero or non-dividing width with `vector-shape`, and
take no attributes. They are positional, defined for every field independently
of its characteristic or two-adic structure; they supply no evaluation-domain
or polynomial meaning by themselves. A consumer that reads a bit-reversed layout
as evaluations on a subgroup coset states that correspondence separately.

`vector.fill<F>(x,n)` produces `n` copies of `x`; `vector.geometric<F>(x,n)`
produces `[1,x,...,x^(n-1)]`. Both admit zero length and take a dynamic `index`.
`vector.embed<E>` applies the declared `E.BaseField → E` embedding elementwise.
These are sequence operations shared by protocol families. In particular, a
prefix-product computation is not itself a permutation argument: its challenge
ordering, linkage to committed traces, and terminal equality are separate
protocol obligations.

## Pointwise maps

Let `f : F^k -> F` be a ring expression over one field and let a mask select its
rowwise inputs. For rowwise inputs `v_j : Vector F n` and scalar inputs `x_j : F`,
the checked map has length `n` and

```text
map(f)(...)[i] = f(..., v_j[i], ..., x_j, ...)
```

Every rowwise input must have the same length, which may be zero. A mismatch
fails the checked map, including for an input that `f` does not read; nothing is
truncated or padded. The failure has the class of a vector kernel's own shape
check, not a native protocol rejection; see the
[source contract](../language/definitions.md#checked-pointwise-maps). This is elementwise arithmetic on vectors. It is not substitution into
formal polynomials: a pointwise product of two tables is not the table of the
product of their multilinear or univariate interpretations.

A successful map is row-by-row evaluation; unequal rowwise lengths cannot
succeed. A helper-composed formula may be mapped over the same operands, and a
scalar-only subformula has one value for every row. Eliminating unreachable
arithmetic must still preserve every original shape guard. These are native
preservation obligations; the selected scalar Lean bridge does not cover vector
maps or their backend implementation.

## Finite map reductions

For admitted same-length row operands and scalar operands of one field, let
`mapped = map(f)(operands)`. Define:

```text
mapSum(f, operands)     = sum(mapped)
mapProduct(f, operands) = product(mapped)
```

The checked map's admission precedes either reduction. A formula that ignores a
row still requires that row's length to agree with every other row. Matched
empty rows yield zero for sum and one for product; an absent rowwise operand
or a mismatched unused row does not become an empty identity. Map refusals
propagate before the reducer obtains a value.

If the formula is exactly `row_a * row_b`, its sum equals `dot(row_a,row_b)`
after admission of the entire original operand list. A rewrite must preserve
all original ordered shape guards, even when the dot itself uses only two of
several row inputs. The [optional native fusion contract](../ir/protocols.md#optional-vector-reduction-fusion)
states the restricted rewrite and its resource relation.

Source binding and evaluation order belong to the
[finite reduction contract](../language/definitions.md#finite-reduction-binders).
The current scalar Lean bridge does not prove these native vector reductions;
empty inputs, unused-row refusal and error propagation remain required native
checks and future adapter obligations.

## Representation and execution

A diagonal representation may retain immutable factors and original values
instead of materializing scaled entries. Its denotation is the same ordered
vector. A consumer must support that representation; serialization, an escaping
result or an incompatible consumer requires an explicit valid materialization
or refusal.

The algebraic law does not authorize removing shape checks, changing sampling,
moving work across an observed stopping position, or ignoring retained backing
storage. A compiler consumer states its [execution relation](../verification/refinement.md),
including whether it compares successful runs under sufficient resources or
establishes a stronger relation on failures. Fewer temporary allocations do not
by themselves establish equal exhaustion behavior or lower retained-memory use.

## Whole-vector equality

`vector.equal<F>(left,right)` returns true exactly when lengths agree and each
pair of corresponding field elements is equal. Unequal lengths return false;
there are no shape attributes. The domain requires `CommRing`. It is a checked
local kernel, realized by an installed scalar provider. It allows authored
constraint checks over complete columns without passing a captured vector
through a scalar loop for every row. It establishes no timing or constant-time
property and does not erase preceding failures or resource charges.

## Ordered equality search

`vector.find_last<F>(values,value)` returns the greatest matching position, or
`length(values)` when no entry matches, including zero for an empty vector.
Equality compares the complete nominal field element, including every extension
coordinate. The domain requires `CommRing`. All entries are visited in stored
order; duplicate values are allowed. Inputs and repeated aliases are immutable.
This authored operation does not assert constant-time behavior or preserve the
resource-exhaustion prefix of a source loop.

The native handler checks input extent and the conservative 512-byte index
result allowance, then admits `length(values)+1` numerical work units and
512 managed bytes
before scanning. It creates no mask, temporary vector or retained lookup table.

# Vectors and linear combinations

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

The maintained Lean laws are
[`linearCombination_rows` and `linearCombination_smul`](../../../formal/Zkc/Algebra/LinearCombination.lean).
They establish value equalities under the stated algebraic and shape premises.

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

`matrix.identity_check<F>(M) [digest]` compares SHA-256 of a canonical
mathematical encoding with one lowercase 64-character hexadecimal attribute.
The encoding is compact UTF-8 JSON
`["zkc.matrix/1", fieldName, [rows, columns, entries]]`, with naturals and
coefficients as canonical decimal strings. Entries are ordered `[row,column,value]`
triples; zero coefficients are omitted. Prime-field values use least nonnegative
representatives. The installed octic extension encodes its ascending coordinates
as the integer `sum(c_i * p^i)`. Thus shape, nominal field and coefficients all
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

## Dynamic sequence operations

`vector.get<F>(v,i)` selects the actual element at the checked `index` operand;
`vector.length<F>(v)` returns an `index`. Static-attribute `vector.at` remains a
separate constant-position operation. Missing elements never become zero.

`vector.slice<F>(v,start,length)` returns the contiguous ordered subsequence
beginning at the dynamic `index` operand `start`, with exactly `length` entries.
It has no attributes. It requires `start <= length(v)` and
`length <= length(v) - start`; checked-size and allocation limits also apply.
An empty slice at the end is valid. Out-of-range slices refuse rather than
truncate, wrap, or pad. The typed Lean slice laws establish bounds, length and
coordinate preservation; native runtime adequacy remains separately tested.

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

`vector.fill<F>(x,n)` produces `n` copies of `x`; `vector.geometric<F>(x,n)`
produces `[1,x,...,x^(n-1)]`. Both admit zero length and take a dynamic `index`.
`vector.embed<E>` applies the declared `E.BaseField → E` embedding elementwise.
These are sequence operations shared by protocol families. In particular, a
prefix-product computation is not itself a permutation argument: its challenge
ordering, linkage to committed traces, and terminal equality are separate
protocol obligations.

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

# Core operations

Core packages separate native representations, traversal and convenience APIs.
Each linked manifest is an independent capture boundary. Import only packages
your source uses directly; public facades retain concise source names.

| Package | Owned modules under `zkc::` |
|---|---|
| [Primitive collections](primitives/collections/zkc.toml) | `primitives::{vector,indices,bytes}`, `sequence`, `matrix`, `field_array` |
| [Primitive algebra](primitives/algebra/zkc.toml) | `primitives::{curve,scalar}`, `pairing` |
| [Primitive polynomials](primitives/polynomial/zkc.toml) | `primitives::{coset,quotient}`, `polynomial`, `symbolic` |
| [Primitive cryptography](primitives/cryptography/zkc.toml) | `primitives::hash`, `encoding`, `oracle`, `permutation`, `shake128`, `transcript` |
| [Traversal](traversal/zkc.toml) | `accumulation`, `finite_domain`, `finite`, `finite_math` |
| [Collections](collections/zkc.toml) | `vector`, `indices` |
| [Algebra](algebra/zkc.toml) | `scalar`, `curve`, `boolean`, `linear` |
| [Polynomials](polynomial/zkc.toml) | `multilinear`, `coset`, `evaluation_domain`, `opening_claims`, `opening`, `quotient` |
| [Encoding](encoding/zkc.toml) | `bytes`, `proof` |
| [Services](services/zkc.toml) | `sampling::words`, `sampling::fields` |

Primitive packages own native identities and direct bindings. Traversal uses
those lower identities, so a vector reduction facade can depend on traversal
without creating a cycle. Facades deliberately reexport operations and notation.
They do not capture unrelated protocol or construction families.

## Checked evaluation and opening views

`evaluation_domain::checked_roots` admits the complete roots-of-unity group in
the supplied order. `two_adic` and `two_adic_bit_reversed` instead check a known
size and exact generator order, then materialize the points without a pairwise
scan. Size one requires generator one; empty domains, repeated points, invalid
roots, non-power-of-two fast inputs and smaller-order generators stop.
`evaluations(unity, data)` fixes equal extent. Getter operations expose the
admitted observations without permitting replacement of private fields.

`coset::coset_domain(shift, size)` admits one canonical natural-order two-adic
coset. `ColumnBatch` fixes its width and exact column-major extent, with checked
index arithmetic before slicing. `extend_batch(input, output_domain)` re-evaluates
each column on the target coset with one private result; `extend_columns` is the
unit-input-shift convenience function. Shrinking requires every interpolant to
fit the target size. These functions do not establish a cryptographic degree
bound. `evaluate_at(word, point)` evaluates one checked word directly;
`evaluate_columns(batch, point)` shares domain/point weights across all columns.
Points on the coset return the corresponding row. Coefficient interpolation
remains available for algorithms that reuse coefficients.
`coset::evaluate_batch(coefficients, columns, coefficient_height, shift, output_height)`
evaluates exact column-major coefficient blocks with one private output.
Coefficient height can be zero or non-power-of-two; shrinking permits only zero
discarded tails in every block. Zero columns ignore the unused domain, while
positive columns require a valid domain even for zero-height blocks. The caller
supplies representation padding. This authored operation has its own numerical
work and workspace admission.
`opening_claims::checked` preserves ordered,
possibly repeated column/rotation/value descriptors. `opening::bind_openings`
binds those descriptors to one coset, width, admitted trace height and zeta,
checks bounds, and excludes every derived opening point from the evaluation
coset. The trace domain is checked even for an empty descriptor list.

`VectorAccumulator` fixes a coset, an exactly sized initial vector, a ratio and
the next weight. `QueryRow` fixes a coset, a bounded query index and an exact row
width; its point is derived from this context. `ScalarAccumulator` carries the
matching coset and query index with the same weight recurrence.

`coset::opening_quotient_sum` combines selected columns with explicit points,
claims, weights and an initial vector. `opening::deep_columns` uses it with the
accumulator's geometric weights, borrowing columns and constructing one private
result. Consecutive openings at the same point reuse denominator inverses within
that call. Zero weights still require off-domain points. This authored bulk
operation has its own resource profile; it preserves the mathematical result,
not the exhaustion points of separate quotient and accumulation calls.

```text
let geometry = coset::coset_domain(shift, size);
let columns = coset::column_batch(geometry, width, data);
let bound = opening::bind_openings(geometry, width, height, zeta, descriptors);
let state = opening::vector_accumulator(geometry, rho, initial, first_weight);
let next = opening::deep_columns(columns, bound, state);
```

`deep_columns` and `deep_row` compare domain values and widths at each join;
the row form also compares query indices. Independently reconstructed equal
contexts work. Thread the returned accumulator to continue weights across
batches. An empty list preserves values and next weight while retaining all
context checks. Private fields prevent construction, mutation or projection
outside the owning module; raw Entry inputs and messages cannot assert these
invariants. Receive public components and reconstruct each view locally.
These checks establish mathematical layout and denominators; authentication,
degree bounds, sampling and acceptance remain protocol obligations.

## Representation contracts

`multilinear::table(entries, dimensions, columns)` checks a row-major table with
`2^dimensions` rows and positive factor width. `Table<F>` retains these
dimensions in private fields. `fix_first` fixes the leading, MSB-first Boolean
coordinate; `fix_prefix` retains the remaining dimensions and every factor
column. `values`, `variables` and `width` expose observations. Zero variables
means one row. `Evaluation<F>` carries a point and value; its polynomial,
dimension and commitment remain the caller's obligation.

`coset::word(data, shift)` checks a nonempty two-adic size and nonzero shift.
`Word<F>` keeps its values and shift in private fields and uses natural domain
order.
`interpolate` and `evaluate_coset` convert between a word and univariate
coefficients. `fold` pairs points `x` and `-x` and returns a word on the squared
coset with half the size. This differs from multilinear restriction.
`opening_quotient` forms `(f(X)-value)/(X-at)` on the supplied coset and refuses
a zero denominator. `disjoint_coset` excludes intersection in either size order.

These records are checked library values, not new native types or compiler
refinements. They cannot enter through raw Entry inputs or messages; receive
raw values and construct the view locally. Constructors establish layout and
domain validity, not polynomial identity, a degree bound or authentication.

`oracle` commits row-major field elements with an explicit width. Authentication
requires the root, width, number of rows, position, row and path. A successful
row check establishes no polynomial evaluation or low-degree claim. `State`
contains prover opening data; `Root` and `Path` are distinct native values.
For schemes with `MultiOpening`, `open_many` returns the rows at several
positions with one pruned proof and `check_many` authenticates them; the
verifier supplies the positions, which must be nonempty. The proof layout is in
the [oracle contract](../../docs/spec/domains/oracles.md#openings-and-the-pruned-proof).

`scalar::inverse` and vector inversion refuse zero. Vector arithmetic and
layout operations retain native shape checks. `scalar::power` uses an unsigned
64-bit index exponent. `indices::two_adic<Max>` recognizes powers of two from
2 through `2^Max`, with `Max <= 63`; zero and one return false. Prefix sums and
products preserve every prefix, while ordinary sums and products return one
value. `polynomial` stores univariate coefficients in increasing
power order; an empty coefficient vector denotes zero.


## Linear group expressions

`linear::Combination<G>` stores ordered scalar/point terms in private fields.
`from_terms` checks equal lengths; `zero`, `term`, `append`, `add` and `scale`
preserve that invariant. `evaluate` uses one ordinary MSM, including for empty,
repeated, related or identity points. `is_zero` checks one expression; `equal` evaluates the difference of one
pair of expressions. Independent equations still require separate checks.

```text
let lhs = linear::from_terms(responses, bases);
let rhs = linear::append(linear::term<G>(1, commitment), challenge, statement);
let accepted = linear::equal(lhs, rhs);
```

Keep coefficients over a known common basis as vectors, add those coefficients,
and attach the basis once with `from_terms`. `add` concatenates ordered terms; it
does not discover common bases or prune runtime zero coefficients. Points must
already be admitted `G` values. Evaluation inherits the selected MSM contract
and its capacity/timing behavior; the library adds no deferred decoding or
variable-time permission. These checked records have the same ingress boundary
as `Table` and `Word` above.

## Byte assembly

`encoding::index_uleb128(value)` emits the shortest unsigned LEB128 encoding
of any `index`, including zero and the full u64 maximum. Its length depends on
the integer. It selects no transcript framing or transport format.

`bytes::repeat(byte, count)` creates padding and `bytes::join(Sequence<Bytes>)`
assembles ordered fragments without repeatedly copying their growing prefix.
`encoding::fields_be`, `fields_le` and `groups_compressed` encode collections
using the corresponding scalar codecs, with no length prefix.
`encoding::fields_from_be` decodes a whole big-endian vector: it returns false
and an empty vector unless the length is a multiple of 32 and every element is
canonical. For KoalaBear and its extensions, `field_montgomery_le` and
`fields_montgomery_le` write the Montgomery residues that Plonky3's binary
serializers use, and `fields_from_le`/`fields_from_montgomery_le` decode whole
elements, rejecting any word at or above the modulus. Domain support and capacity
checks follow the
[native encoding contract](../../docs/spec/realization/external-constructions.md#mathematical-byte-encodings).
These operations do not observe values or choose transcript framing.
`bytes::keccak256` and `bytes::sha256` are the raw hash functions, with no
domain separator or framing of their own.

`permutation::poseidon2_16(states)` applies the installed width-16 Poseidon2
permutation to each consecutive 16-element state of a KoalaBear vector, as one
batched call. It is a raw permutation: sponge and compression modes, padding,
capacity and domain separation belong to the calling library. Parameters and
work charges follow the [permutation contract](../../docs/spec/domains/permutations.md).

Use `concat` for a few small fixed fragments. `join` is useful when fragments
already form a sequence or repeated prefix copying dominates; constructing a
sequence also has storage and work costs.

## Bounded sampling

`zkc::sampling::words::uniform_index<W, Attempts>(state, bound)` returns the next
provider state and an index in `[0, bound)`. `W: Words` supplies one unsigned
64-bit word per `next` call; the interface does not require copyable state.
`bound` may be any positive u64. Zero rejects before a provider call. The
sampler stops drawing after the first accepted word; exhausting `Attempts`
stops with `exhausted`, including when the attempt count is zero. Bound one
still consumes one word when an attempt is available.

The rejected prefix has length `2^64 mod bound`. The accepted interval therefore
contains equally many representatives of each residue. Under independent
uniform provider words, the result conditioned on success is uniform. Provider
uniformity and independence are premises; compiler checks and deterministic
test vectors do not establish them. A copied provider state is an explicit
trial of that snapshot, and its executed work remains chargeable.

## Finite computations

The finite libraries use statically bound callbacks written `fn(...) -> ...`
or `math fn(...) -> ...`, and finite domains written `domain<I>`. These are
static parameter categories, with no runtime function or domain values. The input
item, accumulated state and output element can have different types. Library
callback signatures name the item input and promise
`where item_from(item, rows)` after their effects. This requires the whole
original item of that exact domain; an equal or reconstructed value does not
satisfy the contract. Lambda binders can use any valid name. For example:

```text
use zkc::finite as finite;
use zkc::finite_domain as domains;

let dot = finite::sum(domains::zip(xs, ys), fn((x, y)) => x * y);
let decimal = finite::fold(xs, initial, fn(state, x) => state * 10 + x);
let selected = finite::sum_where(rows, fn(row) => row.enabled,
                                fn(row) => checked_value(row));
```

A native vector, group vector, sequence, index collection or fixed array supplied
at a domain parameter traverses its elements in storage order. Source arrays
use their existing fixed shape. `elements` names the same traversal explicitly;
`indices` yields positions tied to that exact input. Scalars and matrices have
no implicit element traversal. Matrix views are explicit: `row_values`,
`column_values`, `row_indices`, `column_indices`, `coordinates` (row-major) and
`column_coordinates`. A strict zip validates every child extent before entering
its body, including ignored rows and empty inputs. A product traverses all pairs
in lexicographic order. Nested calls construct inner domains only when reached.

`fold` uses its explicit initial state. `collect` returns a `Sequence<T>`;
representation-specific `vector::collect`, `curve::collect` and `indices::collect`
return their native containers. `field_array::collect` is total and requires an
exact proven cardinality. Filtered forms evaluate their predicate before the
body and skip the body on false. Predicate failures propagate.

`accumulate<I, T, C>` starts from `C::identity()` and applies `C::combine` in
traversal order. The `Combiner<T>` interface supplies total operations without
claiming algebraic laws. The field sum/product and group sum functions select
standard modules. A custom nonassociative combiner still preserves order;
no optimization law follows just from implementing the interface. Group sums
require `ScalarAction(G)`, including empty sums.

`vector::reduce(rows, body, reducer)` materializes the body results before
calling the arbitrary scoped reducer exactly once. The reducer sees the whole
vector and may reject even an empty one. This differs from accumulation; the
compiler does not infer an incremental implementation for a user reducer.

`finite_math` uses the same domain and capture infrastructure with total Math
callbacks. `vector::at`, `sequence::at`, `curve::at`, `indices::at` and
`matrix::at` require proven bounds. Their checked `get` counterparts retain
ordinary Local failure behavior where provided.

Within a Math body, an unfiltered collect preserves the input domain's known
length. For a collect over `elements(xs)` or `indices(xs)`, `indices(xs)` can
therefore read its newly constructed result. An arbitrary range's values need
not be indices into the result.
Exact forwarding helpers preserve the input's identity; collection construction
preserves length without identifying the two values. These shape relationships
also cross total acyclic helpers, including returned record projections. A
filtered result has only an upper count; it does not inherit bounds for the
unfiltered input. Direct total finite calls
also preserve actual range endpoints: `field_array::collect(range(0, 4), body)`
can produce `Array<F, 4>` when its backend supports that carrier. A wrapper with
an unconstrained domain parameter must still justify its own output length.

The vector, matrix, curve, sequence, indices and field-array modules export
library-owned indexing bindings to their total `at` functions. Import
`indexing []` to write `values[position]` or `matrix[row, column]`; the same
bound requirements apply as for the named call. A body-local declaration such
as `indexing values[position] = zkc::vector::get(values, position);` selects
checked Local access explicitly. See the [notation guide](../../docs/language/notation.md#index-collections).
The [finite computation example](../../common/tests/fixtures/projects/finite-computations/README.md)
combines named functions, records, matrix views and total mathematical helpers.
The [FRI fold](../../common/tests/fixtures/projects/fri-fold/README.md) and
[LogUp row](../../common/tests/fixtures/projects/logup-rows/README.md) examples exercise returned
projections, intermediate collection lengths and fixed compression weights in
two protocol computations. They reuse `fri::fold_value` and the
`air::interaction` functions `gated_denominator`, `reciprocal_residual` and
`boolean_residual`. These scalar functions express the equations; their callers
supply authenticated values, valid inverses and the remaining protocol checks.

The [table inner-product](../../common/tests/fixtures/projects/table-inner-product/README.md)
and [lookup denominator](../../common/tests/fixtures/projects/lookup-denominators/README.md)
controls exercise indexed reads through nested helpers, repeated arguments and
distinct equal-length vectors in KoalaBear and Ext8.

## Native mathematics and containers

Import only the modules a client needs. Native `fn` definitions retain ordered
execution and the kernels' possible stop behavior: vector splitting requires a
positive even length, point access checks bounds, arithmetic checks lengths,
and matrix products check dimensions. `multilinear::fix_first` applies a scalar affine formula
through native `map` after splitting; both Sumcheck libraries use this definition.
It fixes one Boolean coordinate of an evaluation table. FRI folding additionally
uses its coset points and keeps its separate domain-specific operation.
`has_length<F, N>` compares the dynamic
length with explicit static `N`; it does not resize or pad a vector.

`zkc::matrix::row_dot(matrix, values, row)` and `column_dot(matrix, values,
column)` compute one selected contraction without materializing all outputs.
The compiler selects these same scalar contracts for supported finite row and
column reductions. Whole row/column collections can select a matvec while
retaining the empty-outer behavior of the authored nested computation.

`zkc::matrix::get(matrix, row, column)` checks both dynamic coordinates and
returns the coefficient in the matrix's field. An absent in-range sparse cell
is zero; an out-of-range coordinate stops execution, including every access to
a matrix with either dimension zero.
`zkc::field_array::from_vector<F, N>(values)` checks that the vector has exactly
`N` elements. `zkc::field_array::get(array, position)` checks `position < N`.
Both are ordinary native functions; fixed field arrays currently execute only
over BLS12-381 Fr. This `Array` has the same type as `zkc::symbolic::Array`.
The symbolic module's static `get<F, N, I>` retains its mathematical bound
requirement. A dynamic `index` alone establishes no such bound.

`zkc::sequence::Sequence<T>` stores executable `Copy + Drop` values, including
records, tuples, fixed source arrays, unit and nested sequences. `empty<T>()`
creates an empty sequence, `append(values, value)` returns the extended sequence,
`length(values)` returns an index, and `get(values, position)` stops when the
zero-based position is out of bounds. These are ordinary ordered `fn` primitives.
Products are packed only at the sequence element boundary; functions taking or
returning records still use the ordinary source ABI. Generic helpers retain the
written Copy/Drop requirements. Private fields and restricted constructors retain
their module authority, and sequence formation grants no external construction authority.
Native JSON/wire codecs retain the packed variant's nominal descriptor and ordered
payload; decoding does not construct private source values.

`zkc::symbolic::Polynomial<F, N>` is a formal expression with `N` variables.
`zkc::polynomial::Polynomial<F>` is runtime univariate coefficient data. Use
qualified paths when both occur in one module. Formal MLEs use MSB-first Boolean
coordinates. `mle<F, N>` keeps `N` explicit because inferring it would invert
`pow2(N)`; ordinary field, array and result inference still applies. Coefficients
are increasing powers; formal coefficient extraction checks its degree premise.
`fix_prefix` substitutes leading coordinates; `sum_suffix` sums trailing Boolean
coordinates. `fix_table` performs the same prefix substitution on an MLE table.
Their static arguments name the remaining arity and the fixed/summed arity;
these choices stay explicit when their sum alone would not determine them.
Generic preconditions are completed from the intrinsic contracts and checked
at each call. These modules select no field, commitment or transcript.

Use `!`, `&&` and `||` to write Boolean expressions. The `zkc::boolean` helpers
remain ordinary functions: `both(a, check(b))` evaluates both arguments even
when `a` is false. In local `fn` code, `a && check(b)` skips the call when `a`
is false. See the [Boolean rules](../../docs/spec/language/definitions.md#boolean-formulas)
for mathematical formulas and resource checks.

The [mathematics client](../../common/tests/fixtures/projects/mathematics/README.md) compares
formal evaluation and vector arithmetic. The embedded scalar prelude supplies
field arithmetic and equality, group addition/equality and `point * scalar`
scaling, Boolean equality, and index arithmetic/equality. Its named functions
and operators share the compiler's native operation identities. Asset-specific
ring operations and module-specific PCS operations stay in their owning
libraries, using explicit asset/module parameters and installed kernels.

Use `zkc::curve::identity<G>()` for a nullary mathematical group zero. Its
result fixes the exact group; no point is needed, including for empty sums.
Use `curve::msm(scalars, points)` for a weighted group sum and
`curve::scale_each(scalars, points)` for one result per pair. Both check equal
lengths and use the selected group's associated scalar field. `curve::add` and
`curve::scale` have the imported spellings `points + other` and `points * scalar`.
`empty`, `append`, `length`, `get`, `split` and `concat` provide the matching
collection operations; `generator`, `neg` and `nonidentity` operate on points.
These source names select existing contracts, not new group families or providers.
`pairing::check<F>(left, right)` and `pairing::apply<F>(a, b)` use the ordered
source groups `F::PairingG1` and `F::PairingG2` of a field with
`zkc::algebra::PairingField(F)`; the empty product is the target identity.
`scalar::from_index<F>` embeds an index by reduction in `F`.

`encoding::cryptonote_map` is specific to `edwards25519.prime`; its signature
makes that restriction explicit. Other encoding functions retain their admitted
generic domains.

Import a whole math module to enable its public operators, for example
`use zkc::vector as vec;`. Vector `+` calls `add`; vector `*` calls `scale` with
the scalar on the right. Matrix `*` calls `multiply` on a matrix and vector.
Formal polynomial `+`/`*` call symbolic `add`/`multiply`. Vector `⊙` is
left-associative at power 70 and calls `hadamard`, an explicit wrapper for
`primitive("vector.mul")`; `⟪a, b⟫` calls `dot(a, b)`. Both retain native
length checks and stop behavior. Vector `*` remains right-scalar scaling.
Named `vec::hadamard(a, b)` and `vec::dot(a, b)` remain available.
Importing `::{Vector, add}` alone enables no notation; add `operator +`,
`operator ⊙` or `notation ⟪` to select the corresponding exported binding. The
[operator contract](../../docs/spec/language/definitions.md#library-defined-operators)
defines ambiguity and local replacement rules. The
[notation guide](../../docs/language/notation.md) shows weighted vector expressions,
delimiter declarations and Unicode input. Symbols preserve ordinary callable
modes and effects; they supply no additional algebra, optimizer or security claim.
The vector module reexports `finite`'s paired sum/product notation. Write
`∑ x in xs, x * x` or `finite::sum(xs, fn(x) => x * x)`. Selective imports use
`reduction ∑` and `reduction ∏`; filters use `with`. Strict zip retains checks
for ignored rows. Named `vec::sum(xs)` and `vec::product(xs)` still reduce an
already constructed vector. The [finite reduction guide](../../docs/language/notation.md#reduce-finite-domains)
explains general domains, scoped bodies, precedence and Local/Math selection.

These functions use `primitive` bodies when their ports determine the installed
scheme. Algorithms and operations with explicit attributes retain ordinary bodies.
Both paths reach the same native mathematical/vector contracts; imports control
source notation and do not install new runtime semantics.

`sampling::fields::Nonzero<F,Attempts>` is a single-participant protocol that rejects zero
candidates from a managed `Random<F>` service. It returns the first nonzero field
value or stops after `Attempts` draws, retaining actual service consumption.
Uniformity is conditional on the provider's field distribution; it supplies no
new randomness assumption. `sampling::words::uniform_index` similarly bounds rejection
over an explicit word provider.

[Quotient-ring values](../../docs/spec/domains/quotient-rings.md) retain a static
modulus and nonempty degree, canonical residues and exact integer norm semantics.
The [lattice arithmetic helper](../relations/lattice/README.md) composes these
operations into a short-preimage predicate.

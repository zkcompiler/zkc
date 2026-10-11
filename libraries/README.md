# Libraries

Reusable `.zkc` modules are maintained with the compiler in this repository.
They define algorithms, relations and protocol interfaces. Applications select
concrete domains, Entries and transcript constructions in
[example projects](../examples/projects/README.md).

## Modules

| Module | Public exports | Contract |
|---|---|---|
| [`zkc::finite_domain`](zkc/finite_domain.zkc) | range/zip/product/array | Finite traversal recipes; zip is strict and product is lexicographic |
| [`zkc::finite`](zkc/finite.zkc) | fold/collect/accumulate/sum/product/group_sum and filtered forms | Ordered Local computations with scoped callbacks and explicit state |
| [`zkc::finite_math`](zkc/finite_math.zkc) | Total counterparts of the finite functions | Mathematical callbacks; every domain formation and bounded read must be justified |
| [`zkc::accumulation`](zkc/accumulation.zkc) | `Combiner`, `FieldSum`, `FieldProduct`, `GroupSum` | Explicit identity/combine implementations; no associativity or commutativity is inferred |
| [`zkc::indices`](zkc/indices.zkc) | `Indices`, empty/append/length/get/at/elements/indices/collect | Ordered index collections, checked and total access, finite traversal |
| [`zkc::computation`](zkc/computation.zkc) | apply_math/forward_math/apply/forward/twice | Generic statically bound callbacks; fixed modes and effects that depend on the selected callback |
| [`zkc::vector`](zkc/vector.zkc) | `Vector`, length/get/at/elements/indices/sum/product/split/add/hadamard/scale/dot/fill/collect/collect_where/reduce/fold/has_length, reduction bindings `∑`/`∏` | Ordered finite vectors; fold pairs contiguous halves |
| [`zkc::sequence`](zkc/sequence.zkc) | `Sequence`, empty/append/length/get/at/elements/indices | Immutable sequences of executable Copy + Drop elements, including source products |
| [`zkc::matrix`](zkc/matrix.zkc) | `Matrix`, get/at/row_dot/column_dot/multiply/transpose_multiply/bilinear/rows/columns and explicit finite views | Ordered sparse matrix operations |
| [`zkc::field_array`](zkc/field_array.zkc) | `Array`, from_vector/get/at/elements/indices/collect | Fixed-length field arrays with checked native construction and dynamic access |
| [`zkc::polynomial`](zkc/polynomial.zkc) | `Polynomial`, from_coefficients/evaluate/boundary | Runtime univariate polynomial data; boundary is p(0) + p(1) |
| [`zkc::symbolic`](zkc/symbolic.zkc) | `Array`, `Polynomial`, pack/get/mle/from_coefficients/coefficients/evaluate/fix_prefix/sum_suffix/fix_table/add/multiply/constant | Total formal polynomial expressions |
| [`zkc::curve`](zkc/curve.zkc) | identity, `Groups`, elements/indices/at/collect | Total group zero, group collection traversal and bounded access |
| [`zkc::boolean`](zkc/boolean.zkc) | both/either/different/negate | Total Boolean formulas; eager operands |
| [`zkc::bytes`](zkc/bytes.zkc) | `Bytes`, empty/append/concat/slice/at/length/equal | Bounded immutable byte strings; slices and byte values are checked |
| [`zkc::shake128`](zkc/shake128.zkc) | `State`, init/absorb/squeeze | Private copyable XOF snapshots; ordered transitions and bounded work |
| [`zkc::proof`](zkc/proof.zkc) | `StreamCodec`, `Stream` | Ordinary sequential record accumulation, offset selection and exact EOF; encoding and observations belong to the construction |
| [`zkc::transcript`](zkc/transcript.zkc) | `State`, observe/challenge/challenge_index | Explicit methods on a construction's managed affine state; no source initializer |
| [`zkc::sampling`](zkc/sampling.zkc) | `Words`, `uniform_index` | Bounded rejection over explicit 64-bit word providers; positive u64 ranges and explicit exhaustion |
| [`zkc::encoding`](zkc/encoding.zkc) | field_be/field_from_be/field_reduce_be/group_compressed/group_from_compressed | Explicit mathematical codecs; currently BLS12-381 Fr and G1 |
| [`schnorr`](schnorr/lib.zkc) | `DLog<G>`, `Schnorr<G>` | Discrete-log relation and three-message group protocol |
| [`spongefish`, `spongefish_schnorr`](spongefish/README.md) | SHAKE128 framing, point/scalar observations, challenges and explicit Schnorr | Spongefish 0.7.4 BLS12-381 G1 specialization; authored 80-byte proofs |
| [`sumcheck`](sumcheck/lib.zkc) | `Sumcheck<F, Max>` | Bounded multilinear Sumcheck over a public evaluation table |
| [`expression_sumcheck`](sumcheck/expression.zkc) | `Sumcheck<F, Max, A: Ring>` | Sumcheck for a captured ring expression over public multilinear tables |
| [`fri`](fri/lib.zkc) | `LowDegree<C, LogSize, TerminalLog, Rounds, Queries>` | Binary FRI over a natural-order two-adic coset |
| [`air_polynomial`, `air_table`, `air_stark`](air/README.md) | Scope polynomials, Bundle opening equations and `TableArgument` | A nonhiding KoalaBear/Ext8 argument for one present table, composed with FRI |
| [`air_interaction`, `air_bundle`](air/README.md#whole-bundle-argument) | `Reduction<F>`, `LogUp<F>`, `GrandProduct<F>`, `ThreeTableArgument` | Three-table multiset arguments with phased auxiliary commitments and shared FRI |

### Bounded sampling

`zkc::sampling::uniform_index<W, Attempts>(state, bound)` returns the next
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

### Mathematics

`zkc::computation` demonstrates ordinary user-defined combinators. Its Math
functions accept total scoped bodies; its Local functions use `effects(body)`
to preserve the supplied callback effects and support affine explicit inputs. Captures require Copy+Drop and become explicit
private-helper arguments. The [module client](../examples/projects/scoped-computations/README.md)
forwards nested callbacks with record/vector captures and a checked lookup.

### Finite computations

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

The vector, matrix, curve, sequence, indices and field-array modules export
library-owned indexing bindings to their total `at` functions. Import
`indexing []` to write `values[position]` or `matrix[row, column]`; the same
bound requirements apply as for the named call. A body-local declaration such
as `indexing values[position] = zkc::vector::get(values, position);` selects
checked Local access explicitly. See the [notation guide](../docs/language/notation.md#index-collections).
The [finite computation example](../examples/projects/finite-computations/README.md)
combines named functions, records, matrix views and total mathematical helpers.

### Native mathematics and containers

Import only the modules a client needs. Native `fn` definitions retain ordered
execution and the kernels' possible stop behavior: vector split/fold requires a
positive even length, point access checks bounds, arithmetic checks lengths,
and matrix products check dimensions. `fold` applies a scalar affine formula
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
is false. See the [Boolean rules](../docs/spec/language/definitions.md#boolean-formulas)
for mathematical formulas and resource checks.

The [mathematics client](../examples/projects/mathematics/README.md) compares
formal evaluation and vector arithmetic. The embedded scalar prelude supplies
field arithmetic and equality, group addition/equality and `point * scalar`
scaling, Boolean equality, and index arithmetic/equality. Its named functions
and operators share the compiler's native operation identities. Asset-specific
ring operations and module-specific PCS operations stay in their owning
libraries, using explicit asset/module parameters and installed kernels.

Use `zkc::curve::identity<G>()` for a nullary mathematical group zero. Its
result fixes the exact group; no point is needed, including for empty sums.
This is distinct from the native generator and empty group-vector operations.

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
[operator contract](../docs/spec/language/definitions.md#library-defined-operators)
defines ambiguity and local replacement rules. The
[notation guide](../docs/language/notation.md) shows weighted vector expressions,
delimiter declarations and Unicode input. Symbols preserve ordinary callable
modes and effects; they supply no additional algebra, optimizer or security claim.
The vector module reexports `finite`'s paired sum/product notation. Write
`∑ x in xs, x * x` or `finite::sum(xs, fn(x) => x * x)`. Selective imports use
`reduction ∑` and `reduction ∏`; filters use `with`. Strict zip retains checks
for ignored rows. Named `vec::sum(xs)` and `vec::product(xs)` still reduce an
already constructed vector. The [finite reduction guide](../docs/language/notation.md#reduce-finite-domains)
explains general domains, scoped bodies, precedence and Local/Math selection.

These functions use `primitive` bodies when their ports determine the installed
scheme. Algorithms and operations with explicit attributes retain ordinary bodies.
Both paths reach the same native mathematical/vector contracts; imports control
source notation and do not install new runtime semantics.

### Schnorr

`Schnorr` takes a base and point at both roles, a scalar at P, and separate
random services for the nonce at P and challenge at V. V returns whether
`base * response == commitment + point * challenge`. `DLog` associates the
statement with its witness; the declaration does not insert a verifier check.

Honest execution requires both roles to agree on the base and point.
The group requires `Group`; concrete selection checks the group and scalar codecs.
Correct use requires suitable group parameters and nonce/challenge
sampling. The example selects BLS12-381 G1. Tests of that execution do not
establish security of every group or transcript choice.

### Sumcheck

`Sumcheck` takes a table at both roles, a claim at V and a round count.
Honest execution requires both roles to agree on the table and count.
`Max` bounds the number of rounds. Each reached split requires a positive even
table length. Acceptance requires one final element, so a table of length
`2^n` needs exactly `n` rounds. Splits use contiguous halves; the first challenge
fixes the table's most significant coordinate.

V retains and folds its public table for the terminal check. This library does
not hide the polynomial or use a commitment. The field requires `Field` with the selected vector kernels and codecs installed. The example uses
BLS12-381 Fr. Vector folding and Boolean formulas use the shared modules; `sums` and
`terminal` are private protocol helpers.

### Expression Sumcheck

The expression-based `Sumcheck` takes separate prover and verifier tables, a verifier claim,
and a shared round count. It is generic over a captured ring expression
`A: Ring` and requires `1 <= A::Inputs` and exactly one output
(`1 <= A::Outputs, A::Outputs <= 1`); a client passes an asset domain such as
`domain Product = ring(asset product)`. Tables contain `A::Inputs` columns in
row-major order. Both roles must use the same table, column order, arena and
round count for honest execution. Each round pairs the first and second halves
of the rows, so the first challenge fixes the most significant Boolean coordinate.

P sends exactly the coefficients of `sum_i P(low_i + (high_i - low_i) X)`
through the installed `ring.affine_sum` kernel, padded to `A::Degree + 1`
where `A::Degree` is the arena's largest output degree with every input
weighted one; the vector preserves trailing zeros before transmission. V checks
that coefficient count and the round sum, folds its own table, and checks the
terminal value through `ring.point` on the final `A::Inputs` factors. Both roles
fold through `zkc::vector::fold`, whose private scalar helper is applied by
checked [`map`](../docs/spec/language/definitions.md#checked-pointwise-maps):
each row of the halves becomes
`low + (high - low) * r`. This is vector arithmetic on the table, not a
substitution into the arena. The
compiler derives the width and the degree bound from the admitted arena; no
author-supplied dimension is involved. The exactness of the kernels and the
degree bound are mathematical premises of the installed evaluator, not source
theorems.

The [maintained client](../examples/projects/expression-sumcheck/README.md)
uses the shared [ring evaluator](../docs/spec/domains/ring-expressions.md)
over KoalaBear tables promoted to Ext8, or Ext8 tables directly. It exercises
interactive and Fiat-Shamir execution with extension-field challenges. The
verifier holds the tables, so this client supplies neither a commitment scheme
nor a security theorem for hidden tables.

### FRI

`LowDegree` takes a prover word, nonzero coset shifts at P and V, shared round and
query counts, and verifier randomness. Honest execution uses the same shift at
both roles; separate arguments allow callers to derive it locally. V checks
against its own shift. It requires a two-adic field of odd
characteristic, a row commitment scheme and bounded index sampling. For
`N = 2^LogSize` and `r = Rounds`, the tested degree bound is
`degree < 2^(TerminalLog + r)`. At least one fold and one query are required;
the final domain has at least twice the coefficient bound. Runtime counts must
match the static profile. The word must have exactly `N` entries.

Rows use natural domain order. A fold pairs the entries at `i` and `i + N/2`,
which represent `x` and `-x`. Each layer is committed with width one, so both
entries have independent authentication paths. All roots and final coefficients
precede all query draws; all query draws precede the openings. The final
coefficient vector may be empty (the zero polynomial), and its length must not
exceed `2^TerminalLog`.

The result contains the acceptance Boolean, query positions at both roles and
the authenticated first-layer values at V. A caller consumes these to check its
own polynomial-opening equations at exactly those positions. Successful return
means every verifier check passed; `accepted` is then `true`, and a stopped
verifier returns no result. The library does not attach a relation to an
arbitrary word. The [client](../examples/projects/fri/README.md) and independent
reference tests cover execution, compilation options, profiles, malformed
schedules, degree violations, mutated proof messages, dishonest prover folds
and terminals, and transcript event order. These tests establish no proximity
or Fiat–Shamir soundness theorem.

### AIR STARK

The [AIR modules](air/README.md) derive the constraints, scopes, opening subjects
and quotient bounds from a captured Bundle. They interpolate base-field trace
columns, construct extension-field quotient chunks, check out-of-domain claims,
and tie the original committed rows to the positions and values returned by FRI.
Vector combinations use checked native maps; protocol order stays in source.

The [recurrence project](../examples/projects/air-stark/README.md) consumes an
actual Plonky3 export through independent prover and verifier Hosts. Its small
parameters exercise a complete selected nonhiding profile. The
[accumulator-machine project](../examples/projects/accumulator-machine/README.md)
adds three-table composition, optional memory and interchangeable source LogUp
and grand-product reductions. The module guide states supported interactions,
shared degree bounds and sampling exhaustion. Security reductions for these
exact profiles remain separate obligations.

## Use a module

Imports resolve through explicit compiler module maps:

```text
use schnorr::{Schnorr};
```

```sh
zkc compile --module=schnorr=libraries/schnorr/lib.zkc \
  --module=example=examples/projects/schnorr/main.zkc \
  example::Proof --output=proof.zkpkg
```

See the [walkthrough](../docs/getting-started.md) to invoke the compiled Entry.
Project files can record these maps; see [project inputs](../docs/language/README.md#project-inputs).
Check the shared math modules with `zkc check --project=libraries/zkc/zkc.toml`.
There is no separate registry or library installation step.

## Maintain a library

Keep public exports small and helpers private. Document input ownership,
required capabilities, mathematical assumptions and the acceptance result.
Concrete domain, transcript, setup and application choices belong in the client.
Extract shared modules when multiple clients need the same contract; compiler
intrinsics and backend kernels retain their own implementation owners.

Library changes include their runnable clients and positive and negative checks
through the common compiler and Host. With built tools, run:

```sh
uv run --no-sync --locked pytest common/tests/protocol/test_source_projects.py
uv run --no-sync --locked pytest common/tests/protocol/test_expression_sumcheck.py
uv run --no-sync --locked pytest common/tests/protocol/test_native_map.py
```

These checks cover interactive and separate proof execution, compilation options,
false inputs and malformed proofs. The repository version policy applies to the
libraries; internal edits do not create compatibility modules or version bumps.

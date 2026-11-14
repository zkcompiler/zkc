# The standard library of zkc

The standard library is everything above the core library that is not a protocol. A module of
it holds no language item: it can be replaced by another module with the same signatures and no
rule of the reference notices. This document gives its layers, its naming rules, what a protocol
author imports, and the ten modules that were written in source for the worked programs. It is
one of a set: `LANGUAGE.md`, the reference of the language; `CORE-LIBRARY.md`, the core library;
this document; `conformance/`, the tests; and, at the root of the repository, `libraries/zkc/`,
the library in source, and `examples/`, the worked programs.

*State.* This document follows `LANGUAGE.md`. `zkc::sequence` is layer A, which is frozen;
`zkc::fields` and `zkc::curves` are layer A and carried. The other modules are carried, and the
comment at the head of each source says what will change in it. A library of constraint systems,
`zkc::constraint`, is designed and not written here (`LANGUAGE.md` §E).

---

## 1. Layers and dependency order

A module depends only on modules of lower or equal layers. "Rows" names the rows a layer needs
beyond the rows and the operations that the frontend applies without a declaration
(`LANGUAGE.md` §7.4); a layer that needs none runs on every target.

| Layer | Modules | Rows beyond the table | Kernels | Written here |
|---|---|---|---|---|
| 0 | the language and its tables | — | — | `LANGUAGE.md` |
| 1 core | `prelude`, `option`, `algebra`, `oracle`, `commitment`, `hash`, `layout`, `construction`, `security` | the members of the sorts; `hash.sha256`, `hash.keccak256`, `hash.shake128`, `hash.shake256`; the eight `oracle.*` rows; two group encodings | — | all (`CORE-LIBRARY.md`) |
| 2 mathematics | `sequence`, `polynomial`, `multilinear`, `coset`, `fields`, `curves`; to come: `bits`, `matrix`, `pairing` | one row per field, group and pairing of the vocabulary | optional on every function | `sequence`, `polynomial`, `multilinear`, `coset`, `fields`, `curves::bls12_381` |
| 3 encoding and hashing | `suites`; to come: `encoding`, `sponge`, `hash::poseidon2` | one permutation per hash; the suites of the catalogue until they are written in source | optional | `suites`, with one suite in source |
| 4 commitments | `merkle`, `kzg`, `proximity` | none | optional | all three |
| 5 protocol libraries | `sigma`, `sumcheck`, `gkr`, `fri`, `air`, `stark`, `inner_product` | none | — | as worked programs (`examples/`) |
| 6 deployments | `ethereum::eip4844`, `monero::bulletproofs_plus`, `spongefish` | none | — | — |

Rule: every function of layers 2 to 4 that has a kernel has a body. A target without the kernel
runs the body, or refuses the instance when a natural does not fit its count type (TY8).

**Which rows a library needs** is stated by its `= primitive("…")` bindings and its
`#[kernel("…")]` attributes and by nothing else. A package manifest lists no rows. **Identity.** A
definition of the standard library that a scheme reaches is in the scheme's deployment identity
by its content; one that no scheme reaches is in none. A change to the standard library changes
exactly the schemes that reach the changed definitions. A kernel is implementation data and is in
no identity. **Versions.** No version number is part of any identity: a package is pinned by the
digest of its source tree, and the core library by the compiler.

## 2. Naming

1. One name per notion across modules: `length`, `evaluate`, `at`, `zero`. Executable evaluation
   is `evaluate`; the specification functions on the polynomials of the formal library are
   `value` and `evaluate_at`.
2. The fixed names of a home module (`add`, `sub`, `mul`, `div`, `rem`, `pow`, `neg`, `equal`,
   `at`, `zero`, `one`) mean the operator there and nothing else. The point of a coset is
   `domain[i]`: the function `at` of `zkc::coset`.
3. A static argument that no value argument fixes is a member, not a function with written static
   arguments: `G::generator()`, `F::Order`, never `generator<G>()`.
4. A type is a static argument, never part of a name: `evaluate<F, n>`, not `evaluate_field`.
5. A module is a singular lowercase noun; a constructor has the lowercase name of its type
   (`coset(shift)`); whole words; a predicate is an adjective or a third-person verb (`paired`,
   `holds`, `contains`).
6. `pub` is what a consumer of the module writes. A record with an invariant has a field that is
   not `pub` and a constructor (`Coset`); this replaces a sealed type of the vocabulary wherever
   the record is expressible.
7. A function that can stop is a guard followed by a total operation, and says in its comment
   with which reason it stops (`get`, `slice`, `coefficients`). A decoder returns `Option`.
8. A function whose guard needs a costly test calls a function with a kernel for the test
   (`contains`), because a function that can stop has no kernel.

## 3. The prelude

In scope in every module without `use`, exactly:

| Name | What |
|---|---|
| `byte` | the alias of `index<256>` |
| `length` | the number of elements of a collection |
| `Group`, `Ring`, `PrimeOrderGroup`, `Field`, `PrimeField`, `ExtensionField`, `TwoAdicField` | the sorts |
| `Oracle`, `Pending`, `data` | the handle, the claim, the data of a handle |
| `sum`, `product`, `all`, `any`, `inner` | the ASCII spellings of `∑ ∏ ∀ ∃ ⟪ ⟫`; no declaration |

Nothing of the standard library is in the prelude.

## 4. What a protocol author imports

| Program | In the protocol file | In the deployment file |
|---|---|---|
| a sigma protocol (Schnorr, Chaum–Pedersen) | nothing: `PrimeOrderGroup`, the operators, `sample` and `draw` are language and prelude | `use zkc::curves::bls12_381::{G1}`; a suite, `use zkc::suites::{Merlin3Bls12381}` or `{HashChain}` with `use zkc::hash::{Keccak256}`; `use zkc::security::{completeness, knowledge_soundness, …}` |
| Sumcheck | for the body, `use zkc::multilinear::{fix_first, evaluate}` (`∑`, slices and `sum` are the table). For the contract: `use zkc::polynomial::{MvPoly, Poly, value, first_variable, restrict, restrict_prefix, line, extension, cube, evaluate_at}` | a field of `zkc::curves` or `zkc::fields`, a suite, `zkc::security` |
| a FRI-based scheme | `use zkc::oracle::{Rows, table}`; `use zkc::coset::{Coset, square, coefficients}`; `use zkc::polynomial`; `use zkc::proximity` | a field of `zkc::fields`; `use zkc::merkle::{Tree}` and `use zkc::hash::{Keccak256}` for the `commit` line; `use zkc::oracle::{table}` for the kind pattern; a suite; `zkc::security` |

A program does not bind a type of the vocabulary (`type Fr = primitive("…")`): it imports it.

---

## 5. The modules written in source

Each is a file of `libraries/zkc/`, which the test suite of the frontend checks (`LANGUAGE.md` §11).
They are standard library, not core. Marks as in `CORE-LIBRARY.md`.

### 5.1 `zkc::sequence` (layer 2)

| Declaration | Kind | Mark | Members |
|---|---|---|---|
| `get<T>` | function | source |  |
| `slice<T>` | function | source |  |
| `zip<A, B, n>` | function | source |  |
| `enumerate<T, n>` | function | source |  |
| `count<n>` | function | source |  |
| `reverse<T, n>` | function | source |  |
| `flatten<T, n, m>` | function | source |  |
| `low<T, m>` | function | source |  |
| `high<T, m>` | function | source |  |
| `fold<T, m>` | function | source |  |
| `hadamard<F, n>` | function | source, kernel `sequence.hadamard` |  |
| `powers<F, n>` | function | source |  |
| `batch_inverse<F, n>` | function | source, kernel `sequence.batch_inverse` |  |
| `bit_reverse<T, k>` | function | source, kernel `sequence.bit_reverse` |  |

`libraries/zkc/sequence.zkc`

```zkc
module zkc::sequence

// Standard library, layer 2. Collections. Every declaration is source; a kernel is marked.

// Checked access at a run-time position: a guard, then the total form.
pub def get<T>(values: [T], position: nat) -> T:
    guard position < length(values) else refused
    return values[position]

pub def slice<T>(values: [T], start: nat, count: nat) -> [T]:
    guard start + count <= length(values) else refused
    return values[start..start + count]

pub def zip<A, B, n: nat>(left: [A; n], right: [B; n]) -> [(A, B); n]:
    [(left[i], right[i]) for i in 0..n]

pub def enumerate<T, n: nat>(values: [T; n]) -> [(index<n>, T); n]:
    [(i, values[i]) for i in 0..n]

// The number of flags that are set.
pub def count<n: nat>(flags: [bool; n]) -> index<n + 1>: ∑ f ∈ flags, if f then 1 else 0

pub def reverse<T, n: nat>(values: [T; n]) -> [T; n]: [values[n - (i + 1)] for i in 0..n]

pub def flatten<T, n: nat, m: nat>(parts: [[T; m]; n]) -> [T; n * m] where (1 <= m):
    [parts[i / m][i % m] for i in 0..n * m]

// The two halves of a collection of 2^(m + 1) elements.
pub def low<T, m: nat>(v: [T; 2^(m + 1)]) -> [T; 2^m]: v[0..2^m]

pub def high<T, m: nat>(v: [T; 2^(m + 1)]) -> [T; 2^m]: v[2^m..2^(m + 1)]

// The halves combined with two scalars. One function folds points and scalars: every `Group`
// has a `Scalar`, and a ring, so also a field, is its own.
pub def fold<T: Group, m: nat>(v: [T; 2^(m + 1)], s: T::Scalar, t: T::Scalar) -> [T; 2^m]:
    low(v) * s + high(v) * t

#[kernel("sequence.hadamard")]
pub def hadamard<F: Field, n: nat>(left: [F; n], right: [F; n]) -> [F; n]:
    [left[i] * right[i] for i in 0..n]

pub def powers<F: Field, n: nat>(base: F) -> [F; n]: [base ^ i for i in 0..n]

#[kernel("sequence.batch_inverse")]
pub def batch_inverse<F: Field, n: nat>(values: [nonzero<F>; n]) -> [nonzero<F>; n]:
    [1 / x for x in values]

// The element at i moves to the position whose k bits are those of i in reverse order. The
// reduction modulo 2^k states the bound of the sum, which the ranges do not give.
#[kernel("sequence.bit_reverse")]
pub def bit_reverse<T, k: nat>(values: [T; 2^k]) -> [T; 2^k]:
    [values[(∑ j ∈ 0..k, ((i / 2^j) % 2) * 2^(k - (j + 1))) % 2^k] for i in 0..2^k]
```

### 5.2 `zkc::polynomial` (layer 2)

| Declaration | Kind | Mark | Members |
|---|---|---|---|
| `evaluate<F, n>` | function | source, kernel `polynomial.evaluate` |  |
| `divide_linear<F, n>` | function | source, kernel `polynomial.divide_linear` |  |
| `Polynomial<F, degree>` | interface | source | — |
| `poly<F, degree>` | module | source | `Data`, `Position`, `Row`, `answer` |
| `Poly<F, D>` | spec type | formal: `Zkc.Polynomial.Univariate` |  |
| `MvPoly<F, n, D>` | spec type | formal: `Zkc.Polynomial.Multivariate` |  |
| `evaluate_at<F, n, D>` | spec function | formal: `Zkc.Polynomial.evaluate` |  |
| `extension<F, v>` | spec function | formal: `Zkc.Polynomial.extension` |  |
| `restrict<F, n, D>` | spec function | formal: `Zkc.Polynomial.restrict` |  |
| `restrict_prefix<F, n, k, D>` | spec function | formal: `Zkc.Polynomial.restrictPrefix` |  |
| `first_variable<F, n, D>` | spec function | formal: `Zkc.Polynomial.firstVariable` |  |
| `line<F>` | spec function | formal: `Zkc.Polynomial.line` |  |
| `value<F, D>` | spec function | formal: `Zkc.Polynomial.value` |  |
| `of_coefficients<F, D>` | spec function | formal: `Zkc.Polynomial.ofCoefficients` |  |
| `cube<F, n>` | spec function | formal: `Zkc.Polynomial.cube` |  |

`libraries/zkc/polynomial.zkc`

```zkc
// Carried. Its functions are layer A; the kind `poly` is layer D. Pending: evaluation and
// interpolation over an extension.
module zkc::polynomial

// Standard library, layer 2. Polynomials in one variable by their coefficients, lowest first;
// the kind of a committed polynomial; the polynomials of the formal library, for contracts.

use zkc::oracle::{Kind, Linear}
use zkc::sequence::{reverse}

// The value at x.
#[kernel("polynomial.evaluate")]
pub def evaluate<F: Field, n: nat>(coefficients: [F; n], x: F) -> F:
    ∑ i ∈ 0..n, coefficients[i] * x ^ i

// The quotient and the remainder of the division by `X - root`.
#[kernel("polynomial.divide_linear")]
pub def divide_linear<F: Field, n: nat>(coefficients: [F; n + 1], root: F) -> ([F; n], F):
    mut carry: F = 0
    for i in 0..n collect (quotient = carry):
        carry := coefficients[n - i] + carry * root
    return (reverse(quotient), coefficients[0] + carry * root)

// A kind whose data is the coefficients of a polynomial of degree at most `degree`, and whose
// rows are its values.
pub interface Polynomial<F: Field, degree: nat> where (
    Self: Kind, Data == [F; degree + 1], Position == F, Row == F
)

pub module poly<F: Field, degree: nat>: Kind + Polynomial<F, degree> + Linear<F>:
    type Data = [F; degree + 1]
    type Position = F
    type Row = F
    def answer(data, position): evaluate(data, position)

// [formal] The polynomials of a contract, as the formal library has them.
pub spec type Poly<F: Field, D: nat> = external("Zkc.Polynomial.Univariate")
pub spec type MvPoly<F: Field, n: nat, D: nat> = external("Zkc.Polynomial.Multivariate")

pub spec def evaluate_at<F: Field, n: nat, D: nat>(
    p: MvPoly<F, n, D>, x: [F; n]
) -> F = external("Zkc.Polynomial.evaluate")
pub spec def extension<F: Field, v: nat>(
    values: [F; 2^v]
) -> MvPoly<F, v, 1> = external("Zkc.Polynomial.extension")
pub spec def restrict<F: Field, n: nat, D: nat>(
    p: MvPoly<F, n + 1, D>, r: F
) -> MvPoly<F, n, D> = external("Zkc.Polynomial.restrict")
pub spec def restrict_prefix<F: Field, n: nat, k: nat, D: nat>(
    p: MvPoly<F, n + k, D>, point: [F; k]
) -> MvPoly<F, n, D> = external("Zkc.Polynomial.restrictPrefix")
pub spec def first_variable<F: Field, n: nat, D: nat>(
    p: MvPoly<F, n + 1, D>
) -> Poly<F, D> = external("Zkc.Polynomial.firstVariable")
pub spec def line<F: Field>(a: F, b: F) -> Poly<F, 1> = external("Zkc.Polynomial.line")
pub spec def value<F: Field, D: nat>(p: Poly<F, D>, x: F) -> F = external("Zkc.Polynomial.value")
pub spec def of_coefficients<F: Field, D: nat>(
    coefficients: [F; D + 1]
) -> Poly<F, D> = external("Zkc.Polynomial.ofCoefficients")
// The points of the Boolean cube in n variables.
pub spec def cube<F: Field, n: nat>() -> [[F; n]; 2^n] = external("Zkc.Polynomial.cube")
```

### 5.3 `zkc::multilinear` (layer 2)

| Declaration | Kind | Mark | Members |
|---|---|---|---|
| `fix_first<F, v>` | function | source, kernel `multilinear.fix_first` |  |
| `evaluate<F, n>` | function | source, kernel `multilinear.evaluate` |  |
| `Multilinear<F, variables>` | interface | source | — |
| `multilinear<F, variables>` | module | source | `Data`, `Position`, `Row`, `answer` |

`libraries/zkc/multilinear.zkc`

```zkc
// Carried. Its functions are layer A; the kind `multilinear` is layer D, which is not
// frozen.
module zkc::multilinear

// Standard library, layer 2. A multilinear polynomial in v variables by its values on the
// Boolean cube, the first variable most significant.

use zkc::oracle::{Kind, Linear}
use zkc::sequence::{low, high}

// Fix the first variable.
#[kernel("multilinear.fix_first")]
pub def fix_first<F: Field, v: nat>(table: [F; 2^(v + 1)], r: F) -> [F; 2^v]:
    low(table) + (high(table) - low(table)) * r

// The value at a point.
#[kernel("multilinear.evaluate")]
pub def evaluate<F: Field, n: nat>(values: [F; 2^n], point: [F; n]) -> F:
    mut rest = values
    for i in 0..n:
        rest := fix_first(rest, point[i])
    return rest[0]

pub interface Multilinear<F: Field, variables: nat> where (
    Self: Kind, Data == [F; 2^variables], Position == [F; variables], Row == F
)

pub module multilinear<F: Field, variables: nat>: Kind + Multilinear<F, variables> + Linear<F>:
    type Data = [F; 2^variables]
    type Position = [F; variables]
    type Row = F
    def answer(data, position): evaluate(data, position)
```

### 5.4 `zkc::coset` (layer 2)

| Declaration | Kind | Mark | Members |
|---|---|---|---|
| `Coset<F, k>` | record | source |  |
| `coset<F, k>` | function | source |  |
| `at<F, k>` | function | source |  |
| `square<F, k>` | function | source |  |
| `points<F, k>` | function | source |  |
| `contains<F, k>` | function | source, kernel `coset.contains` |  |
| `interpolate<F, k>` | function | source, kernel `coset.interpolate` |  |
| `coefficients<F, t, k>` | function | source |  |
| `extend<F, k, n>` | function | source, kernel `coset.extend` |  |

`libraries/zkc/coset.zkc`

```zkc
// Layer A, carried. Pending: the lift of a coset to an extension, for additions that mix a
// field and its extension.
module zkc::coset

// Standard library, layer 2. Cosets of the two-adic subgroups of a field.

use zkc::polynomial::{evaluate}

// The coset `shift * H`, with `H` the subgroup of order 2^k; point i is `shift * w^i` for the
// generator `w = F::root(k)`. A record with a field that is not `pub`: built by `coset` only.
pub struct Coset<F: TwoAdicField, k: nat>:
    shift: nonzero<F>

pub def coset<F: TwoAdicField, k: nat>(shift: nonzero<F>) -> Coset<F, k> where (
    k <= F::TwoAdicity
):
    Coset{shift}

// `domain[i]` is this function: the point i.
pub def at<F: TwoAdicField, k: nat>(domain: Coset<F, k>, i: index<2^k>) -> nonzero<F> where (
    k <= F::TwoAdicity
):
    domain.shift * F::root(k) ^ i

// The coset of the squares: point i of `domain` and point i + 2^k both map to its point i.
pub def square<F: TwoAdicField, k: nat>(domain: Coset<F, k + 1>) -> Coset<F, k>:
    Coset{shift = domain.shift * domain.shift}

pub def points<F: TwoAdicField, k: nat>(domain: Coset<F, k>) -> [nonzero<F>; 2^k] where (
    k <= F::TwoAdicity
):
    [domain[i] for i in 0..2^k]

// Whether a value is a point of the coset.
#[kernel("coset.contains")]
pub def contains<F: TwoAdicField, k: nat>(domain: Coset<F, k>, x: F) -> bool where (
    k <= F::TwoAdicity
):
    ∃ i ∈ 0..2^k, domain[i] == x

// The coefficients of the polynomial of degree below 2^k with these values on the domain.
#[kernel("coset.interpolate")]
pub def interpolate<F: TwoAdicField, k: nat>(
    values: [F; 2^k], domain: Coset<F, k>
) -> [F; 2^k] where (k <= F::TwoAdicity):
    [(∑ i ∈ 0..2^k, values[i] / domain[i] ^ j) / 2^k for j in 0..2^k]

// The same, for a polynomial of degree below 2^t; stops with `refused` when the degree is larger.
pub def coefficients<F: TwoAdicField, t: nat, k: nat>(
    values: [F; 2^k], domain: Coset<F, k>
) -> [F; 2^t] where (t <= k, k <= F::TwoAdicity):
    all_coefficients = interpolate(values, domain)
    guard ∀ j ∈ 2^t..2^k, all_coefficients[j] == 0 else refused
    return all_coefficients[0..2^t]

// The values on `target` of the polynomial of degree below 2^k with these values on `domain`.
#[kernel("coset.extend")]
pub def extend<F: TwoAdicField, k: nat, n: nat>(
    values: [F; 2^k], domain: Coset<F, k>, target: Coset<F, n>
) -> [F; 2^n] where (k <= n, n <= F::TwoAdicity):
    [evaluate(interpolate(values, domain), target[i]) for i in 0..2^n]
```

### 5.5 `zkc::fields` (layer 2)

| Declaration | Kind | Mark | Members |
|---|---|---|---|
| `KoalaBear` | type | row `koala-bear` |  |
| `KoalaBear4` | type | row `koala-bear.ext4` |  |

`libraries/zkc/fields.zkc`

```zkc
// Layer A, carried. The vocabulary gives each field the members `Prime`, `Dimension`,
// `components` and `from_components`, and a prime field `to_nat`; this source does not
// declare them.
module zkc::fields

// Standard library, layer 2. The fields of the vocabulary, bound once: a program imports them.

// [row koala-bear] The prime field of order 2^31 - 2^24 + 1.
pub type KoalaBear = primitive("koala-bear")

// [row koala-bear.ext4] Its extension of degree four.
pub type KoalaBear4 = primitive("koala-bear.ext4")
```

### 5.6 `zkc::curves::bls12_381` (layer 2)

| Declaration | Kind | Mark | Members |
|---|---|---|---|
| `Fr` | type | row `bls12-381.fr` |  |
| `G1` | type | row `bls12-381.g1` |  |
| `G2` | type | row `bls12-381.g2` |  |
| `Gt` | type | row `bls12-381.gt` |  |
| `Bls12381` | module | row `bls12-381` |  |

`libraries/zkc/curves/bls12_381.zkc`

```zkc
// Layer A, carried. The vocabulary gives `Fr` the members of a field over its prime field and
// of a `Ring`; the scalar of a group is a `Ring`, and `Fr` is one.
module zkc::curves::bls12_381

// Standard library, layer 2. The groups and the pairing of BLS12-381, bound once.

use zkc::algebra::{Pairing}

// [rows bls12-381.fr, bls12-381.g1, bls12-381.g2, bls12-381.gt]
pub type Fr = primitive("bls12-381.fr")
pub type G1 = primitive("bls12-381.g1")
pub type G2 = primitive("bls12-381.g2")
pub type Gt = primitive("bls12-381.gt")

// [row bls12-381]
pub module Bls12381: Pairing = primitive("bls12-381")
```

### 5.7 `zkc::suites` (layer 3)

| Declaration | Kind | Mark | Members |
|---|---|---|---|
| `Merlin3Bls12381` | module | row `suite.merlin3.bls12-381.fr64be/0` |  |
| `Poseidon2KoalaBear` | module | row `suite.poseidon2-duplex.koala-bear/0` |  |
| `HashChain<H, F>` | module | source | `State`, `Challenge`, `block`, `Units`, `ChallengeUnits`, `PositionUnits`, `start`, `absorb`, `squeeze`, `challenge`, `position`, `challenge_distance`, `position_distance` |

`libraries/zkc/suites.zkc`

```zkc
// Layer C, carried and not frozen. To change: what `Suite` states and what the Fiat-Shamir
// step absorbs.
module zkc::suites

// Standard library, layer 3. Transcript suites: the catalogue suites, bound once, and one
// suite in source.

use zkc::construction::{Suite}
use zkc::hash::{Hash}
use zkc::layout::{canonical}
use zkc::option::{Option}

// [rows] Suites of the catalogue; legacy until they are written in source.
pub module Merlin3Bls12381: Suite = primitive("suite.merlin3.bls12-381.fr64be/0")
pub module Poseidon2KoalaBear: Suite = primitive("suite.poseidon2-duplex.koala-bear/0")

// [source] A hash chain over a byte hash, with challenges in a prime field. The state is one
// digest. A challenge is `F::Bytes + 16` squeezed bytes reduced modulo the order; a position
// is 16 bytes reduced modulo the bound. Not validated against a deployed transcript.
pub module HashChain<H: Hash, F: PrimeField>: Suite where (1 <= H::Size):
    module Units = canonical
    type State = [byte; H::Size]
    type Challenge = F
    nat ChallengeUnits = F::Bytes + 16
    nat PositionUnits = 16

    def start(identity): H::hash(identity)

    def absorb(state, units): H::hash(state ++ [0] ++ units)

    // The block of squeezed bytes with a counter.
    def block(state: State, counter: index<2^64>) -> State:
        H::hash(state ++ [1] ++ canonical::write_natural(counter))

    def squeeze(state):
        (H::hash(state ++ [2]), [block(state, i / H::Size)[i % H::Size] for i in 0..n])

    def challenge(units): Some(F::from_nat(∑ i ∈ 0..F::Bytes + 16, units[i] * 256^i))

    def position(units): Some((∑ i ∈ 0..16, units[i] * 256^i) % n)

    spec def challenge_distance(): F::Order / 2^(8 * (F::Bytes + 16))

    spec def position_distance(): n / 2^128
```

### 5.8 `zkc::merkle` (layer 4)

| Declaration | Kind | Mark | Members |
|---|---|---|---|
| `Tree<H, T, k>` | module | source | `ProverKey`, `VerifierKey`, `Blinding`, `Digest`, `State`, `Proof`, `sibling`, `root_of`, `paired`, `commit` (kernel `merkle.commit`), `opening`, `check` (kernel `merkle.check`) |

`libraries/zkc/merkle.zkc`

```zkc
// Layer D, carried and not frozen. To change: `Tree` takes its layout as a static argument;
// what it relies on in `Commitment`.
module zkc::merkle

// Standard library, layer 4. A Merkle tree over a byte hash, as a commitment scheme for a table.

use zkc::commitment::{Commitment}
use zkc::hash::{Hash}
use zkc::layout::{canonical}
use zkc::oracle::{table}

// A binary tree over the 2^k rows of a table. A row is hashed in the canonical layout. The
// scheme has no key and does not hide. `commit table<_, _> with Tree<Keccak256>` leaves `T`
// and `k` to be found from the kind.
pub module Tree<H: Hash, T, k: nat>: Commitment<table<T, 2^k>>:
    type ProverKey = ()
    type VerifierKey = ()
    type Blinding = ()
    type Digest = [byte; H::Size]
    // Every level, the leaves first; the root is the last node.
    type State = [[byte; H::Size]; 2^(k + 1) - 1]
    // One path per position: the sibling at each level, from the leaves up.
    type Proof<n: nat> = [[[byte; H::Size]; k]; n]

    spec def paired(prover_key, verifier_key): true

    #[kernel("merkle.commit")]
    def commit(key, data, blinding):
        mut level = [H::hash(canonical::write<T>(row)) for row in data]
        mut nodes = level
        for j in 0..k:
            level := [H::hash(level[2 * i] ++ level[2 * i + 1]) for i in 0..2^(k - j - 1)]
            nodes := nodes ++ level
        return (level[0], nodes)

    // The sibling, at level j, of the node above a position: level j starts at
    // 2^(k + 1) - 2^(k - j + 1) and has 2^(k - j) nodes.
    def sibling<j: nat>(state: State, position: index<2^k>) -> Digest where (j + 1 <= k):
        state[
            2^(k + 1) - 2^(k - j + 1) + 2 * (position / 2^(j + 1)) + (1 - (position / 2^j) % 2)
        ]

    def opening(key, state, positions):
        [[sibling<j>(state, positions[q]) for j in 0..k] for q in 0..n]

    // The root that a row, its position and a path give.
    def root_of(row: T, position: index<2^k>, path: [Digest; k]) -> Digest:
        mut node = H::hash(canonical::write<T>(row))
        for j in 0..k:
            node := (
                if (position / 2^j) % 2 == 0 then H::hash(node ++ path[j])
                else H::hash(path[j] ++ node)
            )
        return node

    #[kernel("merkle.check")]
    def check(key, digest, positions, rows, proof):
        ∀ q ∈ 0..n, root_of(rows[q], positions[q], proof[q]) == digest
```

### 5.9 `zkc::kzg` (layer 4)

| Declaration | Kind | Mark | Members |
|---|---|---|---|
| `powers<E, n>` | function | source |  |
| `verifier_key<E>` | function | source |  |
| `Kzg<E, degree>` | module | source | `ProverKey`, `VerifierKey`, `Blinding`, `Digest`, `State`, `Proof`, `paired`, `commit` (kernel `kzg.commit`), `opening` (kernel `kzg.open`), `check` (kernel `kzg.check`) |

`libraries/zkc/kzg.zkc`

```zkc
// Layer D, carried and not frozen. To change: one key serves several shapes
// (`Kzg<E, MaxDegree>`); `Commitment` gets a combination for the linear kind `poly`, and
// `paired` becomes a hypothesis.
module zkc::kzg

// Standard library, layer 4. The KZG commitment scheme for a polynomial, over a pairing.

use zkc::algebra::{Pairing}
use zkc::commitment::{Commitment}
use zkc::polynomial::{poly, divide_linear}

// The keys of a setup with the secret `tau`: its powers in the first group, `tau` in the second.
pub def powers<E: Pairing, n: nat>(tau: nonzero<E::Scalar>) -> [E::G1; n]:
    [E::G1::generator() * tau ^ i for i in 0..n]

pub def verifier_key<E: Pairing>(tau: nonzero<E::Scalar>) -> E::G2: E::G2::generator() * tau

// `commit poly<_, _> with Kzg<E>(prover_key = sites.x, verifier_key = sites.y)` leaves `degree`
// to be found from the kind.
pub module Kzg<E: Pairing, degree: nat>: Commitment<poly<E::Scalar, degree>>:
    type ProverKey = [E::G1; degree + 1]
    type VerifierKey = E::G2
    type Blinding = ()
    type Digest = E::G1
    type State = [E::Scalar; degree + 1]
    // One quotient commitment per position.
    type Proof<n: nat> = [E::G1; n]

    // The prover's key is the powers of the secret that the verifier's key holds.
    spec def paired(prover_key, verifier_key):
        prover_key[0] == E::G1::generator() and ∀ i ∈ 0..degree, (
            E::pair(prover_key[i + 1], E::G2::generator()) == E::pair(prover_key[i], verifier_key)
        )

    #[kernel("kzg.commit")]
    def commit(key, data, blinding): (⟪key, data⟫, data)

    #[kernel("kzg.open")]
    def opening(key, state, positions):
        [⟪key[0..degree], divide_linear(state, z).0⟫ for z in positions]

    #[kernel("kzg.check")]
    def check(key, digest, positions, rows, proof):
        ∀ q ∈ 0..n, (
            E::pair(digest - E::G1::generator() * rows[q], E::G2::generator())
                == E::pair(proof[q], key - E::G2::generator() * positions[q])
        )
```

### 5.10 `zkc::proximity` (layer 4)

| Declaration | Kind | Mark | Members |
|---|---|---|---|
| `fold_error<F>` | spec function | formal: `Zkc.Proximity.foldError` |  |
| `query_error<F>` | spec function | formal: `Zkc.Proximity.queryError` |  |

`libraries/zkc/proximity.zkc`

```zkc
// Layer B, carried: bounds of the formal library.
module zkc::proximity

// Standard library, layer 4. The bounds of proximity testing, as the formal library has them.

// [formal]
pub spec def fold_error<F: Field>(
    log_size: nat, log_degree: nat
) -> rational = external("Zkc.Proximity.foldError")
pub spec def query_error<F: Field>(
    log_size: nat, log_degree: nat, queries: nat
) -> rational = external("Zkc.Proximity.queryError")
```

**Notes.** `zkc::sequence::fold` is the one function that folds points and scalars. `bit_reverse`
reduces its index modulo `2^k`: the reduction states a bound that the range arithmetic of TY8
does not derive from a sum of bits. `zkc::coset::interpolate` and `extend` are written as their
definitions (a sum over the domain); their kernels are the fast transforms. `zkc::merkle::Tree` is
a tree over a byte hash: a row is hashed in the canonical layout through the generated writer
`canonical::write<T>`; a tree over a field-native hash needs the permutation row and the sponge of
layer 3, which are not written. `zkc::kzg::Kzg` states `paired` with pairings and has the two keys
as types. `zkc::suites::HashChain` is one suite in source; it was not compared with a deployed
transcript. The suites of the catalogue are modules bound once to a row, until they are written
in source.

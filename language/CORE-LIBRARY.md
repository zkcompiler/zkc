# The core library of zkc

The core library is the set of modules that hold a language item or a name that the vocabulary
provides (`LANGUAGE.md` §2.5). It is designed with the language, is shipped with the compiler and
has the version of the language: it cannot change without the reference changing. It has nine
modules. Eight are source files, given here in full; the ninth, `zkc::security`, has no source
file: its names are entries of the vocabulary. It is one of a set: `LANGUAGE.md`, the reference
of the language; this document; `STANDARD-LIBRARY.md`, the libraries above it; `conformance/`,
the tests; and, at the root of the repository, `libraries/zkc/`, the library in source, and
`examples/`, the worked programs.

*State.* This document follows `LANGUAGE.md`. `zkc::prelude`, `zkc::option`, `zkc::algebra` and
the interfaces of `zkc::hash` are layer A, which is frozen. The other modules are carried: each
of their sections opens with a note, and the comment at the head of each source says what will
change in it. Every module resolves its names against the frozen ones; the carried modules are
not typed until they are redone. §1 gives the rows of the vocabulary as `LANGUAGE.md` §7.4 has
them.

| Module | Holds | Items |
|---|---|---|
| `zkc::prelude` | what is in scope without `use`: `byte`, `length`, the sorts, `Oracle`, `Pending`, `data` | `length` |
| `zkc::option` | `Option<T>` | `Option` |
| `zkc::algebra` | the sorts; `Pairing` | the seven sorts |
| `zkc::oracle` | kinds, handles, claims, the kind `table` | `Kind`, `Rows`, `Linear`, `Derived`, `Oracle`, `Pending`, `data`, `pending`, `lower` |
| `zkc::commitment` | what realizes a primitive kind | `Commitment` |
| `zkc::hash` | byte hashes; extendable-output functions | `Hash` |
| `zkc::layout` | how a value is written as units | `Layout`, `canonical` |
| `zkc::construction` | how a transcript becomes challenges | `Suite` |
| `zkc::security` | the properties and the models of goals | entries of the vocabulary |

**Marks.** Every public declaration has one mark:

- **item**: a language item (`LANGUAGE.md` §2.4): the sorts, and sixteen other names;
- *row `name`*: bound to a row of the vocabulary with `primitive("name")`; for a function member
  of a sort, the row that the frontend applies;
- *source*: a definition with a body, or an interface; *source, kernel `name`*: with a kernel
  (FN5);
- *sort*: an interface that only the vocabulary implements;
- *formal*: bound to the formal library with `external`;
- *table*: a name of a fixed table of the language (the sorts in the prelude).

A law is listed among the members of its interface: it is an obligation of every implementing
module, typed at every instance the tools check (SP10).

**How it is checked.** The sources below are the files of `libraries/zkc/`, which the test suite of
the frontend checks (`LANGUAGE.md` §11).

---

## 1. The vocabulary, as the tools read it

The vocabulary is defined in the formal library and printed for the tools. The tools read it
from tables written by hand: the types and modules below, the 26 rows that the
frontend applies without a declaration (§1.4; `LANGUAGE.md` §7.4), and the rows that a
declaration of a library binds. A row has one of three kinds: pure, restricted (a function on a
domain, with the pure row that decides the domain) or sampling. The operations on naturals, on
`bool` and on sequences as such are not rows of the vocabulary: the core owns them (§1.4).

### 1.1 Types

A type of the vocabulary is bound once, in the standard library (`zkc::fields`, `zkc::curves`);
a program imports it. The tools check, for each type and each of its sorts, that every type and
natural member of the sort is given and that the conditions of the sort hold.

| Row | Bound as | Sorts | Type members | Natural members |
|---|---|---|---|---|
| `koala-bear` | `zkc::fields::KoalaBear` | `Group`, `Ring`, `Field`, `PrimeField`, `TwoAdicField` | `Scalar` = itself, `Prime` = itself | `Order` = 2130706433, `Characteristic` = 2130706433, `Dimension` = 1, `Bytes` = 4, `TwoAdicity` = 24 |
| `koala-bear.ext4` | `zkc::fields::KoalaBear4` | `Group`, `Ring`, `Field`, `ExtensionField`, `TwoAdicField` | `Scalar` = itself, `Prime` = `KoalaBear`, `Base` = `KoalaBear` | `Order` = 206107…3121 (124 bits), `Characteristic` = 2130706433, `Dimension` = 4, `Degree` = 4, `TwoAdicity` = 26 |
| `bls12-381.fr` | `zkc::curves::bls12_381::Fr` | `Group`, `Ring`, `Field`, `PrimeField`, `TwoAdicField` | `Scalar` = itself, `Prime` = itself | `Order` = 524358…4513 (255 bits), `Characteristic` = 524358…4513 (255 bits), `Dimension` = 1, `Bytes` = 32, `TwoAdicity` = 32 |
| `bls12-381.g1` | `zkc::curves::bls12_381::G1` | `Group`, `PrimeOrderGroup` | `Scalar` = `Fr` | `Order` = 524358…4513 (255 bits) |
| `bls12-381.g2` | `zkc::curves::bls12_381::G2` | `Group`, `PrimeOrderGroup` | `Scalar` = `Fr` | `Order` = 524358…4513 (255 bits) |
| `bls12-381.gt` | `zkc::curves::bls12_381::Gt` | `Group` | `Scalar` = `Fr` | `Order` = 524358…4513 (255 bits) |

`nonzero<F>` is a type of the vocabulary as well: the nominal type `nonzero` at a field `F`
(`LANGUAGE.md` §7.3). It is bound by no declaration: the reserved type names it.

*Open (`LANGUAGE.md` §10.2 item 35).* The table gives no generator for the member `root` of
`TwoAdicField` (the row `field.root`) at `koala-bear.ext4` and at `bls12-381.fr`.

**Default representatives.** For each sort the vocabulary states a default representative: the
type at which a default instance checks a declaration whose type parameter has that sort
(`LANGUAGE.md` SP7). The printed vocabulary is to carry the column; until it does, these
are the representatives, taken by one rule (the type with the fewest sorts besides, the first
of the table above among equals):

| Sort | Default representative |
|---|---|
| `Group` | `bls12-381.gt` |
| `PrimeOrderGroup` | `bls12-381.g1` |
| `Ring`, `Field`, `PrimeField`, `TwoAdicField` | `koala-bear` |
| `ExtensionField` | `koala-bear.ext4` |

### 1.2 Modules

| Row | Bound as | Implements | Members that the vocabulary gives |
|---|---|---|---|
| `bls12-381` | `zkc::curves::bls12_381::Bls12381` | `Pairing` | `Scalar` = `Fr`, `G1` = `G1`, `G2` = `G2`, `Target` = `Gt` |
| `hash.sha256` | `zkc::hash::Sha256` | `Hash` | `Size` = 32 |
| `hash.keccak256` | `zkc::hash::Keccak256` | `Hash` | `Size` = 32 |
| `hash.shake128` | `zkc::hash::Shake128` | `ExtendableOutput` | — |
| `hash.shake256` | `zkc::hash::Shake256` | `ExtendableOutput` | — |
| `suite.merlin3.bls12-381.fr64be/0` | `zkc::suites::Merlin3Bls12381` | `Suite` | `Challenge` = `Fr`, `ChallengeUnits` = 64, `PositionUnits` = 16 |
| `suite.poseidon2-duplex.koala-bear/0` | `zkc::suites::Poseidon2KoalaBear` | `Suite` | `Challenge` = `KoalaBear4`, `ChallengeUnits` = 4, `PositionUnits` = 1 |
| `suite.schnorr-signature` | `— (a project binds it)` | — | `Challenge` = `Fr`, `ChallengeUnits` = 64, `PositionUnits` = 16 |
| `suite.ml-dsa` | `— (a project binds it)` | — | `ChallengeUnits` = 32, `PositionUnits` = 8 |

*Open (`LANGUAGE.md` §10.2 item 30).* The table gives each suite of the catalogue three members,
and `Suite` declares more (§2.8): the module `Units`, the type `State` and the functions. What
the vocabulary gives for them is settled with layer C.

### 1.3 Rows that a declaration of the core library binds

| Row | Declaration | What it is |
|---|---|---|
| `group.from_bytes` | `zkc::layout::canonical::read_group` | group encoding |
| `group.to_bytes` | `zkc::layout::canonical::write_group` | group encoding |
| `hash.keccak256` | `zkc::hash::Keccak256` | module |
| `hash.sha256` | `zkc::hash::Sha256` | module |
| `hash.shake128` | `zkc::hash::Shake128` | module |
| `hash.shake256` | `zkc::hash::Shake256` | module |
| `oracle.claim` | `zkc::oracle::Pending` | sealed type |
| `oracle.claim_handle` | `zkc::oracle::handle` | oracle |
| `oracle.claim_position` | `zkc::oracle::position` | oracle |
| `oracle.claim_row` | `zkc::oracle::row` | oracle |
| `oracle.data` | `zkc::oracle::data` | oracle |
| `oracle.handle` | `zkc::oracle::Oracle` | sealed type |
| `oracle.lower` | `zkc::oracle::lower` | oracle |
| `oracle.pending` | `zkc::oracle::pending` | oracle |
| `seq.length` | `zkc::prelude::length` | collection; an operation that the core owns (§1.4), which the declaration names as another names a row |

The function members of the sorts are rows too, applied where a program writes `T::m(…)`:
`group.generator` (`generator`), `field.from_nat` (`from_nat`), `field.components` (`components`), `field.from_components` (`from_components`), `field.to_nat` (`to_nat`), `field.embed` (`embed`), `field.coefficients` (`coefficients`), `field.from_coefficients` (`from_coefficients`), `field.root` (`root`), `pairing.pair` (`pair`).

### 1.4 Rows and operations that the frontend applies without a declaration

`LANGUAGE.md` §7.4 is normative for both tables; they are printed here as the tools read them.
The rows of the vocabulary, 26:

| Family | Rows | Kind |
|---|---|---|
| field | `field.add`, `field.sub`, `field.mul`, `field.neg`, `field.inverse`, `field.pow`, `field.equal` | pure |
| `nonzero<F>` | `field.nonzero`; `field.is_nonzero`; `field.from_nonzero` | `field.nonzero` is restricted, with the domain row `field.is_nonzero`; the two others are pure |
| ring | `ring.mul`, `ring.pow` | pure |
| group | `group.zero`, `group.add`, `group.sub`, `group.neg`, `group.scale`, `group.equal` | pure |
| collection | `seq.add`, `seq.sub`, `seq.scale`, `seq.sum`, `seq.product`, `seq.inner`, `seq.equal` | pure |
| sampling | `law.uniform`, at a type that is a law (TY15); one row also at a tuple or a sized collection of laws | sampling |

`field.mul`, `field.neg` and `field.pow` are also rows at the type `nonzero<F>`, and
`field.inverse` takes and gives a `nonzero<F>`. A number literal of a field or of a ring is no
row: it is a literal of the nominal type, whose value is `from_nat` of the number (TY6).

The operations that the core owns, 25. They are not rows: their meaning is fixed by the core.

| Family | Operations | With a domain |
|---|---|---|
| natural | `nat.add`, `nat.sub`, `nat.mul`, `nat.div`, `nat.rem`, `nat.pow`, `nat.equal`, `nat.less` | `nat.sub`, `nat.div`, `nat.rem` |
| `bool` | `bool.and`, `bool.or`, `bool.not`, `bool.equal` | — |
| sequence | `seq.at`, `seq.slice`, `seq.concat`, `seq.fill`, `seq.length` | `seq.at`, `seq.slice` |
| refining | `seq.sized`, `nat.below` | both |
| widening | `seq.unsized`, `fin.to_nat`, `fin.widen` | — |
| data | `local.make`, `local.get`, `local.variant` | — |

---

## 2. The modules

### 2.1 `zkc::prelude`

| Declaration | Kind | Mark | Members |
|---|---|---|---|
| `Group` | re-export of `zkc::algebra` | **item**, a sort | |
| `Ring` | re-export of `zkc::algebra` | **item**, a sort | |
| `PrimeOrderGroup` | re-export of `zkc::algebra` | **item**, a sort | |
| `Field` | re-export of `zkc::algebra` | **item**, a sort | |
| `PrimeField` | re-export of `zkc::algebra` | **item**, a sort | |
| `ExtensionField` | re-export of `zkc::algebra` | **item**, a sort | |
| `TwoAdicField` | re-export of `zkc::algebra` | **item**, a sort | |
| `Oracle` | re-export of `zkc::oracle` | **item** | |
| `Pending` | re-export of `zkc::oracle` | **item** | |
| `data` | re-export of `zkc::oracle` | **item** | |
| `byte` | type | source |  |
| `length<T>` | function | **item**, row `seq.length` |  |

In scope without `use` are the twelve names of this module and the five functions of the fixed
table, `sum`, `product`, `all`, `any`, `inner`, which have no declaration: seventeen names. The
prelude holds the names that the syntax and the fixed tables of the language produce or require
(B8): the sorts, re-exported as the closed table they are, and the types that a statement of the
language produces with their eliminator (`send … as oracle` produces an `Oracle`, `query … deferred` a `Pending`, and `data`
reads a handle). A kind is a choice and is imported; `Option` is imported.

`libraries/zkc/prelude.zkc`

```zkc
module zkc::prelude

// Core library. In scope in every module without `use`: these names, and the functions `sum`,
// `product`, `all`, `any` and `inner` of the fixed table, which have no declaration. The prelude
// holds the names that the syntax and the fixed tables of the language produce or require.

// [table] The sorts: a closed set, declared in `zkc::algebra` so that their members can be read.
pub use zkc::algebra::{
    Group, Ring, PrimeOrderGroup, Field, PrimeField, ExtensionField, TwoAdicField
}

// [item] What `send … as oracle`, `query … deferred` and `data(h)` produce and read.
pub use zkc::oracle::{Oracle, Pending, data}

// [source] A byte. `b"…"` and `hex"…"` are `[byte; k]`.
pub type byte = index<256>

// [item] [row seq.length] The number of elements of a collection; a term of the fact calculus.
pub def length<T: linear>(values: [T]) -> nat = primitive("seq.length")
```

### 2.2 `zkc::option`

| Declaration | Kind | Mark | Members |
|---|---|---|---|
| `Option<T>` | variant | **item**, source |  |

`Option` is an item because steps and generators read it: a reader of a layout (TY14) and a
decoder of a suite (SC5) return it, so does the generated `L::read<T>`, and the field of `P::Run`
for an event in a choice is an `Option` (§8 of the reference).

`libraries/zkc/option.zkc`

```zkc
module zkc::option

// Core library.

// [item] [source] A value or nothing: what a reader of a layout and a decoder of a suite return.
pub enum Option<T>:
    Some(T)
    None
```

### 2.3 `zkc::algebra`

| Declaration | Kind | Mark | Members |
|---|---|---|---|
| `Group` | interface | **item**, sort: only the vocabulary implements it | type `Scalar`, natural `Order` |
| `Ring` | interface | **item**, sort: only the vocabulary implements it | natural `Characteristic`, `from_nat` (row `field.from_nat`) |
| `PrimeOrderGroup` | interface | **item**, sort: only the vocabulary implements it | `generator` (row `group.generator`) |
| `Field` | interface | **item**, sort: only the vocabulary implements it | type `Prime`, natural `Dimension`, `components` (row `field.components`), `from_components` (row `field.from_components`) |
| `PrimeField` | interface | **item**, sort: only the vocabulary implements it | natural `Bytes`, `to_nat` (row `field.to_nat`) |
| `ExtensionField` | interface | **item**, sort: only the vocabulary implements it | type `Base`, natural `Degree`, `embed` (row `field.embed`), `coefficients` (row `field.coefficients`), `from_coefficients` (row `field.from_coefficients`) |
| `TwoAdicField` | interface | **item**, sort: only the vocabulary implements it | natural `TwoAdicity`, `root` (row `field.root`) |
| `Pairing` | interface | source | type `Scalar`, type `G1`, type `G2`, type `Target`, `pair` (row `pairing.pair`), law `left`, law `right`, law `nondegenerate` |

The sorts form one hierarchy and state their laws (`LANGUAGE.md` SP3). A `Group` is an abelian
group written additively with a right action of its `Scalar`, which is a `Ring`; it is finite,
with `Order` elements. A `Ring` is a `Group` that is its own `Scalar`, commutative, with the unit
`1`; it carries what is a ring's: number literals, `from_nat`, `Characteristic` and `^` by a
natural. A `Field` is a `Ring` in which every `nonzero` has an inverse, and it states its view over
its prime field: `Prime`, `Dimension`, `components` and `from_components`; a prime field is its
own `Prime`, with dimension 1. `ExtensionField` is one step of a tower. The laws are not written
as `law` members: the vocabulary gives each type a model in the formal library that is an
instance of the structure with these laws, and the operators are the operations of that
instance. A module that interprets a signature without satisfying them (a degree) is not of a
sort. What a program writes:

| For | Write |
|---|---|
| the number of elements of a field or a group | `F::Order`, `G::Order`; a charge is `R::Degree / F::Order` |
| the inverse | `1 / x`, with `x: nonzero<F>`; it is a `nonzero<F>` |
| one half | `1 / 2`, which types exactly when `2` is not a multiple of the characteristic |
| "the characteristic is not two" | `where (F::Characteristic != 2)`; implied by `TwoAdicField` |
| the generator | `G::generator()` |
| a natural or an index as a field element | `F::from_nat(n)` |
| the identity of a group | `0` |
| a uniform group element | `sample G`, `draw G …` (not derived by a suite: SC5) |
| the representative of an element of a prime field | `F::to_nat(x)`, an `index<F::Order>` |
| the coordinates of a field element over its prime field | `F::components(x)`, a `[F::Prime; F::Dimension]` |
| a vector over a ring | a `[R; n]`: it has `+`, `-`, `* scalar` and `⟪ ⟫` |

Group notation is additive and the scalar stands on the right (`LANGUAGE.md` §3.5). `Pairing` is
an ordinary interface: a pairing of the vocabulary is a module, `zkc::curves::bls12_381::Bls12381`,
and its laws are typed there.

`libraries/zkc/algebra.zkc`

```zkc
module zkc::algebra

// Core library. A sort is an interface that only the vocabulary implements: `T: S` holds when
// the vocabulary gives the type `T` the sort `S`. In a sort, `Self` is `T`, and a member is
// reached as `T::m`. The operators of a sort are those of the fixed table; their rows have no
// declaration. The sorts form one hierarchy: a `Group` has a `Scalar` that is a `Ring`; a
// `Ring` is a `Group` that is its own `Scalar`; a `Field` is a `Ring` with division. The laws
// of a sort are stated in the comment of its interface and in `LANGUAGE.md` SP3; they are not
// `law` members, because the vocabulary gives each type a model that satisfies them.

// [item] An abelian group written additively, with a right action of its `Scalar`, a ring:
// `x * 1 == x`, `x * (a * b) == (x * a) * b`, `(x + y) * a == x * a + y * a`,
// `x * (a + b) == x * a + x * b`. It has `+`, `-`, prefix `-`, `==`, the literal `0`, `x * a`
// with `a: Scalar`, `∑`, `⟪xs, as⟫`. A type of the sort is finite and is a law. A sized
// collection of elements of a `Group` is a `Group` with the same `Scalar`.
pub interface Group:
    type Scalar: Ring
    // The number of elements.
    nat Order

// [item] A ring: a `Group` that is its own `Scalar`, with a commutative multiplication that has the
// unit `1`. What is a ring's is here: `*`, `^` by a natural, `∏`, the literal `1` and number
// literals, `Characteristic` and `from_nat`. An interpretation of a signature that does not
// satisfy these laws, such as a degree, is not a `Ring`.
pub interface Ring where (Self: Group, Self::Scalar == Self):
    nat Characteristic
    // [row field.from_nat] The image of a natural; total. A number literal below the
    // characteristic is this image.
    def from_nat(n: nat) -> Self

// [item] A group of prime order with a generator.
pub interface PrimeOrderGroup where (
    Self: Group, Self::Scalar: PrimeField, Self::Order == Self::Scalar::Characteristic
):
    // [row group.generator]
    def generator() -> Self

// [item] A field: a `Ring` in which every `nonzero` has an inverse. It adds `/` by a
// `nonzero<Self>`, and `nonzero<Self>` is a type. A field states its view over its prime field:
// an element is `Dimension` components in `Prime`.
pub interface Field where (Self: Ring):
    // The prime field, and the dimension over it.
    type Prime: PrimeField
    nat Dimension
    // [rows field.components, field.from_components] Total, and inverse to each other.
    def components(x: Self) -> [Prime; Dimension]
    def from_components(c: [Prime; Dimension]) -> Self

// [item] A field of prime order: its elements are the naturals below `Order`. It is its own `Prime`,
// with dimension 1.
pub interface PrimeField where (
    Self: Field, Self::Order == Self::Characteristic, Self::Prime == Self, Self::Dimension == 1
):
    // The length of the canonical byte encoding.
    nat Bytes
    // [row field.to_nat] The representative below the order.
    def to_nat(x: Self) -> index<Self::Order>

// [item] A finite extension, one step of a tower: an element is `Degree` coefficients over `Base`.
pub interface ExtensionField where (Self: Field, Base::Characteristic == Self::Characteristic):
    type Base: Field
    nat Degree
    // [row field.embed] Applied to a `nonzero<Base>` it gives a `nonzero<Self>`: a result range
    // of the row, which a signature in source does not write.
    def embed(x: Base) -> Self
    // [rows field.coefficients, field.from_coefficients]
    def coefficients(x: Self) -> [Base; Degree]
    def from_coefficients(c: [Base; Degree]) -> Self

// [item] A field with a subgroup of order 2^TwoAdicity.
pub interface TwoAdicField where (Self: Field, 1 <= TwoAdicity):
    nat TwoAdicity
    // [row field.root] A generator of the subgroup of order 2^k.
    def root(k: index<TwoAdicity + 1>) -> nonzero<Self>

// An ordinary interface: a pairing of the vocabulary is a module, bound in `zkc::curves`.
pub interface Pairing where (
    G1::Scalar == Scalar, G2::Scalar == Scalar, Target::Scalar == Scalar
):
    type Scalar: PrimeField
    type G1: PrimeOrderGroup
    type G2: PrimeOrderGroup
    type Target: Group
    // [row pairing.pair]
    def pair(a: G1, b: G2) -> Target
    law left(a: G1, b: G2, s: Scalar): pair(a * s, b) == pair(a, b) * s
    law right(a: G1, b: G2, s: Scalar): pair(a, b * s) == pair(a, b) * s
    law nondegenerate(): pair(G1::generator(), G2::generator()) != 0
```

### 2.4 `zkc::oracle`

*State: layer D, carried; not frozen. The interface `Derived` cannot be implemented as written
(its `Open` can neither read nor consume its claims, and no module satisfies the law `opened`);
the direction of its redesign is settled (`LANGUAGE.md` §6.10).*

| Declaration | Kind | Mark | Members |
|---|---|---|---|
| `Kind` | interface | **item**, source | type `Data`, type `Position`, type `Row`, `answer` |
| `Rows<T, n>` | interface | **item**, source | — |
| `Linear<F>` | interface | **item**, source | law `linear` |
| `Derived` | interface | **item**, source | type `Lower`, type `Residual`, spec `settled`, protocol `Send`, protocol `Open`, law `opened` |
| `Oracle<K>` | type | **item**, row `oracle.handle` |  |
| `Pending<K>` | type | **item**, row `oracle.claim` |  |
| `data<K>` | function | **item**, row `oracle.data` |  |
| `pending<K>` | function | **item**, row `oracle.pending` |  |
| `lower<K>` | function | **item**, row `oracle.lower` |  |
| `handle<K>` | spec function | row `oracle.claim_handle` |  |
| `position<K>` | spec function | row `oracle.claim_position` |  |
| `row<K>` | spec function | row `oracle.claim_row` |  |
| `holds<K>` | spec function | source |  |
| `table<T, rows>` | module | source | `Data`, `Position`, `Row`, `answer` |

The shape of a kind is in its static arguments. `Rows` has no member of its own: its `where`
requires `Self: Kind` and fixes the three types. `holds` is a definition; `table` is a module in
source, and what makes a kind primitive is that it does not implement `Derived`. The kinds `poly`
and `multilinear` are declared the same way in the standard library, because their `answer` is
the evaluation function of those modules. `lower` has no default instance (no module of this
library implements `Derived`) and is resolved for names only.

`libraries/zkc/oracle.zkc`

```zkc
// Layer D, carried and not frozen. To change: in `Derived`, `Open` receives the lower handles,
// the positions and the rows; the law `opened` is replaced by a `reduces` contract of `Open`;
// `Residual` takes the size of the block; a claim is one handle, one position and one row;
// the port `data` of `Send` gets a name that does not hide the name `data` of the
// prelude.
module zkc::oracle

// Core library.

// [item] What an oracle of the kind holds and answers. The shape of a kind is in its static
// parameters, so `answer` is total and neither a send nor a query tests anything.
pub interface Kind:
    type Data
    type Position
    type Row
    def answer(data: Data, position: Position) -> Row

// [item] A kind of `n` rows of type `T`: a position is an index. The interface of an `oracle def`.
pub interface Rows<T, n: nat> where (Self: Kind, Data == [T; n], Position == index<n>, Row == T)

// [item] A kind whose handles combine with `+`, `-` and `* scalar`.
pub interface Linear<F: Field> where (Self: Kind, Data: Group, Data::Scalar == F, Row == F):
    law linear(a: Data, b: Data, c: F, p: Position):
        answer(a + b * c, p) == answer(a, p) + answer(b, p) * c

// [item] A derived kind: what a handle stands for, how its data is sent, how a block of claims
// is opened, and what an opening leaves.
pub interface Derived where (Self: Kind):
    type Lower
    type Residual
    spec def settled(residual: Residual) -> bool
    protocol Send roles(H, R)(data: Data @H) -> lower: Lower @H -> R
    protocol Open<n: nat> roles(H, R)(
        claims: [Pending<Self>; n] @(H, R)
    ) -> residual: Residual @(H, R)
    law opened<n: nat>(claims: [Pending<Self>; n], residual: Residual):
        settled(residual) == ∀ c ∈ claims, holds(c)

// [item] [row oracle.handle] The handle of an oracle. Sealed.
pub type Oracle<K: Kind> = primitive("oracle.handle", K)

// [item] [row oracle.claim] A row told and not yet proved. Linear and sealed: formed by a
// deferred query, by `pending` and by `h at p == v`; consumed by `open`, `return`, a port and
// `collect`.
pub type Pending<K: Kind> = primitive("oracle.claim", K)

// [item] [row oracle.data] The data, at a holder.
pub def data<K: Kind>(h: Oracle<K>) -> K::Data = primitive("oracle.data")

// [item] [row oracle.pending] `h at p == v` inside `open` is this call.
pub def pending<K: Kind>(
    h: Oracle<K>, position: K::Position, row: K::Row
) -> Pending<K> = primitive("oracle.pending")

// [item] [row oracle.lower] The handles that a handle of a derived kind stands for; callable in
// the module of `K` only.
pub def lower<K: Kind + Derived>(h: Oracle<K>) -> K::Lower = primitive("oracle.lower")

// [rows] Specification functions on a claim: they read it and never consume it.
pub spec def handle<K: Kind>(claim: Pending<K>) -> Oracle<K> = primitive("oracle.claim_handle")
pub spec def position<K: Kind>(
    claim: Pending<K>
) -> K::Position = primitive("oracle.claim_position")
pub spec def row<K: Kind>(claim: Pending<K>) -> K::Row = primitive("oracle.claim_row")

// [source] The claim is true of the data.
pub spec def holds<K: Kind>(claim: Pending<K>) -> bool:
    row(claim) == K::answer(data(handle(claim)), position(claim))

// [source] The primitive kind of a table of `rows` rows. A kind is primitive when it does not
// implement `Derived`; a scheme then names a `Commitment` for it.
pub module table<T, rows: nat>: Kind + Rows<T, rows>:
    type Data = [T; rows]
    type Position = index<rows>
    type Row = T
    def answer(data, position): data[position]
```

### 2.5 `zkc::commitment`

*State: layer D, carried; not frozen. `Commitment` is to be completed: a combination for a
`Linear` kind, coins for an opening, binding, extractability and hiding as properties that a
goal names, `paired` of the pinned keys as a hypothesis of receipts. The site of a key has
exactly the type of the key (SC5).*

| Declaration | Kind | Mark | Members |
|---|---|---|---|
| `Commitment<K>` | interface | **item**, source | type `ProverKey`, type `VerifierKey`, type `Blinding`, type `Digest`, type `State`, type `Proof`, spec `paired`, `commit`, `opening`, `check`, law `opens` |

A `commit` line reads `commit table<_, _> with Tree<Keccak256>` or
`commit poly<_, _> with Kzg<Bls12381>(prover_key = sites.prover_key, verifier_key =
sites.verifier_key)`: the configuration of a scheme is its static arguments, those that the line
leaves out are solved from the kind (SC5), and the only arguments in parentheses are the two keys,
each bound to a pinned site when its type is not `()`. The law `opens` is the completeness of the
scheme. That a scheme is binding, and for which bound, is a property of the formal library stated
of the module; the commit theorem takes it as its premise and the receipt lists it. The member
that produces a proof is named `opening`: `open` is a reserved word. `Proof` has a static
parameter, the number of rows proved.

`libraries/zkc/commitment.zkc`

```zkc
// Layer D, carried and not frozen. To change: a combination of digests and states for a
// `Linear` kind; coins for an opening; binding, extractability and hiding as properties that a
// goal names; `paired` of the pinned keys as a hypothesis of receipts; the member parameter `n`
// gets a name that an implementing module will not want for itself; the members that are not
// `spec` are deployed code.
module zkc::commitment

// Core library.

use zkc::oracle::{Kind}

// [item] A non-interactive scheme that realizes the primitive kind `K`: what is sent in place
// of the data, and what proves a block of rows. A scheme is named in a `commit` line and nowhere
// else; the commit step applies its members. Its configuration is its static arguments.
pub interface Commitment<K: Kind>:
    // Public parameters; `()` when the scheme has none.
    type ProverKey
    type VerifierKey
    // The randomness of a commitment: a law, or `()` for a scheme that does not hide.
    type Blinding
    type Digest
    type State
    // The proof of a block of `n` rows.
    type Proof<n: nat>
    // The two keys come from one setup.
    spec def paired(prover_key: ProverKey, verifier_key: VerifierKey) -> bool
    def commit(key: ProverKey, data: K::Data, blinding: Blinding) -> (Digest, State)
    def opening<n: nat>(key: ProverKey, state: State, positions: [K::Position; n]) -> Proof<n>
    def check<n: nat>(
        key: VerifierKey,
        digest: Digest,
        positions: [K::Position; n],
        rows: [K::Row; n],
        proof: Proof<n>
    ) -> bool
    // An honest opening of honest data is accepted.
    law opens<n: nat>(
        prover_key: ProverKey,
        verifier_key: VerifierKey,
        data: K::Data,
        blinding: Blinding,
        positions: [K::Position; n]
    ): not paired(prover_key, verifier_key) or check(
        verifier_key,
        commit(prover_key, data, blinding).0,
        positions,
        [K::answer(data, p) for p in positions],
        opening(prover_key, commit(prover_key, data, blinding).1, positions)
    )
```

### 2.6 `zkc::hash`

*State: the interfaces are layer A, among them `ExtendableOutput`, which the two SHAKE modules
implement.*

| Declaration | Kind | Mark | Members |
|---|---|---|---|
| `Hash` | interface | **item**, source | natural `Size`, `hash` |
| `Sha256` | module | row `hash.sha256` |  |
| `Keccak256` | module | row `hash.keccak256` |  |
| `ExtendableOutput` | interface | source | `output` |
| `Shake128` | module | row `hash.shake128` |  |
| `Shake256` | module | row `hash.shake256` |  |

A permutation or a standard byte hash is a row; a sponge, a compression function and a tree mode
are source over it (`STANDARD-LIBRARY.md`). An extendable-output function is no `Hash`, whose
`Size` is fixed: `output<count>` gives as many bytes as its static argument asks for.

`libraries/zkc/hash.zkc`

```zkc
module zkc::hash

// Core library.

// [item] A function from bytes to a digest; the hash of a `pin`.
pub interface Hash:
    nat Size
    def hash(input: [byte]) -> [byte; Size]

// [rows hash.sha256, hash.keccak256]
pub module Sha256: Hash = primitive("hash.sha256")
pub module Keccak256: Hash = primitive("hash.keccak256")

// An extendable-output function: from bytes to as many bytes as are asked for. It is no `Hash`,
// whose `Size` is fixed.
pub interface ExtendableOutput:
    def output<count: nat>(input: [byte]) -> [byte; count]

// [rows hash.shake128, hash.shake256]
pub module Shake128: ExtendableOutput = primitive("hash.shake128")
pub module Shake256: ExtendableOutput = primitive("hash.shake256")
```

### 2.7 `zkc::layout`

*State: layer C, carried; not frozen. The source below has the field leaf over `PrimeField`
and three laws of its own. To change: the field leaf is one function over `F: Field` that may
use `F::components`, and the laws are that a reader is deterministic, agrees with the writer,
accepts only the canonical prefix that the writer produced and leaves the suffix;
`LANGUAGE.md` TY14 states both.*

| Declaration | Kind | Mark | Members |
|---|---|---|---|
| `Layout` | interface | **item**, source | type `Unit`, `write_natural`, `read_natural`, `write_field`, `read_field`, `write_group`, `read_group`, law `natural`, law `field`, law `group` |
| `canonical` | module | **item**, source | `Unit`, `write_natural`, `read_natural`, `write_field`, `read_field`, `write_group` (row `group.to_bytes`), `read_group` (row `group.from_bytes`) |

The leaves of a layout are a natural below `2^64`, an element of a prime field and a group
element. Everything else is structure, and its writer and reader are generated: `L::write<T>` and
`L::read<T>` (§8 of the reference). `canonical` is written in source; its two group leaves are
rows. Its readers do not stop: the condition of an `if` gives the fact that a read needs (TY9),
and a reader returns `None` where the units are too few or the encoding is not canonical. The
three laws are typed at `canonical`. The signatures are proposed and not validated.

`libraries/zkc/layout.zkc`

```zkc
// Layer C, carried and not frozen. To change: the field leaf is one function over
// `F: Field`, written over `F::components`; the law that a reader accepts only what the
// writer wrote, as TY14 states it (deterministic, canonical prefix only, the suffix left, no
// unit for `()` or an empty sized collection); `read_natural` and `read_field` are to form
// their value by an expression whose range is a fact, not in a `mut`
// accumulator.
module zkc::layout

// Core library.

use zkc::option::{Option}

// [item] How the leaves of a value are written as units. The writer and the reader of a
// tuple, a record, a variant, a collection and an element of an extension field are generated
// from these members (`L::write<T>`, `L::read<T>`); a reader returns the value and the number of
// units it took, or `None`. A natural that crosses is below 2^64.
pub interface Layout:
    type Unit
    def write_natural(n: index<2^64>) -> [Unit]
    def read_natural(units: [Unit]) -> Option<(index<2^64>, nat)>
    def write_field<F: PrimeField>(x: F) -> [Unit]
    def read_field<F: PrimeField>(units: [Unit]) -> Option<(F, nat)>
    def write_group<G: Group>(x: G) -> [Unit]
    def read_group<G: Group>(units: [Unit]) -> Option<(G, nat)>
    law natural(n: index<2^64>, rest: [Unit]):
        read_natural(write_natural(n) ++ rest) == Some((n, length(write_natural(n))))
    law field<F: PrimeField>(x: F, rest: [Unit]):
        read_field<F>(write_field(x) ++ rest) == Some((x, length(write_field(x))))
    law group<G: Group>(x: G, rest: [Unit]):
        read_group<G>(write_group(x) ++ rest) == Some((x, length(write_group(x))))

// [item] [source] The layout of a scheme without a `layout` line: bytes; a natural as eight
// bytes and an element of a prime field as `F::Bytes` bytes, least significant first; a group
// element in the compressed encoding of the vocabulary.
pub module canonical: Layout:
    type Unit = byte

    def write_natural(n): [(n / 256^i) % 256 for i in 0..8]

    def read_natural(units):
        mut result: Option<(index<2^64>, nat)> = None
        if 8 <= length(units):
            mut value = 0
            for i in 0..8:
                value := value * 256 + units[7 - i]
            result := Some((value, 8))
        return result

    def write_field(x): [(F::to_nat(x) / 256^i) % 256 for i in 0..F::Bytes]

    // Refuses an encoding that is not below the order: the encoding is canonical.
    def read_field(units):
        mut result: Option<(F, nat)> = None
        if F::Bytes <= length(units):
            mut value = 0
            for i in 0..F::Bytes:
                value := value * 256 + units[F::Bytes - 1 - i]
            if value < F::Order:
                result := Some((F::from_nat(value), F::Bytes))
        return result

    // [rows group.to_bytes, group.from_bytes]
    def write_group(x) = primitive("group.to_bytes")
    def read_group(units) = primitive("group.from_bytes")
```

### 2.8 `zkc::construction`

*State: layer C, carried; not frozen. Pending: the schedule of the
Fiat–Shamir step and a label for `absorb` and `squeeze`; the primitive that the model
idealizes, a bound on `None`, and the distances as obligations.*

| Declaration | Kind | Mark | Members |
|---|---|---|---|
| `Suite` | interface | **item**, source | module `Units`, type `State`, type `Challenge`, natural `ChallengeUnits`, natural `PositionUnits`, `start`, `absorb`, `squeeze`, `challenge`, `position`, spec `challenge_distance`, spec `position_distance` |

`position` and `position_distance` have a `where (1 <= n)`: a position below zero bounds does not
exist, and a draw of `index<0>` is no law (TY15). A suite in source and the suites of the
catalogue are in `zkc::suites` (`STANDARD-LIBRARY.md`). The signatures are proposed and not
validated: their test is a byte-exact reproduction of a deployed transcript.

`libraries/zkc/construction.zkc`

```zkc
// Layer C, carried and not frozen. To change: the primitive that the model idealizes; a bound
// on `None` with a stop reason; the decoder distances as obligations; the schedule of the
// Fiat-Shamir step, with a label for `absorb` and `squeeze`; the member parameter `n` is
// renamed.
module zkc::construction

// Core library.

use zkc::layout::{Layout}
use zkc::option::{Option}

// [item] How a `derived` construction turns the transcript into challenges. The Fiat–Shamir
// step applies the members: it starts from the proof identity, absorbs every value in the
// units of `Units`, and decodes each drawn leaf from squeezed units; `None` asks for more
// units. The draws of `nonzero`, of tuples and of sized collections are derived from the two
// leaf decoders. The signatures are proposed and not validated against a deployed transcript.
pub interface Suite:
    // How a value is absorbed.
    module Units: Layout
    type State
    type Challenge: Field
    nat ChallengeUnits
    nat PositionUnits
    def start(identity: [byte; 32]) -> State
    def absorb(state: State, units: [Units::Unit]) -> State
    def squeeze<n: nat>(state: State) -> (State, [Units::Unit; n])
    def challenge(units: [Units::Unit; ChallengeUnits]) -> Option<Challenge>
    def position<n: nat>(
        units: [Units::Unit; PositionUnits]
    ) -> Option<index<n>> where (1 <= n)
    // The distance of each decoder from the uniform law.
    spec def challenge_distance() -> rational
    spec def position_distance<n: nat>() -> rational where (1 <= n)
```

### 2.9 `zkc::security`

*State: layer B, carried. The statement of a property is the definition of its entry in the
formal library.*

A vocabulary module: it has no source file. Its names are the entries of the vocabulary of kind
`property` and `model`; `use zkc::security::{soundness, random_oracle}` imports them. Their
meaning is the experiment of the formal library. What GL3 and GL4 read of each:

| Property | Honest side | Clause it needs | Stages at which it is stated | Constructions it admits |
|---|---|---|---|---|
| `completeness` | every role | — | written, committed, constructed, serialized | derived, interactive, authored |
| `soundness` | the verifier | `proves` or `reduces` | written, committed, constructed, serialized | derived, interactive, authored |
| `knowledge_soundness` | the verifier | `knowledge` | written, committed, constructed, serialized | derived, interactive, authored |
| `zero_knowledge` | every role but the simulated one; an offline role whose coins a model authorises as a trapdoor is honest | `zero_knowledge` | written, committed, constructed, serialized | derived, interactive, authored |
| `honest_verifier_zero_knowledge` | the prover and the verifier | `zero_knowledge` | written, committed | derived, interactive, authored |
| `unforgeability` | the verifier | — | constructed, serialized | derived, authored |

| Model | Budget (a ceiling needs it) |
|---|---|
| `random_oracle` | `random_oracle(queries = n)` |
| `generic_group` | `generic_group(operations = n)` |
| `algebraic_group` | — |
| `johnson` | — |

For `knowledge_soundness` the vocabulary also gives the signature of the function that the clause
names, and for the two zero-knowledge properties that of the simulator; they are stated once, in
SX6. What a simulator may be given for each property and stage is the table of GL3: the
abilities are permissions. A `trapdoor` is authorised by a model of a reference string,
which names the offline roles whose coins a simulator may be given; the vocabulary has no
such entry yet, and until it has, a goal that uses `trapdoor` is refused. The stages (`written`, `committed`, `constructed`, `serialized`), `fixed`, `adaptive`,
`hidden`, `observed(n)` and `residual` are words of a goal, not names of this module. The names
are whole words: an abbreviation would have to be learned as well.

---

## 3. What a first-time writer looked for, and where it is

| Looked for | Where | Tier |
|---|---|---|
| a group identity | the literal `0` checks against a `Group` (TY6) | table |
| a law for a uniform group element | a type of sort `Group` is a law (TY15) | table |
| a natural or an index as a field element | `F::from_nat(n)`, a member of `Ring` | row of a sort |
| the natural of an element of a prime field | `F::to_nat(x)`, a member of `PrimeField` | row of a sort |
| a ring that is not a field; vectors over it | the sort `Ring`; a sized collection of ring elements is a `Group` over the ring | table |
| SHAKE | `zkc::hash::{Shake128, Shake256}`, modules that implement `ExtendableOutput` | core, rows |
| `zip`, `enumerate`, a count | `zkc::sequence` | standard library, source |
| one function to fold points and scalars | `zkc::sequence::fold<T: Group, m>`: every `Group` has a `Scalar`, and a field is its own | standard library, source |
| the list of suites | `zkc::suites`: modules, found by `use` and checked | standard library |
| `Oracle`, `data` without `use` | the prelude; a kind (`table`) is imported; `shape` does not exist | core |
| arithmetic of `rational` | TY8 | reserved type |
| a named size | a binding of a static term is a static name (TY2) | language |
| multiplicative notation, the scalar on the left | not offered: one spelling per type; the message gives the line to write | — |

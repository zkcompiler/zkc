# Core language: types, definitions and operations

## Types

A type is built from the package's nominal types and a small structural grammar.

| Type | Values |
|---|---|
| `unit` | one value |
| `bool` | truth values |
| `index` | natural numbers |
| `nominal(n)` | row `n` of the package's type table: a catalogue type constructor applied to static arguments, such as a field, a group, a polynomial over a field, bytes, a commitment or a transcript state |
| `array(T)` | finite sequences of `T` |
| `tuple(T₁, …, Tₖ)` | records, by position |
| `variant(T₁, …, Tₖ)`, `k ≥ 1` | one alternative, tagged by position |
| `oracle(n)` | a handle of row `n` of the package's oracle table |

A nominal type has no structure in the core. Its algebra is fixed by the catalogue
operations over it and, in the formal library, by the laws a model satisfies.

A variant has at least one alternative. Every type therefore has a value when every
nominal type has one, and an operation row of any signature has a meaning.

An oracle row records the row type, the position type and the origin of the
handle: `sent`, or `computed(d, n₁, …, nₖ)` by definition `d` from parent handles of
oracle rows `n₁ … nₖ`. The origin is part of the type. A handle whose origin would
change from one loop iteration to the next has no type. The type fixes the shape
of a computed oracle, not its data: the parents it was built from, the values it
captured and its extent belong to the handle.

## Holders

A protocol declares roles `0 … n−1`, at least one. A value in a protocol body has a
located type `T @ r`: a type and one holder. Functions are not located; their values
have plain types.

A source value that several roles hold is emitted as one core value per holder.
The protocol's signature records such copies as an agreement
([contracts](contracts.md#agreements)).

## Definitions

A program is a list of definitions. A definition refers only to earlier ones.

| Definition | Signature | Body |
|---|---|---|
| Function | input types, output types | a local region |
| Protocol | role count, located input types, located output types, agreements | a protocol region |
| Computed oracle | parent oracle rows, capture types, position type, row type | three functions of the captures and a position: whether the position is in the extent; the ordered positions to read in each parent; and, given the parents' answers, the row |
| Relation | parameter types | a function returning `bool`, or an external meaning |

A definition may be marked specification-only
([contracts](contracts.md#specification-only-programs)). Such a definition is never
applied by a deployed protocol.

## Regions

A region has typed inputs and typed outputs. Its body is a sequence of operations
followed by a return. Each operation names its operands among the region's inputs
and the results of earlier operations, by position, and appends its results. A
region is closed: an operation that contains regions passes them their inputs
explicitly.

## Catalogue operations

The package's operation table lists every catalogue operation the program uses,
instantiated at its static arguments, with its input types, output types and kind.

The kind belongs to the row; an operation that uses the row does not restate it.

| Kind | Meaning |
|---|---|
| Pure | a total function of its inputs |
| Partial | a function of its inputs that may stop with an authored reason |
| Sampling | a law: a distribution on the output type determined by the inputs |

Hashing, encoding and transcript operations are pure functions of explicit state
values. A sampling row names a law, not a randomness service that threads a
generator state: the uniform law over a type, for instance, takes the type as a
static argument and has no input. A catalogue operation without a formal meaning is
still a row with a signature and a kind.

## Local operations

Local regions make up functions and the computation a single role performs.

| Operation | Operands | Results | Meaning |
|---|---|---|---|
| `op(o)` | the inputs of operation row `o` (pure or partial) | its outputs | the catalogue operation |
| `call(f)` | the inputs of function `f` | its outputs | the function's body |
| `if` | a `bool`, captures; two regions over the captures | the regions' common outputs | the selected region |
| `loop(m)` | an `index` count, carried values, captures; one region from an `index`, the carried values and the captures to the carried values | the carried values | the region run `count` times with the iteration number; stops `refused` when the count exceeds `m` |
| `match` | a variant, captures; one region per alternative | the common outputs | the region of the alternative |
| `guard(reason)` | a `bool` | none | stops with `reason` when false |
| `stop(reason)` | none | ends the region | stops |

The authored reasons are `reject`, `abort`, `exhausted` and `refused`. A `stop`, a
`guard` and a partial row stop with one of them. The reason `incomplete` is
reserved for the [meaning](meaning.md#agreement) of a side whose roles disagree on
a control value; no program and no model produces it otherwise.

A region that ends in `stop` returns no values. An `if` takes its outputs from the
arm that returns; when both arms stop it has no results, and its own region ends
there. The iteration number of a `loop` starts at 0.

## Protocol operations

Each operation has one owner unless stated. Operands owned by a role are values
that role holds.

| Operation | Operands | Results | Meaning |
|---|---|---|---|
| `at(r, ℓ)` | the operands of local operation `ℓ`, held by `r` | its results, held by `r` | role `r` performs `ℓ`, one of `op`, `call`, `if`, `loop`, `match`, `guard` |
| `exchange(s, r, site)` | `T @ s` | `T @ r` | `s` sends the value to another role `r` |
| `draw(o, R, site, law)` | the inputs of sampling row `law`, held by `o` | `T @ o`, then `T @ r` for each `r` in `R` in increasing order | `o` draws a public coin and announces it to the roles in `R`, which do not include `o` |
| `sample(o, site, law)` | the inputs of `law`, held by `o` | `T @ o` | `o` samples a secret |
| `repeat(P, m)` | for each role in `P` an `index` it holds, the carried values, the captures; one region from the carried values and captures to the carried values | the carried values | the roles in `P` run the region as many times as their count says; stops `refused` above `m` |
| `branch(P)` | for each role in `P` a `bool` it holds, the captures; two regions | the common outputs | each role in `P` follows its own condition |
| `apply(d, ρ, site)` | the inputs of protocol `d` with its roles renamed by the injective map `ρ` | its outputs, renamed | the roles `ρ(0), ρ(1), …` run protocol `d` |
| `oracle_send(s, R, site)` | a table held by `s` | a handle of a `sent` row for `s` and for each role in `R` | `s` gives the roles in `R` query access to the table |
| `oracle_compute(o, d)` | the parent handles, in order, and the capture values, held by `o` | a handle of the `computed(d, …)` row | no information moves; the handle denotes the oracle that `d` computes from these parents and captures |
| `oracle_read(o, site)` | for each of one or more handles held by `o`, an array of positions | for each handle, the array of rows | `o` learns the rows at the positions. The positions of one read are fixed before any of its answers; a position that depends on an answer belongs to a later read |

`repeat` and `branch` list their participants `P`, at least one and each role once.
Every role that
an operation inside their regions names is in `P`: an owner, a sender, a receiver,
the receivers of a draw, the entries of a role map. Every value that enters or
leaves is held by a role in `P`. Each participant holds its own copy of the count,
or of the condition. The copies agree in an honest execution. What a side does
when its copies differ is fixed by the [meaning](meaning.md#agreement).

A protocol region contains no `stop`. A role stops through a `guard` or a partial
operation that it performs.

A verifier's challenge is a `draw`. A value a role samples and later reveals is a
`sample` followed by an `exchange`; the Fiat–Shamir stage does not derive it.

## Sites

Every `exchange`, `draw`, `sample`, `apply`, `oracle_send` and `oracle_read` has a
site. The sites of a definition are numbered from 0 without gaps, and no two
operations of the definition share one, in whatever regions or branch arms they
occur. A protocol-level `guard` has no site of
its own; its position in the body identifies it ([package](package.md#regions-and-values)). A site
together with its definition identifies a static program point. The site of an
operation reached through applications is that of the innermost definition; the
path of applications is not part of it.

## Well-formedness

A package is well formed when two groups of conditions hold.

- **Typing.** Every body type-checks against the tables: operand types and holders
  match; regions are closed; references point to earlier rows; an operation's use
  of a row agrees with the row's signature and kind; the reason of a `guard` is an
  authored reason; the outputs of a `branch` are held by its participants; the
  ports of an agreement have one type; a deployed definition applies no
  specification-only definition. These are the typing rules of the formal library's
  `Region` over the core dialect.
- **Residual conditions.** A protocol has a role. Holders, owners and participants
  are below the definition's role count. A `repeat` or `branch` has a participant;
  its participants are distinct, include every role named inside it, and hold every
  value that enters or leaves it. The sender and receiver of an `exchange` differ.
  The receivers of a `draw` increase strictly and exclude its owner. A role map has
  one entry per formal role, in range and injective. Sites are numbered without
  gaps and unique. A protocol region contains no `stop`, and the reason of a `stop`
  is an authored reason. An agreement names ports with different holders, and the
  agreements of a signature name each port at most once. These are decidable
  conditions over the package's numeric tables.

A consumer accepts a package only when both groups are checked. The formal library
checks the first by type-checking the terms it builds and the second by deciding
each condition once.

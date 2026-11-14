# Core language: types, definitions and operations

## Types

A type is built from the package's nominal types, its declarations of records and
variants, and a small structural grammar.

| Type | Values |
|---|---|
| `bool` | truth values |
| `nat` | natural numbers: counts, positions and sizes |
| `fin n` | the natural numbers below `n` |
| `nominal n` | row `n` of the package's type table: a catalogue type constructor applied to static arguments, such as a field, a group, a polynomial over a field, a commitment or a transcript state |
| `seq T none` | finite sequences of `T`; the length is a property of the value |
| `seq T (some n)` | sequences of exactly `n` elements of `T` |
| `tuple [T₁, …, Tₖ]` | one value of each component, by position. The empty tuple `tuple []` is the unit type, with one value |
| `record d u [T₁, …, Tₖ]` | one value of each field of record declaration `d`, by position |
| `variant d [T₁, …, Tₖ]` | the payload of one alternative of variant declaration `d`, tagged by position |
| `oracle(n)` | a handle of row `n` of the package's oracle table |

A nominal type has no structure in the core. Its algebra is fixed by the catalogue
operations over it and, in the formal library, by the laws a model satisfies.

A record type and a variant type name a declaration of the package by its number and
carry the declaration's shape: the field types of a record, with its use, and the
payload types of a variant. Two declarations of one shape are different types. The
package writes such a type by the number alone ([package](package.md#types)), and its
reader gives it the declaration's use and shape.

A type may have no value: `fin 0`, a variant without alternatives, and a type that
needs a value of one of them. A type is populated when it has a value whenever every
nominal type has one (`Ty.populated`):

- `bool`, `nat`, a nominal type and `seq T none` are populated;
- `fin n` is populated when `n ≥ 1`, and `seq T (some n)` when `n` is 0 or `T` is
  populated;
- a tuple or a record is populated when every component is, and a variant when some
  alternative is.

Every nominal type has a value in every [model](meaning.md#models); a type built from
the nominal types may still have none.

An oracle row records the row type, the position type and the origin of the
handle: `sent`, or `computed(d, n₁, …, nₖ)` by definition `d` from parent handles of
oracle rows `n₁ … nₖ`. The origin is part of the type. A handle whose origin would
change from one loop iteration to the next has no type. The type fixes the shape
of a computed oracle, not its data: the parents it was built from, the values it
captured and its extent belong to the handle.

## Declarations

The package's type table consists of its nominal rows, its record declarations and
its variant declarations (`TypeTable`).

| Declaration | Content |
|---|---|
| Record | a use, and the field types by position |
| Variant | the payload type of each alternative, by position. An alternative without a payload has the unit type |

The use of a record says how often a value of it may be used: any number of times
(`free`), at most once (`atMostOnce`) or exactly once (`exactlyOnce`). It is part of
the record type.

A type agrees with the type table: every nominal row it names is a row of the table,
and every record and variant it names is declared with the use and the shape that the
type carries. The fields and the alternatives of a declaration are types of the
package. No declaration contains itself, directly or through other declarations.

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
| Pure | a total function of its inputs. Every output type is populated |
| Restricted | a function of its inputs on a domain: outside the domain the row has no value. It may name its domain row |
| Sampling | a law: a distribution on the output type determined by the inputs. The output type is populated |

No row stops with an authored reason. A restricted row applied outside its domain
stops with the reserved reason `undefined` ([meaning](meaning.md#functions)). A pure
row cannot return a value of a type that may have none, so a pure row with an output
type that is not populated is refused; a restricted row may have such an output. A law
is a distribution on a type that has a value, so a sampling row whose output type is not
populated is refused as well: a `draw` or a `sample` always has a coin to return.

A restricted row may name its *domain row*: a pure row earlier in the table, with the
inputs of the restricted row and the one output `bool`. The domain row decides the
domain: a model satisfies the *domain law* of the restricted row when the restricted
row has a value exactly where the domain row gives `true`. An application of the
restricted row is justified by a value that is the domain row applied to the same
operands and is known to be `true` ([the check of facts](#the-check-of-facts)). A
restricted row that names no domain row has a domain that only the model knows, and
no application of it is justified.

Hashing, encoding and transcript operations are pure functions of explicit state
values. A sampling row names a law, not a randomness service that threads a
generator state: the uniform law over a type, for instance, takes the type as a
static argument and has no input. A catalogue operation without a formal meaning is
still a row with a signature and a kind.

The operations on the types whose values the core fixes are not rows of the table:
they are the [operations the core owns](#operations-the-core-owns).

## Operations the core owns

The values of `bool`, `nat`, `fin n`, sequences, tuples, records and variants are
fixed by the core, and so are the operations on them. They form a closed list
(`Builtin`), each with its typing and its value, and no model chooses their meaning.
In the table, `a` and `b` are the `nat` arguments in order, `i` is the position
argument of `seq.at`, and `s`, `s₁` and `s₂` are sizes of sequence types, `none` or
`some n`.

| Operation | Arguments | Results | Value |
|---|---|---|---|
| `nat.add`, `nat.mul`, `nat.pow` | `nat`, `nat` | `nat` | `a + b`, `a · b`, `a ^ b` |
| `nat.equal`, `nat.less` | `nat`, `nat` | `bool` | `a = b`, `a < b` |
| `nat.sub` | `nat`, `nat` | `nat` | `a − b`, on `b ≤ a` |
| `nat.div`, `nat.rem` | `nat`, `nat` | `nat` | `a / b` rounded down and the remainder, on `1 ≤ b` |
| `bool.and`, `bool.or`, `bool.equal` | `bool`, `bool` | `bool` | conjunction, disjunction, equality |
| `bool.not` | `bool` | `bool` | negation |
| `seq.length` | `seq T s` | `nat` | the number of elements |
| `seq.at` | `seq T s`, `nat` | `T` | the element at position `i`, on `i < length` |
| `seq.slice` | `seq T s₁`, `nat`, `nat` | `seq T s₂` | the elements from position `a` up to, not including, position `b`, on `a ≤ b ≤ length` and, when `s₂` is `some n`, on `b − a = n` |
| `seq.concat` | `seq T s₁`, `seq T s₂` | `seq T s` | the elements of the first, then those of the second. `s` is `some (n₁ + n₂)` when `s₁` is `some n₁` and `s₂` is `some n₂`, and `none` otherwise |
| `seq.fill` | `T` | `seq T (some n)` | `n` copies of the value |
| `local.make` | `n` values of `T` | `seq T (some n)` | the values, in order |
| `seq.sized` | `seq T none` | `seq T (some n)` | the sequence, on its length being `n` |
| `seq.unsized` | `seq T (some n)` | `seq T none` | the sequence |
| `nat.below` | `nat` | `fin n` | the number, on its being below `n` |
| `fin.to_nat` | `fin n` | `nat` | the number |
| `fin.widen` | `fin n` | `fin m`, `n ≤ m` | the number |
| `local.make` | the components | `tuple [T₁, …, Tₖ]` | the tuple |
| `local.get` | `tuple [T₁, …, Tₖ]` | `Tᵢ` | component `i` |
| `local.make` | the fields | `record d u [T₁, …, Tₖ]` | the record |
| `local.get` | `record d u [T₁, …, Tₖ]` | `Tᵢ` | field `i` |
| `local.variant` | `Tᵢ` | `variant d [T₁, …, Tₖ]` | the payload as alternative `i` |

`nat.sub`, `nat.div`, `nat.rem`, `seq.at`, `seq.slice`, `seq.sized` and `nat.below`
have a domain, stated after "on". Outside its domain an operation has no value, and
its application stops with the reserved reason `undefined`. Every other operation of
the list has a value on every input. The bounds of `fin.widen`, the positions of
`local.get` and `local.variant`, and the declarations that `local.make`, `local.get`
and `local.variant` name are static data of the operation, checked by typing.

## Local operations

Local regions make up functions and the computation a single role performs.

| Operation | Operands | Results | Meaning |
|---|---|---|---|
| `op(o)` | the inputs of operation row `o` (pure or restricted) | its outputs | the catalogue operation |
| `call(f)` | the inputs of function `f` | its outputs | the function's body |
| `if` | a `bool`, captures; two regions over the captures | the regions' common outputs | the selected region |
| `loop(c)` | the `nat` count when `c` is not a number, carried values, captures; one region from a `nat`, the carried values and the captures to one value of each collected type and the carried values | one sequence per collected type, then the carried values | the region run once per iteration number below the count, threading the carried values; each sequence holds the collected values of the iterations in order |
| `match(d)` | a value of variant declaration `d`, captures; one region per alternative, from its payload and the captures | the common outputs | the region of the value's alternative, on its payload |
| `guard(reason)` | a `bool` | none | stops with `reason` when false |
| `literal(c)` | none | a value of the literal's type | the literal's value |
| `builtin(b)` | the arguments of `b` | its results | the [operation the core owns](#operations-the-core-owns) |
| `stop(reason)` | none | ends the region | stops |

The authored reasons are `reject`, `abort`, `exhausted` and `refused`. A `stop` and
a `guard` stop with one of them. Two reasons are reserved and no program names
them: `incomplete`, for the [meaning](meaning.md#agreement) of a side whose roles
disagree on a control value, and `undefined`, for a restricted row or an operation
the core owns applied outside its domain.

A region that ends in `stop` returns no values. An `if` takes its outputs from the
arm that returns; when both arms stop it has no results, and its own region ends
there. No region of a `match` sees the payload of another alternative, and a `match`
on a variant without alternatives has no region.

A `loop` states how its count is given and the types it collects.

- The count is a number `n` of the operation, and the loop has no count operand; or it
  is a `nat` operand, with an optional maximum `m`. A count above its maximum stops
  `refused`; a count without a maximum never does.
- The iteration number starts at 0. Each iteration takes the carried values of the one
  before it, the first those of the operands, and returns the carried values of the
  next. A stop of an iteration is the stop of the loop.
- Each iteration returns, before its carried values, one value of each collected type
  `T`. The loop returns, before the carried values of the last iteration, the collected
  values of all iterations in order: a `seq T (some n)` when the count is the number
  `n`, and a `seq T none` when the count is an operand. The size of the first is the
  count by the meaning of the loop: no operation with a domain is applied, and nothing
  stops `undefined`. A loop of no iteration returns empty sequences and its carried
  operands.

### Literals

A literal is a value written in the program.

| Literal | Type |
|---|---|
| a natural number | `nat` |
| a truth value | `bool` |
| a number below `n` | `fin n` |
| the numbers that a model reads as a value of nominal row `n` | `nominal n` |
| bytes, each below 256 | `seq (fin 256) (some k)`, with `k` the number of bytes |

A label and a proof identity are literals of nominal types.

## The check of facts

An application of an operation with a domain is *justified* when what is known of
its operands puts them in the domain. The check of facts computes what is known at
every instruction of a body, from the instructions before it, and decides each such
application. Nothing is recorded in the package for it: the guard, the condition, the
count of a loop and the type that a fact comes from are instructions and types of the
program. A function or a protocol *passes* when every application in its body is
justified and no `stop` names `undefined`; a program passes when every function and
every protocol does. A function known by its header only has no body to check.

The rules are stated first for the body of a function, a region of local
operations. [A protocol body](#facts-in-a-protocol-body) has the same rules for the
local operations of each role.

The check is separate from [well-formedness](#well-formedness). A package whose
restricted rows name no domain row is well formed and does not pass.

**What is tracked.** For every value of the region:

- for a `nat`, an interval `lo..hi`, whose `hi` may be absent;
- its *shape*, when it is the result of one of: `a + b`, `a - b`, `seq.length`,
  `fin.to_nat`, `a < b`, `a == b` on naturals, `bool.not`, `bool.and`, `bool.or`, a
  pure row with the one output `bool`, or an `if` that is a conjunction or a
  disjunction (below); the shape names the operands;
- orders `a < b` and `a <= b` between naturals;
- the conditions known to be `true`.

**Intervals of results.**

| Result | Interval |
|---|---|
| a `nat` literal `c` | `c..c` |
| `a + b`, `a * b` | `lo(a) + lo(b) .. hi(a) + hi(b)`, and the same with `*` |
| `a ^ b` | `lo`: `lo(a) ^ lo(b)` when `lo(a)` is at least 1; otherwise 1 when `hi(b)` is 0, and 0. `hi`: `hi(a) ^ hi(b)`, and at least 1 when `lo(b)` is 0 |
| `a - b` | `lo(a) - hi(b) .. hi(a) - lo(b)`, not below 0 |
| `a / b` | `lo(a) / hi(b) .. hi(a) / lo(b)` |
| `a % b` | `0 .. min(hi(a), hi(b) - 1)` |
| `seq.length` | `n..n` on a sequence of `n` elements, `0..` on an unsized one |
| `fin.to_nat` of a `fin n` | `0 .. n - 1` |
| a `nat` result of an `if` or a `match` | the smaller `lo` and the larger `hi` of the regions that return |
| the iteration number of a `loop` | `0 .. n - 1` for the count `n` of the operation; `0 .. hi(count) - 1` for a count that is a value |
| a carried `nat` result of a `loop` whose region returns, at that position, its carried input plus a term `t`, in either order | `lo(init) + lo(count) * lo(t) .. hi(init) + hi(count) * hi(t)` |
| anything else | `0..` |

In the row of the carried result, `init` is the operand carried in, `t` has its
interval in the facts of the region where the region returns, and the count is
`n..n` for the count `n` of the operation and the interval of the count operand for
a count that is a value; the `hi` is absent when one of the three is. Nothing is
known of the carried input inside the region, so the interval of `t` holds in every
iteration. A carried result of any other form has the interval `0..`.

A sum, a product and a power have a `hi` when both operands have one. A difference
and a quotient have a `hi` when `a` has one, and their `lo` is 0 when `hi(b)` is
absent. A remainder has the bound that is present.

**What a condition gives.** A `guard` on `c` gives the facts of `c` taken true to the
instructions after it. An `if` on `c` gives them to its first region and the facts of
`c` taken false to its second. The facts of a condition follow its shape:

| `c`, taken true | Facts |
|---|---|
| `a < b` | the order `a < b`; `hi(a)` is at most `hi(b) - 1`; `lo(b)` is at least `lo(a) + 1` |
| `a == b` | `a <= b` and `b <= a`; each has the interval of the other as well |
| `not d` | the facts of `d` taken false |
| `d and e` | the facts of both, taken true |
| the result of an `if` on `a` whose second region returns the literal `false` | the facts of `a` taken true |
| any condition | it is known to be `true` |

| `c`, taken false | Facts |
|---|---|
| `a < b` | the order `b <= a`; `hi(b)` is at most `hi(a)`; `lo(a)` is at least `lo(b)` |
| `a == b` | `lo(a)` is at least 1 when `hi(b)` is 0, and `lo(b)` is at least 1 when `hi(a)` is 0 |
| `not d` | the facts of `d` taken true |
| `d or e` | the facts of both, taken false |
| the result of an `if` on `a` whose first region returns the literal `true` | the facts of `a` taken false |

An `if` on `a` whose second region returns the literal `false` is `a and b` with `b`
computed under `a`; one whose first region returns the literal `true` is `a or b`
with `b` computed when `a` does not hold. A region *returns the literal* `v` when it
consists of one instruction, `literal` of the `bool` `v`, and returns the value of
that instruction and nothing else; the output of the `if` is then one `bool`. No
other form counts: a region that computes `false`, or that returns the literal
after another instruction, gives the result no shape. When both regions have the
form, the result is a conjunction. The facts of `b` are not given.

A `loop` whose count is a value gives its region the order of the iteration number
below the count, when the region captures the count.

**Nested regions.** A region sees the values it is given. A bound, an order, a known
condition or a shape enters a region when every value it mentions is a capture of
the region. Nothing is known of the payload of a `match` or of the carried values of
a `loop` beyond their types.

The region of a `loop` over the count 0 of the operation never runs. Every
application in it is justified, whatever is known.

**Values of a type without a value.** A region in which a value of a type that is not
populated is in scope never runs: nothing gives that value. Every application after
the place where the value is bound is justified, in that region and in every region
nested in it. The place is one of four: the inputs of a function; the inputs of a
nested region, such as the payload of a `match` on an alternative `fin 0`; the results
of an instruction, such as a call of a function whose output is a variant without
alternatives; the results of a block.

**What is known.** `a <= b` is known when one of: `hi(a) <= lo(b)`; `a` and `b` are
one value; an order says `a <= b` or `a < b`; `b` is `a + u` or `u + a`; `a` is
`b - u`. `a < b` is known when one of: `hi(a) < lo(b)`; an order says it; `b` is
`a + u` or `u + a` with `lo(u)` at least 1; `a` is `b - u` with `lo(u)` at least 1;
or `a` is `x + t` or `t + x`, and an order says `t < d` for a `d` that is `b - x`.
The last is the index of a range that does not start at 0. Nothing else is tried:
orders are not chained, and no arithmetic is done on both sides.

**What each application needs.**

| Application | Needs |
|---|---|
| `nat.sub a b` | `b <= a` known |
| `nat.div a b`, `nat.rem a b` | `lo(b)` at least 1 |
| `seq.at xs i` | on `n` elements: `hi(i) < n`. On an unsized sequence: `i < l` known for an `l` that is `seq.length` of `xs` |
| `seq.slice xs a b` | `a <= b` known; on `n` elements `hi(b) <= n`, on an unsized sequence `b <= l` known for an `l` that is `seq.length` of `xs`; and into `k` elements: `a` and `b` have one-point intervals whose difference is `k`, or `b` is `a + c` or `c + a` with `c` in `k..k` |
| `seq.sized xs` to `n` | an `l` that is `seq.length` of `xs` with the interval `n..n` |
| `nat.below a` to `fin n` | `hi(a) < n` |
| a restricted row with a domain row | a value known to be `true` that is the domain row applied to the same operands |
| a restricted row without one | never justified |

A function that passes never stops `undefined`
([meaning](meaning.md#functions-that-pass-the-check-of-facts)).

### Facts in a protocol body

A value of a protocol body has one holder, and a role computes on the values it
holds. What is known is therefore kept role by role: each role has its own
intervals, shapes, orders and known conditions, about values it holds. A fact of one
role never reaches another. A value that a role receives has what its type gives and
nothing more, whatever the sender knew of the value it sent; a role that needs a fact
of a received value states its own `guard`.

| Operation | What it gives |
|---|---|
| `at(r, ℓ)` | the rules above for the local operation `ℓ`, on what `r` knows: the requirement of `ℓ`, the intervals and shapes of its results, the facts of a `guard`, and the facts at the start of the regions of an `if`, a `loop` and a `match` |
| `exchange`, `draw`, `sample`, `apply` | results of which no role knows anything |
| `choose` on a condition | in the region of `false`, each role of `P` knows the facts of its own copy of the condition taken false; in the region of `true`, taken true |
| `choose` on an arm number or on a variant | nothing; nothing is known of the payloads |
| a `nat` result of a `choose` or of a block | its holder knows the smaller `lo` and the larger `hi` of what it knows of that result where the regions return, as for a result of an `if` |
| `repeat(P, c)` | each role of `P` knows the interval of its iteration number: `0 .. n - 1` for the count `n` of the operation, and `0 .. hi(count) - 1` for its own copy of a count that is a value; in the second case, when the region captures that copy, also the order of the iteration number below it |

The results of a `repeat` are values of which no role knows anything: a carried
result that is a sum has no interval. Nothing is known of the carried values inside
the region of a `repeat`. A result of a `choose` or of a block has no shape.

A nested region of a `choose` or a `repeat` is entered as a nested local region is:
each role keeps the bounds, the orders, the known conditions and the shapes all of
whose values are captures of the region. The region of a `repeat` over the count 0
of the operation never runs, and every application in it is justified.

A value of a type that is not populated stops its holder, and no other role. After
the place where the value is bound (the inputs of the protocol, the inputs of a nested
region, the results of an instruction or of a block), every application of the holder
is justified. An application of another role is checked as before: a side without the
holder holds nothing there and runs.

A copy of a condition that a role received has no shape, so the region of a `choose`
gives that role only that its copy is `true`, in the region of `true`. The role that
computed the condition has the facts of its shape.

An application that is not justified is reported with its *path* and the
requirement it does not meet. The path is the number of the instruction in the body;
for an instruction inside a nested region, the number of the instruction that has the
region, the number of the region among its regions and the number of the instruction
in the region, and so on. The regions of a `choose` on a condition are numbered 0
for `false` and 1 for `true`. A region of a local operation inside an `at` is
numbered under the instruction of the `at`.

A protocol that passes never stops `undefined`, for any side, and neither does the
program of any of its roles
([meaning](meaning.md#protocols-that-pass-the-check-of-facts)).

## Protocol operations

Each operation has one owner unless stated. Operands owned by a role are values
that role holds.

| Operation | Operands | Results | Meaning |
|---|---|---|---|
| `at(r, ℓ)` | the operands of local operation `ℓ`, held by `r` | its results, held by `r` | role `r` performs `ℓ`, one of `op`, `call`, `if`, `loop`, `match`, `guard`, `literal`, `builtin` |
| `exchange(s, r, site)` | `T @ s` | `T @ r` | `s` sends the value to another role `r` |
| `draw(o, R, site, law)` | the inputs of sampling row `law`, held by `o` | `T @ o`, then `T @ r` for each `r` in `R` in increasing order | `o` draws a public coin and announces it to the roles in `R`, which do not include `o` |
| `sample(o, site, law)` | the inputs of `law`, held by `o` | `T @ o` | `o` samples a secret |
| `repeat(P, c)` | for each role in `P` a `nat` it holds when `c` is not a number, the carried values, the captures; one region from a `nat` held by each role in `P`, the carried values and the captures to one value per collected entry and the carried values | one sequence per collected entry, held by its holder, then the carried values | the roles in `P` run the region as many times as the count says, each holding the iteration number; each sequence holds the collected values of the iterations in order |
| `choose(P, t)` | for each role in `P` a tag of type `t` it holds, the captures; the regions of the tag, each over the captures, and the region of an alternative of a variant first over one copy of its payload per role in `P`, held by that role | the common outputs, held by roles in `P` | each role in `P` follows the region its own tag selects; in the region of an alternative of a variant it holds its own payload |
| `apply(d, ρ, site)` | the inputs of protocol `d` with its roles renamed by the injective map `ρ` | its outputs, renamed | the roles `ρ(0), ρ(1), …` run protocol `d` |
| `oracle_send(s, R, site)` | a table held by `s` | a handle of a `sent` row for `s` and for each role in `R` | `s` gives the roles in `R` query access to the table |
| `oracle_compute(o, d)` | the parent handles, in order, and the capture values, held by `o` | a handle of the `computed(d, …)` row | no information moves; the handle denotes the oracle that `d` computes from these parents and captures |
| `oracle_read(o, site)` | for each of one or more handles held by `o`, an array of positions | for each handle, the array of rows | `o` learns the rows at the positions. The positions of one read are fixed before any of its answers; a position that depends on an answer belongs to a later read |

The tag of a `choose` (`ChoiceTag`) is one of three.

| Tag | Each participant holds | Regions | Inputs of a region |
|---|---|---|---|
| a condition | a `bool` | two, one for each truth value | the captures |
| an arm number | a `fin k` | `k`, region `i` for the number `i` | the captures |
| an alternative of the variant declaration `d` | a value of the variant | one per alternative of `d`, in order | for each participant, in their order, its own copy of the payload of the alternative, which it holds; then the captures |

Every value of the tag selects a region. A `choose` over a condition is a branch. A
`choose` over a variant is the `match` of its participants: no region sees the
payload of another alternative, and a `choose` over a variant without alternatives
has no region. Two copies of a variant are the same tag when they are the same
alternative; their payloads are not compared, and each participant keeps its own.

`repeat` and `choose` list their participants `P`, at least one and each role once.
Every role that
an operation inside their regions names is in `P`: an owner, a sender, a receiver,
the receivers of a draw, the entries of a role map. Every value that enters or
leaves is held by a role in `P`. Each participant holds its own copy of the tag,
and of the count when it is a value. The copies agree in an honest execution. What
a side does when its copies differ is fixed by the [meaning](meaning.md#agreement).

The count of a `repeat` is given as the count of a `loop` is. It is a number `n` of
the operation, and the `repeat` has no count operand; or each participant holds a
`nat`, its copy of the count, and the operation states the maximum `m`: a count
above it stops `refused`. A `repeat` over a count that is a value always has a
maximum.

The region of a `repeat` takes the iteration number first, once per participant in
the order of `P`, each copy held by its participant. The iteration number starts
at 0.

A `repeat` states the values it collects: a list of located types, each held by a
role in `P`. Each iteration returns, before its carried values, one value per
collected entry. The `repeat` returns, before the carried values of the last
iteration and per collected entry of type `T` at holder `h`, the values of all
iterations in order, held by `h`: a `seq T (some n)` when the count is the number
`n`, and a `seq T none` when the count is a value. A `repeat` of no iteration
returns empty sequences and its carried operands.

A protocol region contains no `stop`. A role stops through a local operation that
it performs.

A verifier's challenge is a `draw`. A value a role samples and later reveals is a
`sample` followed by an `exchange`; the Fiat–Shamir stage does not derive it.

## Sites

Every `exchange`, `draw`, `sample`, `apply`, `oracle_send` and `oracle_read` has a
site. The sites of a definition are numbered from 0 without gaps, and no two
operations of the definition share one, in whatever regions or arms they
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
  authored reason; a `match` has one region per alternative of its variant; a
  literal lies in its type; the static data of an operation the core owns fit its
  operands; the outputs of a `choose` are held by its participants, and a `choose`
  over a variant has one region per alternative of its declaration; the ports of an
  agreement have one type; a deployed definition applies no specification-only
  definition. These are the typing rules of the formal library's `Region` over the
  core dialect.
- **Residual conditions.** A protocol has a role. Holders, owners and participants
  are below the definition's role count. A `repeat` or `choose` has a participant;
  its participants are distinct, include every role named inside it, and hold every
  value that enters or leaves it. A `choose` over an arm number has an arm. The sender and receiver of
  an `exchange` differ. The receivers of a `draw` are listed once each, in any order, and
  exclude its owner. A role map has one entry per formal role, in range and injective. Sites are
  numbered without gaps and unique. A protocol region contains no `stop`, and the
  reason of a `stop` is an authored reason. An agreement names ports with different
  holders, and the agreements of a signature name each port at most once. Every
  type of a signature, of a result and of a table row agrees with the type table,
  and every output type of a pure row and of a sampling row is populated. The domain
  row that a restricted row names is an earlier pure row with its inputs and the one
  output `bool`. These are decidable conditions over the package's numeric tables.

A consumer accepts a package only when both groups are checked. The formal library
checks the first by type-checking the terms it builds and the second by deciding
each condition once.

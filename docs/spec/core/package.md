# Core language: the package format

`zkc.core/0` serializes one program as one JSON value built from arrays, strings
and non-negative integers. Every reference is a position in a table. A consumer that type-checks a
package needs no name lookup, no string comparison and no search.

## Canonical bytes

The canonical encoding is UTF-8 JSON with no insignificant whitespace, integers in
decimal without leading zeros, and strings escaped minimally. A reader accepts any
JSON whitespace.

## Identities

A package has two identities, for two purposes.

- The **artifact identity** is the SHA-256 of the canonical bytes of the whole
  package. It names the file. Names change it.
- The **proof identity** is the SHA-256 of the canonical encoding of
  `["zkc.core.proof/0", original, declaration, []]`: the `original` program and the
  [declaration](contracts.md#the-declaration), which holds the suite and the layout,
  with the list of online roles always written and without the identity itself. Both
  are fixed before the Fiat–Shamir stage runs; `names` is not among them. The
  Fiat–Shamir stage puts the proof identity into the constructed program as a
  constant.

The `original` program of the proof identity is the closure of the entry: the
definitions and rows that the entry protocol and the proof declaration reach,
directly or through others, and no others. They are numbered by a walk from the
entry and then from what the declaration names, in the order of its fields; the walk
visits the references of each definition or row in the order they occur in it and
lists each one after everything it reaches, so the entry is the last protocol. The
declaration is numbered with the program. A definition or a row that neither
reaches, and the order in which the package lists the others, do not change the
proof identity.

A definition number and a site are positions in one package. The proof identity
is what separates the proofs of two packages.

## Envelope

```text
package  = ["zkc.core/0", programs, contracts, proof, parameters, names]
programs = [program]
program  = ["original", types, records, variants, [], operations, definitions]
```

A package holds one program. `contracts`, `proof` and `parameters` are the empty
array, and so is the fifth position of a program; a reader ignores the first three
and refuses a program whose fifth position is not empty. The
[declaration](contracts.md#the-declaration) of a scheme is a document of its own.
`names` is a side table and carries no meaning.

What a [stage](stages.md) returns is printed as a package of the same form. Whether a
package is a program as written or what a stage returned is not in the package: it
is stated to [admission](language.md#admission) beside it.

## Types

```text
types    = [typeRow, …]                       nominal types
typeRow  = [constructor, [static, …]]         constructor: a catalogue type constructor
static   = ["domain", string] | ["nat", n] | ["type", type]
records  = [[use, [type, …]], …]              record declarations: use, field types
use      = "free" | "at_most_once" | "exactly_once"
variants = [[type, …], …]                     variant declarations: payload types
type     = "bool" | "nat"
         | ["fin", n] | ["nominal", n] | ["seq", type] | ["seq", type, n]
         | ["tuple", [type, …]] | ["record", k] | ["variant", k]
```

Each type has one spelling, named as the type is. A sequence whose length is a
property of the value (`seq T none`) is `["seq", T]`, and a sequence of `n` elements
(`seq T (some n)`) is `["seq", T, n]`. The empty tuple, the unit type, is
`["tuple", []]`. A record or a variant type is the number of its declaration,
`["record", k]` or `["variant", k]`; it has the use and the shape of that
declaration. The fields and the alternatives of a
declaration are types of the package, and no declaration contains itself, directly
or through others.

Catalogue identities (`constructor`, operation names, domain names) are the only
strings with meaning besides the words of this grammar and the names of the
[operations the core owns](language.md#operations-the-core-owns). They occur once, in
these tables. A consumer binds each row to its own interpretation when it loads the
table and thereafter refers to the row by number. A catalogue name consists of
letters, digits, `.`, `_`, `-` and `/`. A `type` static of a type row names only
earlier type rows.

## Operations

```text
operations   = [operationRow, …]
operationRow = [name, [static, …], kind, [type, …], [type, …]]     inputs, outputs
kind         = "pure" | "restricted" | ["restricted", o] | "sampling"
```

`["restricted", o]` is a restricted row that names row `o` as its
[domain row](language.md#catalogue-operations): an earlier row of the table, pure,
with the same inputs and the one output `bool`.

The identity of a row is its name with its static arguments. No two rows of the
table have one identity. A sampling row has one output. Every output type of a pure
row and of a sampling row is populated. No row has the name of an operation the core
owns.

## Definitions

```text
definitions = [definition, …]                 a definition refers only to earlier ones
definition  = ["function", flags, [type, …], [type, …], region]
            | ["protocol", flags, roles, [port, …], [port, …], agreements, region]
port        = [type, holder]
agreements  = [[side, [i, …]], …]             side: 0 inputs, 1 outputs
flags       = n                                bit 0: specification-only
```

`roles` is the number of roles; a holder, an owner or a participant is a role
number below it.

## Regions and values

```text
region = [[instruction, …], [v, …]]           instructions, then the returned values
```

Values are numbered within a region: its inputs first, in order, then the results
of each instruction in order. A region's inputs are fixed by where it occurs: a
definition's inputs, or the values an enclosing instruction passes. A nested
region starts its own numbering.

Local instructions:

```text
["op", o, [v, …]]
["call", f, [v, …]]
["if", v, [v, …], region, region]                  condition, captures, then, else
["loop", bound, c, [v, …], [v, …], region]         count, carried, captures
["loop", bound, c, [v, …], [v, …], region, [type, …]]   the same, then the collected types
["match", d, v, [v, …], [region, …], [type, …]]    variant, value, captures, one region per alternative, outputs
["guard", reason, v]
["literal", literal]
["builtin", name, [static, …], [v, …]]             name, static data, operands
["stop", reason]                                   last instruction of its region
reason  = "reject" | "abort" | "exhausted" | "refused"
bound   = "static" | m | null
literal = ["nat", n] | ["bool", n] | ["fin", n, n]
        | ["nominal", n, [n, …]] | ["bytes", [n, …]]
```

An `if` region receives the captures. A `loop` region receives the iteration
number, the carried values and the captures, and returns one value of each collected
type, then the carried values. A `match` region receives the payload of its
alternative and the captures; a `match` on a variant without alternatives lists no
region.

A region that returns the literal `v`, the form that
[the check of facts](language.md#the-check-of-facts) reads in an `if` that is a
conjunction or a disjunction, is `[[["literal", ["bool", v]]], [n]]`, with `n` the
number of the region's inputs.

The two positions after `"loop"` give the count. With `"static"` the second is the
count itself, a number, and the loop has no count value. Otherwise the second is the
value that holds the count, and the first is its maximum `m`, or `null` when it has
none. A loop that collects nothing has six elements, and an empty list of collected
types is refused; one that collects lists the collected types last.

A literal is a `nat` (`["nat", n]`), a `bool` (1 for true, 0 for false), a value
below a bound (`["fin", bound, value]`), the numbers a model reads as a value of a
nominal row (`["nominal", row, [n, …]]`), or bytes, each below 256.

The static data of an operation the core owns are the types that fix its signature,
and numbers:

| Name | Static data |
|---|---|
| `nat.add`, `nat.sub`, `nat.mul`, `nat.div`, `nat.rem`, `nat.pow`, `nat.equal`, `nat.less`, `bool.and`, `bool.or`, `bool.not`, `bool.equal` | none |
| `seq.length`, `seq.at` | the sequence type of the operand |
| `seq.slice` | the sequence type of the operand, then that of the result |
| `seq.concat` | the sequence types of the two operands |
| `seq.fill`, `seq.sized` | the sized sequence type of the result |
| `seq.unsized` | the sized sequence type of the operand |
| `local.make` | the type of the result: a sized sequence, a tuple or a record |
| `local.get` | the type of the operand, a tuple or a record, then the position |
| `local.variant` | the variant type, then the position of the alternative |
| `nat.below`, `fin.to_nat` | the bound |
| `fin.widen` | the bound, then the wider bound |

Protocol instructions:

```text
["at", r, local]                                   local: any local instruction but "stop"
["exchange", s, r, site, v]
["draw", o, [r, …], site, law, [v, …]]             receivers, each once; results in their order
["sample", o, site, law, [v, …]]
["repeat", [[r, v], …], m, [v, …], [v, …], region] participants with counts, maximum, carried, captures
["repeat", [r, …], ["static", n], [v, …], [v, …], region]
                                                   participants, count, carried, captures
["repeat", …, region, [port, …]]                   either form, then the collected values
["branch", [[r, v], …], [v, …], region, region, [port, …]]
                                                   participants with conditions, captures, outputs
["choose", [[r, v], …], [v, …], [region, …], [port, …]]
                                                   participants with arm numbers, captures, outputs
["case", d, [[r, v], …], [v, …], [region, …], [port, …]]
                                                   variant, participants with values of it, captures,
                                                   one region per alternative, outputs
["apply", d, [r, …], site, [v, …]]                 role map: formal role j runs as the j-th entry
```

A region nested in `["at", r, …]` is a local region over `r`'s values. A `repeat`
region receives the iteration number once per participant, in their order, then
the carried values and the captures, and returns one value per collected entry, then
the carried values. A `repeat` that collects nothing has six elements, and an empty
list of collected values is refused; one that collects lists their located types
last. The position
after the participants gives the count: a number `m` is the maximum of a count that
is a value, and each participant is listed with the value that holds its count;
`["static", n]` is the count itself, and the participants are listed alone. A `branch` is
the `choose` over a condition: each participant holds a `bool`, the first region
runs when it holds and the second when it does not. A `choose` with `k` regions, at
least one, is the `choose` over an arm number: each participant holds a `fin k`,
and region `i` runs for the number `i`. A region of either receives the captures.
A `case` is the `choose` over the variant declaration `d`: each participant holds a
value of the variant, and region `i` runs for alternative `i`. It receives the
payload of that alternative once per participant, in their order, each copy held by
its participant, then the captures. A `case` lists one region per alternative, and
none for a variant without alternatives.
A protocol `guard` is `["at", r, ["guard", reason, v]]` and has no site of its own;
its position in the body identifies it.

## Names

```text
names = [[definition names], [[role names], …], [[site names], …]]
```

one list of role names and one of site names per definition, empty for
definitions without roles or sites. A package without names has `names = []`.

## Example

A Schnorr proof of knowledge of `x` with `y = x·g`, with roles 0 (prover) and
1 (verifier), over a scalar field and a group:

```json
["zkc.core/0",
 [["original",
   [["field", [["domain", "scalar"]]], ["group", [["domain", "curve"]]]],
   [],
   [],
   [],
   [["law.uniform", [["type", ["nominal", 0]]], "sampling", [], [["nominal", 0]]],
    ["curve.scale", [["domain", "curve"]], "pure", [["nominal", 1], ["nominal", 0]], [["nominal", 1]]],
    ["curve.add", [["domain", "curve"]], "pure", [["nominal", 1], ["nominal", 1]], [["nominal", 1]]],
    ["curve.equal", [["domain", "curve"]], "pure", [["nominal", 1], ["nominal", 1]], ["bool"]],
    ["field.mul", [["domain", "scalar"]], "pure", [["nominal", 0], ["nominal", 0]], [["nominal", 0]]],
    ["field.add", [["domain", "scalar"]], "pure", [["nominal", 0], ["nominal", 0]], [["nominal", 0]]]],
   [["protocol", 0, 2,
     [[["nominal", 1], 0], [["nominal", 1], 0], [["nominal", 0], 0],
      [["nominal", 1], 1], [["nominal", 1], 1]],
     [["bool", 1]],
     [[0, [0, 3]], [0, [1, 4]]],
     [[["sample", 0, 0, 0, []],
       ["at", 0, ["op", 1, [0, 5]]],
       ["exchange", 0, 1, 1, 6],
       ["draw", 1, [0], 2, 0, []],
       ["at", 0, ["op", 4, [9, 2]]],
       ["at", 0, ["op", 5, [5, 10]]],
       ["exchange", 0, 1, 3, 11],
       ["at", 1, ["op", 1, [3, 12]]],
       ["at", 1, ["op", 1, [4, 8]]],
       ["at", 1, ["op", 2, [7, 14]]],
       ["at", 1, ["op", 3, [13, 15]]]],
      [16]]]]]],
 [], [], [],
 [["schnorr"], [["prover", "verifier"]], [["nonce", "commitment", "challenge", "response"]]]]
```

Values 0–4 are the inputs (`g`, `y`, `x` for the prover; `g`, `y` for the
verifier). Value 5 is the nonce, 6 the commitment, 7 the verifier's copy of it, 8
and 9 the challenge at the verifier and at the prover, 11 the response, 12 the
verifier's copy, and 16 the decision.

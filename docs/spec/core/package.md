# Core language: the package format

`zkc.core/0` serializes every stage of one compilation, with the contracts and the
proof declaration, as one JSON value built from arrays, strings and non-negative
integers. Every reference is a position in a table. A consumer that type-checks a
package needs no name lookup, no string comparison and no search.

## Canonical bytes

The canonical encoding is UTF-8 JSON with no insignificant whitespace, integers in
decimal without leading zeros, and strings escaped minimally. A package's identity
is the SHA-256 of its canonical bytes. A reader accepts any JSON whitespace.

## Envelope

```text
package  = ["zkc.core/0", programs, contracts, proof, parameters, names]
programs = [program, …]                       one per stage, in pipeline order
program  = [stage, types, oracles, operations, definitions]
stage    = "original" | "unfolded" | "committed" | "constructed"
```

`contracts`, `proof` and `parameters` follow the [contract](contracts.md) and
[stage](stages.md) chapters; each may be the empty array. `names` is a side table
and carries no meaning.

## Types

```text
types    = [typeRow, …]                       nominal types
typeRow  = [constructor, [static, …]]         constructor: a catalogue type constructor
static   = ["domain", string] | ["nat", n] | ["type", type]
type     = "unit" | "bool" | "index"
         | ["nominal", n] | ["array", type] | ["tuple", [type, …]]
         | ["variant", [type, …]] | ["oracle", n]
oracles  = [oracleRow, …]
oracleRow = [row: type, position: type, origin]
origin   = ["sent"] | ["computed", d, [n, …]]
```

Catalogue identities (`constructor`, operation names, domain names) are the only
strings with meaning. They occur once, in these tables. A consumer binds each row
to its own interpretation when it loads the table and thereafter refers to the row
by number. A catalogue name consists of letters, digits, `.`, `_`, `-` and `/`. A
`type` static of a type row names only earlier type rows.

## Operations

```text
operations   = [operationRow, …]
operationRow = [name, [static, …], kind, [type, …], [type, …]]     inputs, outputs
kind         = "pure" | "partial" | "sampling"
```

The identity of a row is its name with its static arguments. No two rows of the
table have one identity. A sampling row has one output.

## Definitions

```text
definitions = [definition, …]                 a definition refers only to earlier ones
definition  = ["function", flags, [type, …], [type, …], region]
            | ["protocol", flags, roles, [port, …], [port, …], agreements, region]
            | ["oracle", flags, [n, …], [type, …], position: type, row: type, f, f, f]
                                               parent rows, capture types; extent test, parent positions, answer
            | ["relation", flags, [type, …], meaning]
port        = [type, holder]
agreements  = [[side, [i, …]], …]             side: 0 inputs, 1 outputs
flags       = n                                bit 0: specification-only
meaning     = ["formula", f] | ["external", string]
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
["loop", m, v, [v, …], [v, …], region]             maximum, count, carried, captures
["match", v, [v, …], [region, …]]
["guard", reason, v]
["stop", reason]                                   last instruction of its region
reason = "reject" | "abort" | "exhausted" | "refused"
```

An `if` region receives the captures. A `loop` region receives the iteration
number, the carried values and the captures, and returns the carried values. A
`match` region receives the alternative's value and the captures.

Protocol instructions:

```text
["at", r, local]                                   local: any local instruction but "stop"
["exchange", s, r, site, v]
["draw", o, [r, …], site, law, [v, …]]             receivers in increasing order
["sample", o, site, law, [v, …]]
["repeat", [[r, v], …], m, [v, …], [v, …], region] participants with counts, maximum, carried, captures
["branch", [[r, v], …], [v, …], region, region]    participants with conditions, captures
["apply", d, [r, …], site, [v, …]]                 role map: formal role j runs as the j-th entry
["oracle_send", s, [r, …], site, v]
["oracle_compute", o, d, [v, …], [v, …]]           parents, captures
["oracle_read", o, site, [[v, v], …]]              per handle: handle, array of positions
```

A region nested in `["at", r, …]` is a local region over `r`'s values. A `repeat`
region receives the carried values and the captures and returns the carried
values. A protocol `guard` is `["at", r, ["guard", reason, v]]` and has no site of
its own; its position in the body identifies it.

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

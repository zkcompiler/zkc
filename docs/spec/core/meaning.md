# Core language: meaning

## Models

A model gives every type a set of values and every catalogue operation a meaning:
a pure row a function, a partial row a function into values or stops with an
authored reason, a sampling row a distribution. `unit`, `bool`, `index`, arrays, tuples and variants have their
standard values. Nominal types and catalogue operations are the model's choice. A
statement about a program holds for the models that satisfy the laws the statement
names; a deployment fixes one model.

## Functions

A function denotes a map from its inputs to its outputs or a stop. Local
operations have the meanings of the [language chapter](language.md#local-operations).
A stop ends the function and everything that called it.

## Effects

A set `H` of a protocol's roles is a side. The meaning of a protocol for `H` is the
process of the roles in `H` acting together. A process is a tree: it returns, stops,
or performs an effect and continues with the reply.

| Effect | Reply | Performed when |
|---|---|---|
| `send(site, value)` | none | a role in `H` sends to a role outside `H` |
| `receive(site, T)` | a value of `T` | a role in `H` receives from a role outside `H` |
| `draw(site, law, inputs)` | a value of the law's output type | a role in `H` draws a public coin |
| `sample(site, law, inputs)` | a value of the law's output type | a role in `H` samples a secret |
| `read(site, position)` | none | a role in `H` reads an oracle |

A reply is unconstrained by the process. Who answers is fixed by the experiment
that runs the process: an adversary answers `receive`; `draw` and `sample` are
answered from their laws, or as the experiment's model of the challenge source
says.

A site in an effect is a pair of the definition and its local site number. An
effect does not name the role outside the side that it reaches. Everything outside
the side is one adversary: it sees every `send` and `draw`, and answers every
`receive`. An experiment that separates several outside parties needs their
identities and is outside this meaning.

## The meaning of a protocol for a side

A value of type `T @ r` exists for `H` exactly when `r` is in `H`. The side's
environment holds the values of its roles and nothing for the others.

| Operation | Meaning for side `H` |
|---|---|
| `at(r, ℓ)` | if `r ∈ H`, the local operation on `r`'s values; otherwise nothing |
| `exchange(s, r, site)` | `s, r ∈ H`: the result is the operand. `s ∈ H` only: `send`. `r ∈ H` only: `receive`, and the result is the reply. Neither: nothing |
| `draw(o, R, site, law)` | `o ∈ H`: `draw`; every result held by a role in `H` is the reply. `o ∉ H`: each receiver in `H`, in increasing order, performs its own `receive`, and its result is its own reply |
| `sample(o, site, law)` | `o ∈ H`: `sample`. Otherwise nothing |
| `guard` at `r` | if `r ∈ H`, stops with the reason when the condition is false |
| `repeat(P, m)` | if no role of `P` is in `H`, nothing. If the counts held by the roles of `P ∩ H` differ, stops `incomplete`. Otherwise, if the count exceeds `m`, stops `refused`. Otherwise the region is run for `H` that many times |
| `branch(P)` | if no role of `P` is in `H`, nothing. If the conditions held by the roles of `P ∩ H` differ, stops `incomplete`. Otherwise the selected region |
| `apply(d, ρ, site)` | the meaning of `d` for the side `{ j : ρ(j) ∈ H }` |
| `oracle_send(s, R, site)` | as an exchange of the table from `s` to each role of `R` |
| `oracle_compute(o, d)` | if `o ∈ H`, the handle that records the parents and the captured values |
| `oracle_read(o, site)` | if `o ∈ H`: as described under [reads](#reads) |

"Nothing" means the operation performs no effect and its results, which no role of
`H` holds, do not exist for `H`.

## Agreement

A side with one role is that role's own execution. A side with several roles is
their joint execution, and it is defined as one process only while its roles agree
on every control value they share.

- An adversary can give two honest roles different values: each `exchange` and
  each announcement of a `draw` from outside the side is a separate `receive`.
  Nothing in the meaning assumes a broadcast channel.
- At a `repeat` or a `branch`, the roles of the side that participate must hold
  equal copies. If they do not, the side stops with the reserved reason
  `incomplete`: the roles would go separate ways, and no single process describes
  them.
- A stop by any role of the side ends the side's process. Alone, the other roles
  of the side would go on until they needed something from the stopped role.
- A statement about a side with several roles therefore shows two things: that
  `incomplete` is unreachable, and that a stop by one role leaves no other role of
  the side able to reach a decision. The second holds, for instance, when every
  role of the side but one performs no guard and no partial operation. Under both,
  the joint process restricted to any one of the side's roles is that role's own
  execution, with the other roles of the side as part of its environment.

In a two-party proof the sides used for soundness and zero knowledge have one
role. With a setup role they have two, the setup and the verifier or the setup and
the prover; agreement is then in question only if the setup takes part in a
`repeat` or a `branch`. For completeness every role is in the side, and the copies
are equal because honest roles compute them from equal inputs.

## Sides in use

Three sides matter most.

| Side | Its effects | Used for |
|---|---|---|
| every role but the prover | `receive` for prover messages, `draw` for challenges, `sample` for setup secrets | soundness, knowledge soundness |
| the prover, with a setup role | `send` for the prover's messages and for what the setup gives the verifier, `receive` for challenges, `sample` for its secrets | zero knowledge |
| every role | `draw` and `sample` only | completeness |

The meaning for a single role is the participant the compiler projects.

## Ideal and deployed interpretations

A handle of a `sent` oracle denotes, for a side that holds it, the table: an
extent, which is a decidable set of positions, and a row for each position in it.
A `sent` handle received from outside the side is a logical message: the reply to
its `receive` is the whole table. The side never computes with the whole table; it
performs `read`s, whose results the table determines. A computed handle denotes its
parents and captured values; its table is the one its definition gives for them,
and a read of it is carried out on the parents. This is the ideal interpretation.

### Reads

A `read` effect names a `sent` handle and one position. Only reads of `sent`
tables are effects: they are what an adversary observes and what a budget counts.

A read operation proceeds in three steps.

1. Every requested position is tested against the extent of its handle, in the
   order of the operation's handles and of each handle's positions. The first
   failure stops the side with `refused`, before any effect of the operation.
2. For a `sent` handle, one `read` effect per requested position, in order,
   repeated positions included.
3. For a computed handle, the definition's position function gives, for each
   requested position, the positions to read in each parent; the parents are read
   by this same procedure; the definition's answer function gives the row.

The result of a read of a computed handle equals its table at the position. That
is a property of the definition, used by relations over the table; the process is
the one above.

A [stage](stages.md) replaces operations on an ideal type by operations on
deployed data: a table by a commitment and openings, a challenge by a hash of the
transcript. Properties are proved of the ideal program and carried to the deployed
one by the stage's theorem.

A type that the source uses in deployed form can be read ideally by the formal
library without a compiler stage. A group element that a side receives in a
protocol with a secret setup is read as a linear form over the setup's published
elements; the step back to the group is a model assumption named in the result.

## What the meaning does not include

The meaning has no scheduling, no encoding of messages into bytes and no notion
of time. The order of effects is the order of operations in the body. Encodings
enter when a stage introduces explicit encoding operations.

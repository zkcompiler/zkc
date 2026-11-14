# Core language: meaning

## Models

A model gives every nominal type a set of values and every catalogue operation a
meaning: a pure row a total function, a restricted row a function on its domain,
which has no value outside it, a sampling row a distribution on its output type, which
has a value. A model also gives
every literal of a nominal type its value, so every nominal type has a value.
`bool`, `nat`, `fin n`, sequences, tuples, records and variants have their standard
values, and the operations the core owns have the values the
[language chapter](language.md#operations-the-core-owns) gives them. A type may have
no value: `fin 0`, a variant without alternatives, or a type that needs one of them.
Nominal types and catalogue operations are the model's choice. A
statement about a program holds for the models that satisfy the laws the statement
names; a deployment fixes one model.

## Functions

A function denotes a map from its inputs to its outputs or a stop. Local
operations have the meanings of the [language chapter](language.md#local-operations).
A stop ends the function and everything that called it.

A restricted row applied outside its domain, and an operation the core owns applied
outside its domain, stop with the reserved reason `undefined`. No `guard`, no `stop`
and no function names it.

### Functions that pass the check of facts

A model satisfies the *domain laws* of an operation table when every restricted row
that names a domain row has a value exactly where the domain row gives `true`. The
laws say nothing of a restricted row without a domain row.

For every model that satisfies the domain laws: a function whose body passes
[the check of facts](language.md#the-check-of-facts), in a program whose earlier
functions all pass it, never stops `undefined`, on any arguments. In a program all
of whose functions pass, the process of every function on every arguments has no
`undefined` stop. The statement holds for the meaning as it is defined: the meaning
reads no justification, and an application outside its domain would stop. The model
that gives the rows of the source vocabulary their values satisfies the domain laws of
the table of every package whose rows are the vocabulary's, by name, static arguments,
kind, inputs and outputs.

The proof keeps one invariant along the body: every bound contains its value, every
order holds, every known condition is `true`, and every shape is the operation that
made the value. A justified application is then inside its domain. The facts of a
region that never runs hold of no environment: a loop of no iteration gives its region
none, and no environment gives a value of a type without one.

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
| `repeat(P, c)` | if no role of `P` is in `H`, nothing: the carried results are the operands, and no sequence is held in `H`. For a count that is a value: if the counts held by the roles of `P ∩ H` differ, stops `incomplete`; otherwise, if the count exceeds the maximum, stops `refused`. Otherwise the region is run for `H` as many times as the count, the number of the operation or the agreed value; in the iteration `i`, counted from 0, every role of `P ∩ H` holds `i`, and every holder in `H` of a collected entry keeps the value of the iteration. Its sequence is the values of the iterations in order |
| `choose(P, t)` | if no role of `P` is in `H`, nothing. If the tags held by the roles of `P ∩ H` differ, stops `incomplete`; two copies of a variant differ when they are different alternatives. Otherwise the region the tag selects. The region of an alternative of a variant takes the payload of every role of `P ∩ H`, each from that role's own copy; the payloads of the other roles of `P` do not exist for `H` |
| `apply(d, ρ, site)` | the meaning of `d` for the side `{ j : ρ(j) ∈ H }` |

"Nothing" means the operation performs no effect and its results, which no role of
`H` holds, do not exist for `H`.

### Protocols that pass the check of facts

For every model that satisfies the
[domain laws](#functions-that-pass-the-check-of-facts) and every side `H`: the
meaning for `H` of a protocol whose body passes
[the check of facts](language.md#facts-in-a-protocol-body), in a program whose
functions and earlier protocols all pass it, never stops `undefined`, on any values
of its inputs and under any applications that reached it. The statement holds
whatever the roles outside `H` do: their values reach `H` as the replies of its
effects, and the statement holds through every reply of every effect. In a program
that passes, the process of every protocol for every side has no `undefined` stop.

The proof keeps the invariant of the local check for the roles of `H` only: what a
role of `H` knows holds of the values that `H` holds, and nothing is required of what
a role outside `H` knows. This is sound because a fact of one role mentions values of
that role alone, and a role outside `H` performs nothing in the process of `H`. A role
that holds a value of a type without a value is stopped by the check for the same
reason: a side that contains the role has no values to run on, and a side that does
not contain it performs none of the role's applications.

A stop `incomplete`, where two roles of `H` disagree on a count or a tag, and a stop
`refused`, where a count exceeds its maximum, are not `undefined`; the statement says
nothing of them.

The program that projection gives a role has the process of the protocol for the
side of that role alone. So in a program that passes, the program of every role of
every protocol never stops `undefined`, on any arguments and whatever it receives.

### Protocols that pass the check of copies

For every model, every protocol of a program that passes
[the check of copies](language.md#the-check-of-copies), every side `H` that supports
the requirements that the check found for the protocol, and every values of its
inputs of which the copies of each agreement that `H` holds are equal: the meaning of
the protocol for `H` never stops `incomplete`, whatever the replies of its effects,
and of the values it returns the copies of each agreement of outputs that `H` holds
are equal. The side of every role supports every requirement, so the statement holds
for it with no condition on the side.

The statement is about a program as written. It is not made of what a
[stage](stages.md) returns, on which the check is not run, and so not of the program
that projection gives a role of a constructed scheme.

## Agreement

A side with one role is that role's own execution. A side with several roles is
their joint execution, and it is defined as one process only while its roles agree
on every control value they share.

- An adversary can give two honest roles different values: each `exchange` and
  each announcement of a `draw` from outside the side is a separate `receive`.
  Nothing in the meaning assumes a broadcast channel.
- At a `repeat` over a count that is a value or a `choose`, the roles of the side
  that participate must hold equal copies. If they do not, the side stops with the
  reserved reason `incomplete`: the roles would go separate ways, and no single
  process describes them. Copies of a variant that is the tag of a `choose` need
  only be the same alternative: the roles then follow one region, each with its
  own payload, and nothing compares the payloads.
- A stop by any role of the side ends the side's process. Alone, the other roles
  of the side would go on until they needed something from the stopped role.
- A statement about a side with several roles therefore shows two things: that
  `incomplete` is unreachable, and that a stop by one role leaves no other role of
  the side able to reach a decision. The second holds, for instance, when every
  role of the side but one performs no operation that stops. Under both,
  the joint process restricted to any one of the side's roles is that role's own
  execution, with the other roles of the side as part of its environment.

In a two-party proof the sides used for soundness and zero knowledge have one
role. With a setup role they have two, the setup and the verifier or the setup and
the prover; agreement is then in question only if the setup takes part in a
`repeat` or a `choose`. For completeness every role is in the side, and the copies
are equal because honest roles compute them from equal inputs.

## Sides in use

Three sides matter most.

| Side | Its effects | Used for |
|---|---|---|
| every role but the prover | `receive` for prover messages, `draw` for challenges, `sample` for setup secrets | soundness, knowledge soundness |
| the prover, with a setup role | `send` for the prover's messages and for what the setup gives the verifier, `receive` for challenges, `sample` for its secrets | zero knowledge |
| every role | `draw` and `sample` only | completeness |

The meaning for a single role is the participant the compiler projects.

## Runs

A side's process leaves every reply open. A run fixes who answers.

A *sampler* answers draws and samples. It gives a value of the type for every site,
every count and every populated type: the `k`-th draw or sample at a site is answered by
the sampler's `k`-th coin of that site, at the output type of the law. The output type of
a law is populated ([catalogue operations](language.md#catalogue-operations)), so a
sampler answers every request of a process; at a type without a value it has no coin,
and nothing asks for one. Every model has a sampler. A statement for every sampler is a
statement for every outcome of the coins and says nothing of their distribution.

- **One process.** A process that neither sends nor receives *returns* a value under a
  sampler when it returns that value with every draw and sample answered by the
  sampler.
- **Two processes.** Two processes run against each other *return together* two values
  under a sampler when some order of their steps ends with both returned. A `send`
  puts its value in the mail of its site. A `receive` takes the oldest message of its
  site or, when no message is in transit there, hears a coin of its site. A `draw` is
  answered by the sampler and announces its coin at its site. A draw is a broadcast in
  order: the coins of a site stay announced in the order of their draws, each process
  hears them one after another, and a coin that nobody hears leaves nothing in transit. A `sample` is answered by the sampler. Either process may take the
  next step: the relation fixes no schedule.

A protocol is *complete* for a condition on its outputs when, for every sampler, its
meaning for the side of every role returns outputs that the condition holds of. A
protocol whose verifier stops on every run is complete for no condition.

The *endpoint lemma* relates the programs of two roles to the meaning of the protocol.
For every protocol of a program, two disjoint sides that each contain exactly one role
of the protocol, and every sampler: when the meaning for the union of the two sides
returns outputs, the programs that projection gives the two roles, run against each
other from an empty mail with the same sampler and the same counts, return together what
each role holds of those outputs. The lemma is a statement about the relation above; the
functions of the program perform no effect.

An *executor* is such a program. It runs processes under one schedule and a source of
coins, the `k`-th coin of a site at a type, which gives a sampler; a run always ends,
since every effect continues one process and a process has no infinite path. Its runs
are related to the relations above as follows.

- A run of one process that returns values is a return of the process under that
  sampler, and a run that stops is a stop of the process with that reason.
- A run of two processes in which both return is a return together of the two: the
  executor gives a receiver the coins of a site one after another, as the relation does.
- A run under the [limit on the work of reading](stages.md#the-limit-on-the-work-of-reading)
  that returns or stops is a run of the meaning without the limit.

Nothing is stated of a run of three or more processes, of a run in which a process
fails or waits, or of the converse, that a return of the relation is found under the
executor's schedule.

A scheme that the [Fiat–Shamir and serialize stages](stages.md#what-the-two-rewrites-preserve)
derive is *complete* for a condition when, for every sampler, the prover's program run
alone returns a proof on which the verifier's program run alone returns outputs that the
condition holds of. It is complete for the condition of the interactive protocol when:

- the interactive protocol is complete for every sampler, for the side of the prover and
  the verifier together;
- the prover's and the verifier's copies of the statement are equal in the inputs;
- the suite's operations return;
- the wire layout reads back what it writes: what the reader takes from the bytes of a
  written value followed by anything is the value and what follows, a writer starts
  empty, the reader of a closed writer has its content, and a reader with nothing left
  is exhausted;
- every value that the interactive prover sends is one that the layout writes.

The canonical layout has these laws in the model of the source vocabulary; for a type
that contains a point of the group they rest on the named hypothesis that the compressed
bytes of a point are read back as the point. A value of a prime field that the model's
arithmetic gives is written; that a multiple of a point of the group is written needs the
closure of the group under multiples, which is a named hypothesis.

## What the meaning does not include

The meaning has no scheduling, no encoding of messages into bytes and no notion
of time. The order of effects is the order of operations in the body. Encodings
enter when a stage introduces explicit encoding operations.

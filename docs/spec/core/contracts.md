# Core language: contracts and the proof declaration

A contract states what a definition promises. It is data attached to the
definition, typed over the definition's formals, and has no effect on execution.
The formal library turns each clause into a statement about the definition's
[meaning](meaning.md); the author of the definition proves it.

## Relations

A relation has typed parameters and one of two meanings.

| Form | Meaning |
|---|---|
| Formula | a function of the program returning `bool`; the relation holds when it returns true |
| External | a pair of predicates defined in the formal library, `yes` and `no`, that never hold together. A claim that a relation holds refers to `yes`; a claim that it fails refers to `no` |

An external relation with a gap between `yes` and `no` states a promise: proximity
to a code within one radius against distance beyond another, or a witness for a
relation against none for a relaxed relation.

A relation over an oracle handle is a relation over the handle's table.

## Logical parameters

A protocol's contract may bind logical parameters: typed values that no role holds
and no operation computes, such as the table behind a prover's oracle, a witness,
or a linear form. Clauses refer to them; statements quantify over them.

## Selectors

A clause names its arguments by selector.

| Selector | Denotes |
|---|---|
| `input(i)` | the protocol's `i`-th input |
| `output(j)` | its `j`-th output |
| `logical(k)` | its `k`-th logical parameter |
| `table(s)` | the table of the oracle handle selected by `s` |
| `field(s, i)` | component `i` of the tuple selected by `s` |

Two clauses of one contract that use the same selector speak of the same value.

## Clauses

| Clause | Arguments | Reading |
|---|---|---|
| `requires R(a…)` | a relation and its arguments | assumed by every other clause of the contract |
| `reduces R(a…) to S(b…)` | two relations | if `R` fails at entry then `S` fails at exit, up to the bounds of the definition's sites; with rewinding evidence, a witness for `S` at the leaves of a tree of challenges gives a witness for `R` |
| `target R(a…) accept o` | a relation and a `bool` output | if `R` fails at entry the output is false, up to the bounds |
| `knowledge R(a…; w) by e` | a relation, the witness position, an extractor | an accepting execution yields, through extractor `e`, a witness `w` with `R(a…; w)` |
| `zero_knowledge by s` | a simulator | the view of the corrupted roles in an honest execution has the distribution that `s` produces |
| `invariant R(a…) at ℓ` | a relation and a `repeat` of the body | `R` holds at each iteration boundary of loop `ℓ`, numbered in order of occurrence |
| `bound site ≤ e` | a site and a bound expression | the claimed charge of the site |
| `binding`, `extractable` | on a commitment scheme | the premise of the scheme's stage |

A clause does not say how it is proved. The kind of evidence is chosen by the claim
that uses the contract.

## Agreements

An agreement is a set of inputs, or of outputs, of one protocol that are copies of
one source value held by several roles: ports of one type with different holders,
each named once. An honest execution starts with equal
copies. A statement about a side that holds one copy refers to that copy.

## Specification-only programs

A function or protocol marked specification-only is part of the package and is
never applied by a deployed definition. Simulators and extractors are such
programs. An extractor is a function from the transcripts it needs to a witness.
A simulator is a protocol or function whose outputs are the corrupted roles'
view. Tests execute them; the formal library reasons about them as about any
other definition.

## The proof declaration

A proof declaration selects a protocol and fixes how it is deployed.

| Field | Content |
|---|---|
| Protocol | the definition |
| Roles | which role is the prover, which the verifier, and which, if any, the setup |
| Statement | the verifier's inputs that form the public statement, in order, each with its encoding |
| Acceptance | the verifier's `bool` output that decides |
| Reference string | for a protocol with a setup role: the setup's outputs, and the asset that carries them at deployment with its digest |
| Construction | `derived` with a suite, `authored`, or `none` |
| Suite | the hash, the challenge decoder, the labels and the domain separation, as data |

With a `derived` construction the Fiat–Shamir [stage](stages.md) produces the
non-interactive program. With an `authored` construction the source computes its
challenges by explicit hashing and marks each hash-derived challenge; the hash
input of a marked challenge determines everything the roles have exchanged so far.
With `none` the protocol has no challenge.

## Claims

A claim names a property (soundness, knowledge soundness, zero knowledge,
completeness), a relation, the corrupted roles, a model, the last stage it covers
and a bound. The default corrupted roles are the prover for soundness and
knowledge soundness, the verifier for zero knowledge, and none for completeness.
A claim is a request; the formal library answers it with a proved statement and
the list of what that statement assumes.

# The core language

The core language is the typed representation of a protocol between the source
language and the programs that its roles run. A producer writes a program of it as
a package; the Core package (`lean/compiler/Zkc/Core`) admits the package, applies the stages
of a scheme and projects the result to one program per role. Every statement about
a protocol is a statement about the meaning of a core program.

| Chapter | Content |
|---|---|
| [Language](language.md) | Types, holders, definitions, operations, the check of facts, the check of copies, admission, sites and well-formedness |
| [Meaning](meaning.md) | Effects, the meaning of a program for a set of roles, what an admitted program never does, runs |
| [Agreements and the declaration](contracts.md) | Agreements, specification-only programs, the declaration of a scheme |
| [Package](package.md) | `zkc.core/0`: the positional serialization of a program |
| [Stages](stages.md) | Stage tables, Fiat–Shamir, serialization, layouts, what the stages preserve |

## Position

```text
package (program as written)
   │  admission
   ▼
admitted program ── Fiat–Shamir ── serialization ──► constructed program
   │                                                      │
   └───────────────────── projection ─────────────────────┘
                              ▼
                        role programs ──► run by the executor
```

A package is a program as its producer wrote it. Admission is the one gate between
a package and everything after it. The two [stages](stages.md) of a declared scheme
rewrite the admitted program, and what each returns is admitted again. Projection
gives the program of each role, of the written protocols or of the constructed
scheme. The executor of the Core package runs role programs against each other
under a model of the catalogue's rows.

## The model in brief

- A program is an ordered list of definitions: functions and protocols. A protocol
  applies another protocol; an application stays an application through every
  stage.
- A protocol has numbered roles. Every value in a protocol body has a type and
  exactly one holder, a role. A source value held by several roles is one core
  value per holder.
- An operation is owned by one role and uses values that role holds. The only
  operations that move information between roles are `exchange` and `draw`.
- Randomness is of two kinds. `draw` is a public coin, announced to named
  receivers. `sample` is a secret.
- The meaning of a protocol is defined for every set of its roles taken as a side:
  the process of those roles together, whose effects are the messages that cross
  the side's boundary and the random replies of its own draws and samples.
- A role accepts by returning. A guard is how a body rejects, and a stop of a role
  is a rejection by that role whatever its reason.
- Every interaction and random choice carries a site: a number local to its
  definition.

## What this specification covers

It covers what the Core package defines and reads. Three things that an earlier
version of these chapters described are not part of it.

- **Oracles.** There is no oracle type, row or operation, and no stage that
  commits to a table. A package whose program has an oracle row is refused. How a
  protocol publishes data that another role queries is not specified yet.
- **Properties.** Relations, clauses and claims are not part of a package: the
  `contracts`, `proof` and `parameters` positions of the envelope are empty. What
  is stated here of every admitted program is in the [meaning](meaning.md) and
  [stages](stages.md) chapters; no statement of soundness, knowledge or zero
  knowledge is part of this specification.
- **Native execution.** Role programs are run by the executor of the Core package.
  Their lowering to native code is not specified here.

## Consumers

| Consumer | Uses |
|---|---|
| A producer | writes a package and states beside it what [admission](language.md#admission) checks |
| The Core package | reads a package, admits it, applies the stages of a declaration, projects, runs role programs; its theorems are about these definitions |
| A proof about a program | reads the meaning of an admitted program for a side |

## Identity and versions

The format tag is `zkc.core/0`. A package is identified by the SHA-256 of its
canonical bytes. Tables are positional: a reference is a number, and no consumer
resolves a reference by name. Names sit in a side table that carries no meaning.

## Implementation

The Core package implements every chapter: the reader and printer of the format,
elaboration, admission, the meaning, projection, the two stages, the canonical
layout and the executor. `core-tool admit` and `core-tool compile` are its
admission and its compilation on a package read from a file
([package guide](../../../lean/compiler/Zkc/Core/README.md)).

# The core language

The core language is the one typed representation of a protocol that the frontend
emits, the security-relevant compiler stages rewrite, and the formal library reads.
A security statement is a statement about the meaning of a core program.

| Chapter | Content |
|---|---|
| [Language](language.md) | Types, holders, definitions, operations, typing and sites |
| [Meaning](meaning.md) | Effects, the meaning of a program for a set of honest roles, ideal interpretations |
| [Contracts](contracts.md) | Relations, logical parameters, clauses, specification-only programs, the proof declaration |
| [Package](package.md) | `zkc.core/0`: the positional serialization of every stage of one compilation |
| [Stages](stages.md) | Stage tables and the three security-relevant stages |

## Position in the pipeline

```text
.zkc ─► frontend ─► core₀ ─► core₁ ─► core₂ ─► core₃ ─► expansion ─► projection ─► exec ─► physical
                    original  unfolded committed constructed
```

Every `core` is a program of this language. The frontend's closed, typed model is
emitted into `core₀` once. Each later `core` is the previous one rewritten by one
[stage](stages.md). Application expansion, participant projection and the
execution profiles follow the last stage and preserve meaning.

## The model in brief

- A program is an ordered list of definitions: pure functions, protocols, computed
  oracles and relations. A protocol applies another protocol; an application stays
  an application through every stage.
- A protocol has numbered roles. Every value in a protocol body has a type and
  exactly one holder, a role. A source value held by several roles is one core
  value per holder.
- An operation is owned by one role and uses values that role holds. The only
  operations that move information between roles are `exchange`, `draw` and the
  oracle operations.
- Randomness is of two kinds. `draw` is a public coin, announced to named
  receivers. `sample` is a secret.
- The meaning of a protocol is defined for every set of roles taken as the honest
  side: the process of those roles together, whose effects are the messages that
  cross the side's boundary and the random replies of its own draws and samples.
- Every interaction and random choice carries a site: a number local to its
  definition.

## Consumers

| Consumer | Uses |
|---|---|
| Compiler stages | read one `core`, write the next |
| Expansion and projection | read the last `core` |
| Formal library | type-checks every `core` of a [package](package.md), recomputes each stage from the previous one, and proves properties of the side meanings |
| Tests | execute side meanings on vectors and compare with the virtual machine |

## Identity and versions

The format tag is `zkc.core/0`. A package is identified by the SHA-256 of its
canonical bytes. Tables are positional: a reference is a number, and no consumer
resolves a reference by name. Names, source spans and digests of external assets
sit in side tables that carry no meaning.

## Implementation

The [formal model](../../../lean/docs/spec/core-language.md) implements types (all
but oracle handles), located types, sides, models, the effect signature, the local
dialect (`op`, `call`, `if`, `loop`, `guard`, `stop`), the protocol dialect (`at`,
`exchange`, `draw`, `sample`, `repeat`, `branch`, `apply`), agreements as part of a
protocol's signature, the meaning of functions, the meaning of protocols for every
side with the agreement rule, and the residual well-formedness conditions, which
the kernel decides for every definition it accepts. Its importer reads the program
of one selected stage (`original` by default) of a `zkc.core/0` package into
kernel-checked definitions; it type-checks that stage only, and recomputes no
stage. It is exercised on three hand-written packages: a Schnorr proof (the example
of the package chapter), a Sumcheck, and a polynomial opening with a setup role.
The compiler does not yet write packages. Oracle rows and operations, `match`,
computed oracle and relation definitions, contracts and stage tables are specified
here and not yet read by any consumer.

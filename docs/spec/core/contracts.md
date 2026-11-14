# Core language: agreements, specification-only programs and the declaration

Three kinds of data say how a definition is meant to be used. None changes the
[meaning](meaning.md) of a body.

## Agreements

An agreement is a set of inputs, or of outputs, of one protocol that are copies of
one source value held by several roles: ports of one type with different holders,
each named once. An honest execution starts with equal copies. A statement about a
side that holds one copy refers to that copy.

Admission checks the copies of a body against the agreements of its header
([the check of copies](language.md#the-check-of-copies)): a protocol that passes,
run on inputs whose agreed copies are equal, returns outputs whose agreed copies
are equal.

## Specification-only programs

A function or protocol marked specification-only is part of the package and is
never applied by a deployed definition. Such a program states something about a
protocol, an extractor or a simulator for example, and no role runs it. Tests
execute it, and a statement is made of it as of any other definition.

## The declaration

A declaration selects a protocol of a package and fixes how it is deployed as a
scheme. It is a document of its own, beside the package.

```text
declaration = ["declaration", entry, prover, verifier, suite, layout]
            | ["declaration", entry, prover, verifier, suite, layout, [online role, …]]
suite       = null
            | ["catalogue", state type, label type row, start row, [absorbing row, …],
               [[law row, deriving row], …], [proof identity number, …]]
            | ["source", state type, start function, [absorbing function, …],
               [[law row, deriving function], …], [[site row, …], …]]
site row    = [site, row] | [site, row, prover, verifier]
layout      = null
            | ["canonical", writer type, reader type, proof type, open row, close row,
               read row, exhausted row, [putting row, …], [taking row, …]]
```

| Field | Content |
|---|---|
| Entry | the protocol, by its number among the protocols of the package |
| Prover, verifier | the two roles of the entry whose transcript the scheme derives |
| Online roles | the roles of the entry that take part in a run; the prover and the verifier when the list is absent |
| Suite | the transcript that the Fiat–Shamir [stage](stages.md#fiatshamir) reads: the type of its state and the rows or functions that start it, absorb a message of each type and derive a value of each law |
| Layout | the proof that the serialization [stage](stages.md#serialization) reads: the types of its writer, of its reader and of the proof, and the rows that open, close, put and take |

Every reference is the number of a row of the operation table or of a function of
the package. A stage resolves a number when it uses it, and refuses a declaration
whose number names a row of another signature. A scheme is constructed by both
stages, so its declaration has a suite and a layout; a stage refuses a declaration
without the one it reads.

A scheme has no output that says whether the verifier accepted. The verifier
accepts by returning: a stop of the verifier is a rejection, whatever its reason,
and a guard is how a body rejects.

The [proof identity](package.md#identities) is computed over the package and the
declaration, and a catalogue suite carries it in the declaration that a stage reads.

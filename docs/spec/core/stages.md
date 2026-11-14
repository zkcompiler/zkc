# Core language: stages

A stage rewrites one core program into the next. The two stages between the
program as written and the constructed one, Fiat–Shamir and serialization, are the
only compilation steps that change what a security statement has to assume. Each is
defined by a table.

## Stage tables

A stage table consists of the stage's name, the type of the state it threads, its
parameters and its rows. A row has a pattern and a template.

| Part | Content |
|---|---|
| Pattern | an operation form, with conditions on its attributes: owner, receivers, types, the row of a catalogue table |
| Template | a region. Its inputs are the matched operation's operands followed by the state values of the roles the row names; its outputs are the operation's results followed by the new state values |
| State | a type and its initial value per role, or none |
| Parameters | values of the declaration on which the template may depend |

The rewrite of a definition replaces every operation that matches a row by the
row's template, instantiated at the operation's attributes, and leaves every other
operation unchanged. When the stage has a state, each protocol takes and returns
one state value per role that the stage names, and an application passes them
through. A loop whose region is rewritten carries them from one iteration to the
next; the sequences that the loop collects are unchanged.

A template mentions only the matched operation. A stage therefore commutes with
sequencing, loops, branches and applications, and rewrites one definition at a
time. The stages are definitions of the Core package: compilation applies them,
and what a rewrite preserves is proved once, for the table, about the definition
that compilation applies.

The parameters of the two stages are in the
[declaration](contracts.md#the-declaration): the transcript roles, the suite and
the layout.

## Fiat–Shamir

Parameters: the transcript roles `T` (the prover and the verifier of the proof
declaration), and the suite. State: one transcript value per role of `T`.

| Pattern | Template |
|---|---|
| entry of the declared protocol | each role of `T` absorbs the public statement, in the declared order and encoding |
| `exchange(s, r, site)` with `s, r ∈ T` | the exchange; then `s` and `r` each absorb the site label and the encoded value |
| `draw(o, R, site, law)` with `o ∈ T` and `R = T ∖ {o}` | each role of `T` absorbs the site label and derives the value from its transcript with the suite's decoder; nothing is exchanged |
| `sample`, and an `exchange` with a role outside `T` | unchanged |

A `draw` of any other shape has no row; a program that contains one is refused by
this stage.

### Transcript discipline

- The suite's domain separator is absorbed first and names the proof: it includes
  the [proof identity](package.md#identities), which is fixed before this stage
  runs.
- The statement is absorbed next, by an operation of the constructed program.
- A label is the site: the definition and its local site number. The path of
  applications and the iteration number are not absorbed. Two executions of one
  site differ in the transcript absorbed before them.
- Every value the suite absorbs is an explicit operation with an explicit
  encoding.
- A decoder that rejects and retries is a sampling law with a stated factor; its
  extra hash calls belong to the site.
- An authored construction is not rewritten. Its marked challenges are its sites.

### Serialization

After the Fiat–Shamir rewrite, or in a protocol whose construction is authored, the
prover's messages to the verifier are carried in one proof. Parameters: the prover,
the verifier and a wire layout. State: a writer at the prover and a reader at the
verifier.

A wire layout consists of the types of the writer, the reader and the proof, and
rows of the package: one that opens a writer, one per message type that puts a value
on it, one that closes it into the proof, one that opens a reader on the proof, one
per message type that takes a value from it, and one that tests whether it is
exhausted. Every row of the layout is pure, so the writer, the reader and the proof
are populated types.

| Pattern | Template |
|---|---|
| entry of the declared protocol | the proof becomes a first input of the verifier and a first output of the prover. The prover opens a writer and, after the body, closes it into the proof; the verifier opens a reader on the proof and, after the body, guards with `reject` that the reader is exhausted |
| `exchange(s, r, site)` from the prover `s` to the verifier `r` | `s` puts the value on its writer; `r` takes from its reader a flag, a value of the type and the rest of the reader, and guards the flag with `reject`. Nothing is exchanged, and the site is gone |
| `exchange` of a type that has no value | refused: no row takes a value of it |
| `draw` between the prover and the verifier | refused: the program still needs a transport |

The row that takes is pure: its outputs are `bool`, the message type and the reader.
The flag says whether the reader had a value of the type, and the value is any value
of the type when it had none. On a proof that is too short or malformed the verifier
therefore stops `reject`.

### The canonical layout

The layout `zkc::layout::canonical` has bytes for its writer, its reader and its
proof. It writes a value of a type as the format of the type. A format states the
values it writes, its domain; a writer; a reader, which gives the value at the front
of bytes and the bytes after it; and the width of its values when they all have
one. One description of a type gives all four, and a type is written exactly when
it has a format.

| Type | Bytes |
|---|---|
| `index<n>` | the number in the least `k` bytes with `n ≤ 256^k`, least significant first. `index<1>` takes no bytes, a byte one, `index<2^64>` eight, `index<2^65>` nine. A number not below `n` is not read |
| `bool` | as `index<2>`: one byte |
| `nat` | groups of seven bits, least significant first, the high bit of a byte saying that another group follows, and no last group of zero except for the number 0: unsigned LEB128 in its shortest form. Every other form is not read |
| a collection with a size | its elements, one after another |
| a collection without a size | its length as a `nat`, then its elements |
| a tuple | its components, one after another. The tuple of no component, and every type built from parts of no bytes, takes no bytes |
| `nonzero<F>` | as `F`; zero is not read |
| an element of a prime field | its natural in the width of the field, least significant first. A natural not below the order is not read |
| an element of an extension | its coefficients, lowest first, each as an element of the base |
| a point of `bls12-381.g1` | 48 bytes, the compressed form of the ZCash serialization format (draft-irtf-cfrg-pairing-friendly-curves-11, appendix C). Bytes that are not those of a point of the group are not read |

Every value of a type that has a format is in the domain of the format: no writer
drops a part of a value, and no value is written as another. A record and a variant
are not message values of this layout.

A format has two laws.

- *Round trip of a prefix.* For a value of the domain and any bytes after it, the
  reader on what the writer wrote, followed by those bytes, gives the value and
  those bytes.
- *Canonical.* When the reader on bytes gives a value and the bytes after it, the
  value is of the domain and the bytes are what the writer writes for it, followed
  by the bytes after it.

So the writer is injective on the domain, the bytes of one value are never a proper
prefix of the bytes of another, and what a reader accepts does not depend on what
follows the value. The laws of a type follow from its structure: each way of
building a format (a number in a fixed width, a natural of variable length, a pair, a
tuple, a repetition of a fixed count, a repetition after its count, a refinement)
has the two laws when its parts have them. For the row that puts and the row that
takes: a reader given the bytes that the writer wrote for a value, followed by
anything, gives the flag `true`, the value and what follows.

The laws of a type with a point of G1 in it take one hypothesis, by name: the bytes
of a point of the group are read back as the point. It rests on the arithmetic of
the base field of the curve. That the reader of a point gives only a point of the
group, from exactly the bytes that the writer writes for it, takes no hypothesis.

A suite absorbs a value as the bytes that the layout writes for it, so two values of
one type are absorbed as different bytes.

### The limit on the work of reading

The width of a value on the wire and the work of reading it are different
quantities. A value of no bytes is a value, and a collection of them is its length
and nothing else, so a length of a few bytes can ask for any number of elements.
The reader of a format is the mathematical one: a counted collection reads as many
elements as its count, of whatever width, and ends by the count.

An executor reads under a limit on the number of elements of collections that one
reading of a value builds. The reader under a limit agrees with the reader whenever
it answers, with a value or with a refusal. When the limit is reached the run ends
with the limit: an end that is neither a return nor a stop of the program, since
the proof was not checked to the end. It is never reported as a reader that had no
value.

The limit holds wherever a row reads: in a function, and in the program of a role, so
a verifier ends with the limit on a proof whose length asks for more elements than
the limit, of whatever width. A program that waits for a message that is never sent,
a value of a type with no value included, is waiting, and is not at the limit.

### What the two rewrites preserve

Both stages thread a state, and their theorem is one statement about a side's process.
A side that holds exactly one of the two transcript roles, with or without other roles,
is the prover's or the verifier's side; the statement is about these sides.

- **A definition.** The image of a definition that takes and returns the state is the
  definition's process for the side interpreted by the stage's *handler*: the handler
  performs every effect of the process as it is, except at the sites of the operations
  that the stage rewrote, where it performs the row's template for the side on the
  state it carries. The prover's side meets a rewritten exchange as a `send`, the
  verifier's side as a `receive`; the owner's side meets a rewritten draw as a `draw`,
  the receiver's side as a `receive`. An image that keeps its header has the
  definition's process, for every side.
- **The entry.** The process of the rewritten entry is: make the state as the entry row
  says, run the old entry under the handler from that state, consume the final state as
  the entry row says. The state is made and consumed without an effect.
- **A program.** Both hold for every definition of every program that the stage accepts
  and for every application path, with the handler determined by the program: the stage
  records the sites it rewrote, a callee's sites are read below the site of its
  application, and a callee that is not rewritten for the roles it is reached with is
  left as it is. The statement holds through every reply of every effect.
- **Two stages.** A handler of one stage followed by a handler of the next is one handler
  over the pair of their states, so the entry after Fiat–Shamir and serialization is the
  original entry under one handler, between the two starts and the two finishes.

A side that holds both transcript roles has no handler: an exchange between two roles
of one side performs no effect, so a handler of the side's effects has nothing to absorb,
while the rewritten program absorbs the value in both states. For that side the
Fiat–Shamir stage has a refinement instead: when the two roles start from equal copies of
the statement and the suite's operations return, the rewritten entry returns, on every
choice of its remaining coins, outputs that the original entry returns on some choice of
its coins; both roles derive the same coin from equal transcripts. The serialize stage
is then read through the two single-role sides: the prover's side writes its messages in
the order in which the verifier's side takes them, so on the prover's proof the
verifier's side returns its part of what the grouped entry returns
([completeness of a derived scheme](meaning.md#runs)).

A stage accepts a program when the conditions of its rows hold (the shapes of draws and
exchanges for the declared roles) and its parameters have the rows it asks for. It never
refuses a well-formed program for any other reason, and its result is well-formed.

## After the last stage

The constructed program contains, for the transcript roles, no `draw`. Application
expansion and projection to role programs preserve the meaning of every side: the
program of a role is the meaning of its protocol for the side of that role alone.
How a role program is lowered to native code is not part of this specification.

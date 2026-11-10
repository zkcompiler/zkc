# Core language: stages

A stage rewrites one core program into the next. The three stages between the
original program and the constructed one are the only compilation steps that
change what a security statement has to assume. Each is defined by a table.

## Stage tables

A stage table consists of the stage's name, the type of the state it threads, its
parameters and its rows. A row has a pattern and a template.

| Part | Content |
|---|---|
| Pattern | an operation form, with conditions on its attributes: owner, receivers, types, the row of a catalogue or oracle table |
| Template | a region. Its inputs are the matched operation's operands followed by the state values of the roles the row names; its outputs are the operation's results followed by the new state values |
| State | a type and its initial value per role, or none |
| Parameters | values the compiler chooses and exports, on which the template may depend |

The rewrite of a definition replaces every operation that matches a row by the
row's template, instantiated at the operation's attributes, and leaves every other
operation unchanged. When the stage has a state, each protocol takes and returns
one state value per role that the stage names, and an application passes them
through.

A template mentions only the matched operation. A stage therefore commutes with
sequencing, loops, branches and applications, and rewrites one definition at a
time. The same table is read by the compiler, which performs the rewrite, and by
the formal library, which recomputes it and compares the result with the exported
program, and which proves once, for the table, what the rewrite preserves and what
it costs.

A choice that does not affect meaning, such as the layout of a batch, is a
parameter. The compiler records the parameters it chose in the
[package](package.md); the stage's theorem holds for every parameter value.

## Unfold computed oracles

| Pattern | Template |
|---|---|
| `oracle_read(o, site)` on a handle whose origin is `computed(d, …)` | for each position in order: `o` evaluates `d`'s extent test on the captures and stops `refused` if it fails; evaluates `d`'s position function; reads the parents at those positions; evaluates `d`'s answer function on the captures and the answers |
| `oracle_compute(o, d)` | the handle becomes the tuple of its parents and captures, in order |

No state, no parameters. The ideal meaning of every side is unchanged, including
which execution stops, where and why. After the stage every handle is `sent`.
Functions of a computed oracle stay shared definitions; a read calls them.

## Commit oracles

Parameters: for each `sent` oracle row, a commitment scheme of the catalogue; for
each `oracle_read`, a layout of its openings.

| Pattern | Template |
|---|---|
| `oracle_send(s, R, site)` | `s` commits to the table and keeps the opening state; `s` exchanges the commitment with each role of `R` |
| `oracle_read(o, site)` | for each handle: the holder of the table opens the positions; it exchanges the rows and the openings with `o`; `o` checks each opening against the commitment and stops `reject` on failure |

The handle type becomes the commitment type for a receiver and the table with its
opening state for the sender. No threaded state.

The layout of a read says how its openings are grouped into messages: one opening
per position, or one opening for several positions of one or of several handles
with shared parts sent once. A read is one operation whose positions do not depend
on its answers, so every layout stays inside that operation and moves nothing
across a guard, a draw or a later read. A layout is admissible when it covers
every position of the read once and lets the reader restore the rows in their
order; the stage checks this. Layouts differ in their messages. For every
admissible layout the reader obtains the same rows, stops at the same point for
the same reason, and is charged for the same accesses; the stage's theorem is
stated for all of them.

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
  the package's identity. Two proofs that share an oracle have different
  separators.
- The statement is absorbed next, by an operation of the constructed program.
- A label is the site: the definition and its local site number. The path of
  applications and the iteration number are not absorbed. Two executions of one
  site differ in the transcript absorbed before them.
- Every value the suite absorbs is an explicit operation with an explicit
  encoding.
- A decoder that rejects and retries is a sampling law with a stated factor; its
  extra hash calls belong to the site.
- An authored construction is not rewritten. Its marked challenges are its sites.

## After the last stage

The constructed program contains no oracle operation and, for the transcript
roles, no `draw`. Application expansion, projection to participants and lowering
to the execution profiles preserve the meaning of every side.

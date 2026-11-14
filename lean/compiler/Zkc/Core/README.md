# Core

The core language of zkc and its tool. `Zkc.Core` holds the library: types, value
references by position with a random-access mirror, regions that bind results in
order, processes, `elaborate` as an ordinary function with its round trip, the tool's
steps (Fiat–Shamir and serialize threading with their whole-program theorem, expansion,
specialization, projection),
per-definition links checked by the kernel, a concrete executor, the meanings and
their structural theorems, the check of facts with the theorems that a function, a
protocol for any side and the program of a role that pass it never stop `undefined`,
the closure of an entry of a package with the proof identity of a scheme over it,
and the `zkc.core/0` JSON text of a package, read and printed. `Zkc.Core.Vocabulary`
states the vocabulary of the source language as data: its types with their sorts and
members, its modules, the default representative of each sort, and its operation rows,
each with the static arguments it takes, its kind with its domain row and its type at
given static arguments. `Zkc.Core.VocabularyModel` states
what each row computes on data, driven by the vocabulary's entry for its type (a prime
field by its order, the quartic extension of KoalaBear by its reduction, the group G1
of BLS12-381 by the curve arithmetic of the executor; `Zkc.Core.VocabularyElements`),
and runs a function of an admitted package on data; a row whose type has no arithmetic
here (G2, Gt, the pairing, the hashes other than SHA-256, `field.root` of a field whose
generator the catalogue does not give) does not run, with a message that names it.

Admission (`Zkc.Core.Admission`) is the one entry that says a raw package is a program.
`admit` elaborates the package, checks the facts of every body on its normal form
(`Zkc.Core.Normal`, `NormalLocal`, `NormalProtocol`: nested regions flattened, opened and
shared, each proved to keep the meaning of the body), checks the maxima of loops, checks
copies (`Zkc.Core.Copies`), and checks what the producer states beside the package
(`Admission.Claims`): the keys of its sites, which functions can stop, and the vocabulary
that its rows and the data of its literals are of. An `Admitted` holds the package, what was
stated and the proofs that the checks passed. Its theorems are the statements about a
program that passed: a function, a protocol for any side and the program of a role never
stop `undefined` (`Admitted.never_undefined`, `protocols_never_undefined`,
`role_never_undefined`), in every model that satisfies the domain laws and so in the model
of the vocabulary (`vocabulary_laws`); and a protocol of a package admitted as written, for
a side that supports the requirements that the check of copies found and on arguments that
hold the agreements of its header, never stops `incomplete`, whatever the replies of its
effects, and returns values that hold the agreements of its outputs
(`Admitted.protocols_cohere`; `protocols_cohere_together` for the side of every role).
The check of copies gives every copy of a value a class and the roles that must hold the
same value; `Zkc.Core.CopiesClasses` proves that what it returns is well formed without a
run, and `Zkc.Core.CopiesSound` proves the statement for every instruction of a protocol
body. `Zkc.Tests.Core.CopiesPremises` has a program that the check refuses and that stops
`incomplete`, and a run for each premise that fails without it.

A scheme is constructed on an admitted package (`Zkc.Core.Construction`):
`constructAdmitted` applies the Fiat–Shamir step and the serialize step and admits what each
returns, with the sites in the order of the body and without the check of copies, which is
a check of the program as written: a step threads the transcript states of the two roles
without declaring them copies of one value, and after serialization the prover and the
verifier do not interact. So the statement about `incomplete` is not made of a constructed
program. A construction starts from a package admitted as written and records it, and it
records that what was stated beside the source, other than the keys of its sites, is what
each step's result was admitted under (`Construction.claims`), so the vocabulary of the rows
of a constructed package is read from the construction (`Construction.rows_stated`).

`compile` is the one way from a raw package to role programs: admission of the package as a
program as written, the construction when a scheme is declared, and projection.
`compile_checked` says that a package that compiles was admitted and that its role programs
are those of the admitted package or of a construction on it; `Zkc.Tests.Core.Compile` has a
package for each gate that elaborates, that the gate refuses, and from which nothing is
compiled. The tool's two checked commands are these functions: `core-tool admit` is `admit`
and `core-tool compile` is `compile`, with `--vocabulary` to state that the rows and the
literal data are the vocabulary's. The commands under `core-tool step` apply one definition
to a package that elaborates; they admit nothing, and print the fixtures that the kernel
compares with its own evaluation.

The canonical layout is one format per type. A format (`Zkc.Core.Format`) states the
values it writes, a writer, a reader of a prefix and its width when it is fixed, with
two laws: the reader on what the writer wrote for a value of the domain, followed by
any bytes, gives the value and those bytes; and the reader gives a value only on bytes
that the writer writes for it, a value of the domain, followed by the bytes it leaves.
The laws are proved once per combinator (a pair, a tuple, a repetition of a fixed
count, a repetition after its count, a refinement, a view) and for the formats of
numbers (`Zkc.Core.FormatNumbers`): a number below a bound in the fewest bytes that
hold every such number, and a natural of variable length in its shortest form, every
other form refused. `Zkc.Core.CanonicalLayout` builds the format of a closed type of
the vocabulary (`formatOf`): `index<n>` in the least `k` bytes with `n ≤ 256^k`, `bool`
as `index<2>`, `nat` as the variable-length natural, a collection without a size after
its length, a tuple and a sized collection part by part, a type with one value in no
bytes, `nonzero<F>` as `F` without zero, an element of a prime field in the field's
width, an element of an extension by its coefficients, and a point of G1 in the 48
bytes of the compressed form. A type is written exactly when it has a format, the
rows of the layout and the absorbing row of the suite are the writer and the reader
of that format, and admission of such a row is the existence of the format. In the
model of a package the row that puts a value appends the bytes of its format, and the
row that takes one, on those bytes followed by anything, gives the flag `true`, the
value and what follows (`model_put`, `model_take`, with `model_open`, `model_close`,
`model_read` and `model_exhausted` for the rows of the entry); a typed value is read
back from its datum (`Concrete.ofDatum_toDatum`). The laws
of a type (`formatOf_lawful`) take a hypothesis only for a type with a point of G1 in
it: `PointCompression`, that the bytes of a point of the group are read back as the
point, which needs the arithmetic of the base field of the curve. The published
vectors of the encoding are its executable check. Records and variants have no
format: the vocabulary has no closed type for them, and no row writes one.

A reader of a format reads as many elements as the bytes ask for. A run reads under a
limit on the number of elements of collections that one reading of a value builds
(`defaultLimit`, `2^20`, unless the caller gives one): the reader under a limit agrees
with the reader whenever it answers (`formatOf_agrees`), and a run that reaches the
limit ends with the limit, which is neither a return nor a stop
(`Zkc.Core.DecodingLimit`). This holds for a function (`Vocabulary.run`, `Run.limit`)
and where a verifier reads a proof: the executor runs the programs of roles with their
pure rows under the limit (`Zkc.Core.DecodingLimitRoles`, `Execute.limitedRoleEntry`;
`Vocabulary.runRoles` and `Vocabulary.runEntry` of `Zkc.Core.VocabularyExecute`), and a
role that reaches the limit ends with `Execute.Outcome.limit`. What a run runs is the
meaning under the model, cut where a reading reaches the limit: for functions
(`limitedFunctions_within`) and for the programs of roles (`limitedRoles_within`),
which perform the effects of the meaning with their replies.

The mark of the limit in a process is a wait for a value of a type with no value, at a
site that the executor reserves: a definition number above the identity of every
definition of the program it runs (`reservedDefinition`,
`identity_lt_reservedDefinition`), which it gives to the rows and by which it
recognises the mark (`limitOf?`). A program that itself waits for a value of a type
with no value waits at a site of its own and is reported as waiting for a message that
is never sent. That no effect of a program is at the reserved site is read off
`RolePrograms.table`, in which every effect of a role program is at a site of the
identity of one of its definitions; it is checked on a program whose receiver waits
for `index<0>`, and it is not a theorem.

An input of a run is a value of its type (`validInput`, by structural recursion): a
number below the bound of an index, an element below the order of its field, a point
of G1 that is of the group and not only on the curve.

The endpoint statements (`program_together`, `program_endpoints_return`) are about
relations on processes, for an arbitrary model and an arbitrary sampler: `ReturnsAlone`
for one process and `ReturnTogether` for two, in which either process may take the next
step. A draw is a broadcast in order: the board keeps every coin of a site in the order
announced, each of the two processes counts the coins it has heard at each site, and a
hearing takes the coin at the hearer's count. The endpoint lemma holds for two sides that
each hold at most one role of the protocol, over functions that perform no effect
(`QuietTable`); that each part has heard every coin of the sites at which it hears is an
invariant that the proof derives from the fact that a site is one operation
(`Protocols.entry_listened`). A sampler gives a coin at every type that has a value, and
every model has one (`Sampler.constant`).

The executor (`Zkc.Core.Execute`) is total: one process is run by recursion on the
process (`runAlone`), and any number of processes against each other one effect at a
time (`run`, `runAll`), which ends because every effect continues one process
(`oneContinues_wellFounded`); no fuel is given. Its coins are a parameter
(`Execute.Coins`, the `k`-th coin of a site at a type): `Vocabulary.seededCoins` is the
source of a seed, in which a coin is the value of the law of its type made of numbers of the
seed, the site and `k`; a caller with its own mapping of coins gives its own, read through
`Vocabulary.validCoins` so that a coin is validated at its type where it enters a run; and a
source gives a sampler (`Coins.sampler`). What a value of a law is has one definition,
`Vocabulary.lawValue`: from a closed type and a stream of numbers to a value, or why the type
has no law. It keeps every public coin announced at the draw's site and gives a
receive at a site without a message in transit the first coin of that site that its
process has not heard, so every receiver of a draw hears every coin; a process that drew
goes to the end of the order of the run, so that the others hear its coin before it
draws again. The inputs of a run are validated values (`Vocabulary.Checked`, made only
by validation): an input is validated once and run as often as a caller likes
(`Vocabulary.run`, `runRole`, `runRoles`; `runData`, `runEntryRole` and `runEntry`
validate and run).

What is proved of its runs (`Zkc.Core.ExecuteRuns`, `Zkc.Core.VocabularyExecute`), for
the sampler of the source of coins: a run of one process that returns is a return alone
(`runAlone_returned`, `ReturnsAlone`), and one that stops is a stop alone
(`runAlone_stopped`, `Execute.StopsAlone`); a run of two processes in which both return
is a return together, without a condition on the run (`run_together`, `ReturnTogether`:
the executor reads coins from the relation's board); a process
cut at the limit returns or stops only as the whole one does (`ReturnsAlone.of_within`,
`Execute.StopsAlone.of_within`, `ReturnTogether.of_within`). From a run to the meaning,
with the model of the vocabulary: `runRole` on a role that returned or stopped gives
that the role's program of the meaning, without a limit, returns or stops alone
(`runRole_returned`, `runRole_stopped`), and `runRoles` on two roles that returned gives
that their two programs return together (`runRoles_together`). The
kernel computes a run of the verifier of a serialized program in the checks, so the
statement has a closed instance.

What is not proved: nothing is stated of three or more processes, of a role that fails or waits, or of the converse, that the relation's
returns are found under the executor's schedule; and the grouped meaning is related to
the role programs by the endpoint lemma, not by a statement about the executor.

What each role of a run did is read beside the executor (`Zkc.Core.Observed`): an event is
what a role sent, received or heard, drew or sampled, with its site and its value, read from
the mail, the board and the coins as the executor's step reads them. A role has an event
exactly when it moves (`event?_isSome`), and a run to its end with its events ends as the
executor's run does (`finishObserved_fst`, `observeAlone_fst`); no definition of the executor
changes.

The threading steps (Fiat–Shamir, serialize) have a theorem over whole programs, for a
side that holds exactly one of the two transcript roles (the prover and the verifier as
separate sides; `OneTranscriptRole`). From `stepProtocols … = .ok …`: the image of the
declared entry is the entry interpreted by the handler of the step (`threadHandler` on
`stepMarks`, the record of the operations that the step rewrote, by site), between what
the rule's entry does before and after the body (`stepProtocols_entry`, with
`fiatShamirEntry_sound` and `serializeEntry_sound`); an entry that the step copies has its
meaning (`stepProtocols_plain_entry`); every image of an applied protocol that threads is
the protocol under every handler that follows its marks, and every copy has its
protocol's meaning (`rewriteProtocols_threads`). That the handler fits the body of every
definition (`Fits`) and the statement about callees (`CalleesThread`) are derived
(`region_fits`, from the fact that the sites of a well-formed definition are pairwise
different), not assumed. For a side that holds both transcript roles there is no handler:
an exchange between two roles of one side performs no effect, so no handler of effects
can absorb its value. What holds there is a refinement, for a rule whose two roles keep
coupled states (`RuleCouples`; for Fiat–Shamir, equal transcripts, over a suite whose rows
and functions return, `Suite.Returns`): the image of the entry returns on every run on
which the entry does, for inputs in which the prover's and the verifier's copies of the
statement are equal (`fiatShamir_together`, with `EveryRun`, which is `GroupedComplete`
taken apart along sequencing). Nothing is stated for a side that holds neither.
A `repeat` that collects and whose region is rewritten is threaded like any other loop
(`repeat_threads`). A step refuses no program of well-formed definitions internally: it
returns whenever the construction item accepts and the declaration has the rows
(`stepProtocols_returns`, `construct_returns`); when the construction item accepts and
when the rows are present are not characterised by a theorem.

Completeness of the scheme that `construct` derives is a theorem (`construct_complete`;
`serializeProtocols_complete` for the serialize step alone on an authored construction):
for every sampler the constructed prover's program returns a proof on which the
constructed verifier's program returns outputs that the interactive condition holds of.
Its premises, besides the equations that say which programs were constructed: the
interactive entry is complete for every sampler, for the side of the prover and the
verifier together (`GroupedComplete`); the prover's and the verifier's copies of the
statement are equal in the inputs (`StatementCopiesEqual`); the suite's rows and
functions return (`Suite.Returns`, automatic for a suite of rows); the layout reads back
what it writes (`Layout.Lawful`: one law per row, in the prefix form); and every value
the interactive prover sends is one the layout writes (`EverySend`). Nothing is assumed
about a handler or about two programs run against each other: the proof goes through the
grouped process (the Fiat–Shamir refinement above, then `serialize_entry_replays`: the
prover's side writes the messages in the order in which the verifier's side takes them),
not through `ReturnTogether`. In the model of the vocabulary the laws of the canonical
layout are derived (`Vocabulary.construct_complete`, `canonicalLaws`), with the named
hypothesis `PointCompression` only when a message type contains a point of G1. What a
protocol still has to show there: its interactive completeness, in the strong form for
every sampler of the model's carrier, and that its messages are written, which for a
multiple of a point needs that the group is closed under multiples
(`GroupClosedUnderMultiples`, a named hypothesis; the arithmetic rows of a prime field
give written values). The statement says nothing for an entry that exchanges with a
third role or reads an oracle: its grouped process does not return alone. The model of the vocabulary's rows satisfies the domain laws of the
table of a package that the core elaborates and whose rows are the vocabulary's
(`Vocabulary.model_domainLaws`), so the never-`undefined` theorems apply to the model that
is run; `Vocabulary.missing` compares a package's rows with the vocabulary by name, static
arguments, kind with its domain row, inputs and outputs. Admission checks the rows of a package
that states the vocabulary beside it one by one: a row under a name of the vocabulary must be
the vocabulary's row at its static arguments (`Vocabulary.misstated`), and a row under another
name is a row of an extension (`Vocabulary.extensions`), which admission does not refuse and
the model of the vocabulary does not run. A package without a row of an extension has the
vocabulary's rows (`Admitted.rows_matched`).

`Zkc.Core.VocabularyArithmetic` states, for the rows of the arithmetic of a field, of a group
and of a sized collection of elements, the value that the model of a package gives at typed
values, as the operation of the element type on their data, at any package whose row has the
name and the static arguments of the vocabulary's row. A statement about a model of the
mathematics is related to the model that runs through these (`lean/formal`).

The core is a library of the package `zkc_compiler` (`lean/compiler`), which has no Lake
dependency; the frontend (`Zkc.Frontend`, in the same package) emits its packages and reads its
vocabulary, and the formal package (`lean/formal`) states and proves properties over its
meaning. A module of the core imports only modules of the core and of Lean's prelude and
standard library (`Init`, `Std`); `lake exe zkc-audit` checks this, the axioms, `@[extern]` and
`@[implemented_by]` of its declarations, and that the kernel accepts them when they are
replayed.

Run `lake build` from `lean/compiler`. It builds the library, the tool and the checks;
the kernel comparisons, the printed links and their statements are checked by the
build.

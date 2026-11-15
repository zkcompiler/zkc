# Core

The core of the zkc compiler: one type of typed terms over three dialects (a function, a
protocol of all its roles, the program of one role), their meanings as processes, the
projection of a protocol to the programs of its roles with the theorem that every role program
is a projection of its protocol, what elaboration decides about a body, the data of an admitted
program and of a deployed scheme, the run of a role under the handlers of its deployment, and
the types of the functions that are still to be built with the statements that they must
satisfy. It is the library `ZkcCore` of the package `zkc_compiler` (`lean/compiler`), in the
namespace `Zkc.Core`; it imports only `Init` and `Std`. Each file is a Lean module whose
definitions are exposed (`@[expose] public section`), so that a proof in another module unfolds
them. The root module, `Zkc/Core.lean`, imports every module of the core.

## Layers

The directories are layers: a module imports modules of its own directory and of the
directories above it in this table, never of a directory below. No module that defines
something imports a module that only proves something.

| Directory | Holds |
|---|---|
| `Process/` | processes (well-founded trees of effects), the one property on every path (`Process.Every`) and its rules, handlers, their composition, and the retry of an attempt |
| `Program/` | keys, labels, occurrences, sites, places and stops (`Identity`); types, the vocabulary and its models (`Vocabulary`); terms, their addresses and their linear use (`Term`); located types and role maps (`Located`); the record of a run (`Record`); the kinds of events and the shape of a protocol (`Shape`); the three dialects (`Dialects`); projection, the translation of a protocol's term to a role's (`Project`); a typed program, its definitions with what elaboration decided about each body, and the lookup of a definition by its key (`Typed`); the program by names that a frontend gives (`Syntax`) |
| `Meaning/` | events and what a role holds (`Events`); the fold of a term over the semantics of a dialect (`Fold`); the semantics of a function, of a protocol and of a role program (`Local`, `Protocol`, `Role`); the meanings of a whole program (`Program`); the rule of a call (`Call`) |
| `Projection/` | the relation of a role's process to a protocol's and its lemmas (`Proj`), the proof for one term (`Sound`), and the theorem for every definition of a program (`Theorem`) |
| `Facts/` | the property at every instruction that a run reaches, facts and their reading, and the annotation of an admitted program |
| `Admission/` | refusals, the association of a program and its resolution in it, and an admitted program |
| `World/` | the description of a layer (a handler of a role) and its meaning as a handler, the network of the roles, and the runs of a protocol and of one role alone |
| `Scheme/` | the declaration of a scheme, who proves and who verifies, a deployed scheme and the run of a role under its handlers, and what deployment decides about scopes and keys |
| `Run/` | how a run of the executor ends, the executor, and the prover's and the verifier's runs |
| `Format/` | formats of values and the codecs of a model |

`Functions.lean` and `Statements.lean` are above every directory.

## What is proved, what is defined, what is still to be built

Proved, with no axiom beyond `propext` and `Quot.sound`:

- the projection theorem (`Zkc.Core.projection`, `Projection/Theorem.lean`): the program of
  every role of every protocol of a typed program, run on what the role holds of one input, is
  a projection of the protocol's process; where the protocol returns, the role returns what it
  holds of the results;
- the rules of proof on every path (`Process.every_bind`, `every_mono`, `every_iterate`), and the
  rule of a call (`Contract.call`, `Law.call`, `Law.contract`): a contract of a function, a
  property of its entry in a table, installed at an actual call with the operands and the
  continuation taken from the term;
- that the process with the record of a run is, without the record, the process of the term
  (`Term.observe_fst`), and the lemmas on `Proj`, on what a role holds and on literals.

Defined: everything else, from the terms and their meanings to deployment, the network and
the runs.

Still to be built:

- the functions of the record `Functions` (`Functions.lean`), with their types: `elaborate`,
  `print`, `printRole`, `format`, `admit`, `check`, `deploy`, `identity`, `execute`,
  `schedule`;
- the theorems that `Statements.lean` states and does not prove, each with what it preserves
  (execution and state, a view, validity or progress): from `roundTrip` and
  `admitsWhatWasGiven` to `complete`, `executorRuns` and `formats`.

`Process/`, `Program/`, `Meaning/` and `Projection/`, and the data of `Admission/`, are what
the projection theorem and the meanings stand on. `Facts/`, `World/`, `Scheme/`, `Run/` and
`Format/` are defined and type-checked, and no implementation has exercised them yet: the
code that first builds one of these parts changes its definitions here first.

## Tests

The tests of the core are the library `ZkcCoreTests` (`Zkc/Tests/Core/`), whose checks the
kernel runs when they are built:

- `Shapes.lean`: protocols of different shapes written as typed programs, with what
  elaboration decides about each, and meanings that compute;
- `Controls.lean`: controls at the edges of the definitions (the world, the scheduler, handlers
  and the retry of an attempt, distinct keys, codecs, linear use, who proves, forks, the start
  of a layer, laws and contracts of functions at their calls, the lookup of a definition), and
  the theorems that are the reasons for the definitions' shape;
- `Consumers.lean`: each consumer's side, written against the core.

In `lean/compiler`, `lake build` builds the core and its tests, `lake test` builds the tests
(the library is the test driver), and `lake exe zkc-audit` audits the core and its tests: the
axioms of every declaration, the replay of every declaration through the kernel, and the rules
on imports.

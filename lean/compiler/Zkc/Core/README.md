# Core

The core of the zkc compiler: one type of typed terms over three dialects (a function, a
protocol of all its roles, the program of one role), their meanings as processes, the
projection of a protocol to the programs of its roles with the theorem that every role program
is a projection of its protocol, the elaboration of a program of functions by names with its
printed form and the round trip, what elaboration decides about a body, the data of an admitted
program and of a deployed scheme, the run of a role under the handlers of its deployment, and
the types of the functions that are still to be built with the statements that they must
satisfy. It is the library `ZkcCore` of the package `zkc_compiler` (`lean/compiler`), in the
namespace `Zkc.Core`; it imports only `Init` and `Std`. Each file is a Lean module whose
definitions are exposed (`@[expose] public section`), so that a proof in another module unfolds
them. The root module, `Zkc/Core.lean`, imports every module of the core. The standard
vocabulary, its keys and its table, is the library `ZkcVocabulary` beside the core
([guide](../Vocabulary/README.md)); it imports the core, and the core does not import it.

## Layers

The directories are layers: a module imports modules of its own directory and of the
directories above it in this table, never of a directory below. No module that defines
something imports a module that only proves something.

| Directory | Holds |
|---|---|
| `Process/` | processes (well-founded trees of effects), the one property on every path (`Process.Every`) and its rules (iteration among them, with an invariant asked of every step or only of the steps below a count), handlers, their composition, and the retry of an attempt |
| `Program/` | keys, labels, occurrences, sites, places and stops (`Identity`); types, the vocabulary, whose keys say everything that tells a nominal type, a row or a law from another, with the law that the domain row of a restricted row decides it, which types have no value, and its models (`Vocabulary`); terms, their addresses and whether their case analyses without an arm give nothing (`Term`); items placed by the low bits of a natural, the keyed collection of the decision of distinct addresses and of what the check of facts knows (`BitTree`); the decision of distinct addresses, with what failed, proved to decide that proposition (`Conditions`); linear use, defined by its decision, which says which value is not used as it must be and where (`Linear`); located types and role maps (`Located`); the record of a run (`Record`); the kinds of events and the shape of a protocol (`Shape`); the three dialects (`Dialects`); projection, the translation of a protocol's term to a role's (`Project`); a typed program, its definitions with what elaboration decided about each body, one definition elaborated against the headers before it and a program extended by it, and the lookup of a definition by its key (`Typed`); the program by names that a frontend gives (`Syntax`); refusals: the rules of the core, what a rule found and the place where it found it, as data (`Refusal`); the elaboration of a region over the rules of a dialect, each refusal made at its place (`Elaborate`); the printed form of a term and its round trip over lawful rules (`Print`); the written form of each operation of a function and its resolution, with their laws, and the rules of the local dialect (`LocalRules`); the elaboration of a function, its printed form and their round trip (`ElaborateLocal`); the printed form of a typed program (`PrintProgram`); what an operation with a domain asks of an application, as data, and the values that it names (`Requirement`) |
| `Meaning/` | events and what a role holds (`Events`); the fold of a term over the semantics of a dialect (`Fold`); the semantics of a function, of a protocol and of a role program (`Local`, `Protocol`, `Role`), with the meaning of every operation that the core owns (`Local`); what it is for the functions of a table to keep validity and never stop `undefined`, that every local operation keeps validity, and that a type with a valid value has a value (`Validity`); the meanings of a whole program (`Program`); that a function whose header says that it cannot stop stops only `undefined` (`Stops`); the rule of a call (`Call`) |
| `Projection/` | the relation of a role's process to a protocol's and its lemmas (`Proj`), the proof for one term (`Sound`), and the theorem for every definition of a program (`Theorem`) |
| `Facts/` | the property at every instruction that a run reaches, the annotation of an admitted program, which is the bounds of its loops, and what it is for a program to respect it, in its functions and in its role programs (`Facts`); what the check of facts is told about operations: what a written operation requires, the ranges of its results and how its result reads, which operations of a dialect compute, and which of its types have no value (`OpFacts`); the state of the check, a table of applications by written form and operand identifiers, placed by a number computed from those identifiers and by each result's identifier, and what is known, each part placed by an identifier, with the rules that decide a requirement and learn from a truth value (`State`); the check of facts, one walk over a term of any dialect, in which a region is dead only where what is written says that it never runs (`Walk`); what the local dialect tells it (`Local`); what the state says of a run, a valuation of identifiers, and the laws of `OpFacts` as propositions (`Valuation`); that the rules of what is known are true (`Learning`); what the walk does to its state whatever the run (`Growth`); that the local operations satisfy the laws, and that what an operation requires is enough for it (`LocalLaws`); the soundness for a function (`Soundness`) |
| `Admission/` | the elaboration of one definition against the headers before it, of a program of functions, and its round trip (`Elaboration`); the association of a program and its resolution in it, with the arguments of an instance of a generic declaration that it records (`Static`), and an admitted program (`Admission`); the check of one definition against the headers before it (elaborated, then its facts checked), admission as that check for each definition in order, and the acceptance of a typed program by the check of facts as a proposition (`Check`); the soundness of the check of facts for the functions of a program (`Programs`); the statements of `Statements.lean` about functions, proved of `admit` and `check` (`Theorems`) |
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
- the rules of proof on every path (`Process.every_bind`, `every_mono`, `every_iterate`,
  `every_iterate_below`), and the
  rule of a call (`Contract.call`, `Law.call`, `Law.contract`): a contract of a function, a
  property of its entry in a table, installed at an actual call with the operands and the
  continuation taken from the term;
- that the process with the record of a run is, without the record, the process of the term
  (`Term.observe_fst`), and the lemmas on `Proj`, on what a role holds and on literals;
- the round trip: for rules whose laws hold, the printed form of a term whose case analyses
  without an arm give nothing, elaborated in its context with the levels as the names in scope,
  is the term (`elabBody_print`, `Program/Print.lean`), and elaboration gives only such terms
  (`elabBody_armed`, `Program/Elaborate.lean`); the local rules are lawful over headers with
  distinct keys, and the written form of a local operation names it (`localRules_lawful`,
  `LocalOp.print_injective`, `Program/LocalRules.lean`); the printed body of every typed
  function elaborates as the body with its conditions (`elabFn_printFn`,
  `Program/ElaborateLocal.lean`); the printed form of every typed program of functions
  elaborates as the program (`elaborateFunctions_print`, `Admission/Elaboration.lean`), so also
  that of every program that elaboration gives (`elaborateFunctions_roundTrip`);
- that every local operation keeps validity: on valid operands, the results that it gives are
  valid (`localOp_valid`, with `localOp_row_valid`, `localOp_owned_valid`,
  `localOp_literal_valid`, `localOp_call_valid` and `ownedOp_valid` for the operations that the
  core owns, `Meaning/Validity.lean`);
- the decision of distinct addresses: the first repeated address, or none exactly when the
  addresses are distinct (`Term.repeatedAddress_eq_none`, `Program/Conditions.lean`). Linear
  use is defined by its decision (`Term.UsedOnce` is `Term.misuse … = none`,
  `Program/Linear.lean`), so it has no separate statement to prove;
- the check of facts of a function (`FactCheck.checkFacts_sound`, `Facts/Soundness.lean`): for a
  body with distinct addresses that `checkFacts (localFactRules V fns)` accepts, against callees
  with distinct keys that never stop `undefined` on valid inputs and keep validity, on valid
  inputs the process never stops `undefined`, returns valid values, and every loop as often as
  a count runs at most the bound given for its place; for a typed program each of whose
  functions the check accepts (`Defs.Accepted`), every function is safe and keeps validity,
  and the functions' part of `Respects` holds (`Defs.FunctionsRespect`; `functions_sound`,
  `typed_functions_sound`, `Admission/Programs.lean`), which for a program without protocols
  is `Respects` (`Respects.of_functions`, `Facts/Facts.lean`). Beneath them: the laws of
  `localOpFacts` against the meaning (`localOpFacts_lawful`), that the requirements of every
  local operation are enough for it (`localOp_defined`) and name values that exist
  (`localRequires_runs`), `Facts/LocalLaws.lean`;
- the statements of `Statements.lean` about functions, of `admit`, `check` and
  `elaborateFunctions` (`Admission/Theorems.lean`): what `admit` returns is the elaboration of
  what was given, with the association resolved in it (`admitsWhatWasGiven`); `check`, one
  definition at a time from no headers, gives the headers of the admitted program
  (`checkAgrees`); a function of an admitted program never stops `undefined` on valid inputs
  and returns valid values (`functionsSafe`, `functionsKeepValidity`); an admitted program
  respects its annotation (`annotationHolds`); a function whose header says that it cannot
  stop does not stop (`headersSayWhoStops`), since such a function stops only `undefined`
  (`Defs.fnTable_stops_undefined`, `Meaning/Stops.lean`).

Defined: everything else, from the terms and their meanings to deployment, the network and
the runs.

Still to be built:

- the functions of the record `Functions` (`Functions.lean`), with their types. For a program
  of functions, `elaborate`, `admit` and `check` are built as the definitions
  `elaborateFunctions`, `admit` and `check` (`Admission/Elaboration.lean`,
  `Admission/Check.lean`); the record gets them when protocols are elaborated, which needs the
  rules of the protocol dialect and the walk of role programs by the check of facts (until
  then `admit` and `check` refuse a protocol). `printRole`, `format`, `deploy`, `identity`,
  `execute` and `schedule` are still to be built;
- the theorems that `Statements.lean` states and does not prove, each with what it preserves
  (execution and state, a view, validity or progress): those about functions are proved of
  the definitions above for a program of functions (`Admission/Theorems.lean`); `rolesSafe`,
  `realized`, `anyOrder`, `replayed`, `recordsAreValid`, `schedulerRuns`, those of deployment
  from `deployKeeps` to `identityReads`, `executorRuns` and `formats` are not, and neither is
  `roundTrip` for a program with protocols.

`Process/`, `Program/`, `Meaning/` and `Projection/`, and the data of `Admission/`, are what
the projection theorem and the meanings stand on; `Facts/` is built for functions. `World/`,
`Scheme/`, `Run/` and `Format/` are defined and type-checked, and no implementation has
exercised them yet: the code that first builds one of these parts changes its definitions here
first.

## Tests

The tests of the core are the library `ZkcCoreTests` (`Zkc/Tests/Core/`), whose checks the
kernel runs when they are built:

- `Shapes.lean`: protocols of different shapes written as typed programs, with what
  elaboration decides about each, and meanings that compute;
- `Controls.lean`: controls at the edges of the definitions (the world, the scheduler, handlers
  and the retry of an attempt, distinct keys, codecs, linear use, who proves, forks, the start
  of a layer, laws and contracts of functions at their calls, the lookup of a definition), and
  the theorems that are the reasons for the definitions' shape;
- `Consumers.lean`: each consumer's side, written against the core;
- `Operations.lean`: for each written name of an operation that the core owns, a function that
  elaborates and whose printed form elaborates back; written forms with other types refused;
  the operations that would copy or drop a part refused at a linear type, and so is giving a
  sequence of linear items a size; each meaning at a value, and each domain at a value outside
  it;
- `Elaboration.lean`: for each rule of elaboration and each condition of a body, a program by
  names that is accepted and one that is refused, compared with the whole refusal (rule, place
  and what the rule found); the latest binding of a name; the case analysis without an arm that
  the printed form cannot tell apart; and the printed form of each accepted program elaborated
  back to it;
- `Facts.lean`: the check of facts on functions written by names: the conformance cases of the
  reference that a function can express, by their identifiers, accepted or refused as the case
  says with the whole refusal; for each operation with a domain and for a restricted row, an
  application accepted and one refused; sharing and the scope of facts in sibling regions, in
  loops, after a choice and when a name is bound again; which code does not run: the body of a
  loop of the written count zero, an arm whose payload has no value, a function with an input
  that has none, and not the code after a guard that contradicts what is known (`N-TY9e`);
- `Admission.lean`: `admit` and `check` on programs of functions: a program of two functions
  admitted with its whole annotation; admission stopped at the first refused definition, with
  every refusal of it and nothing of a later one, for a refusal of the check of facts and for
  one of elaboration; `check`, one definition at a time, giving the headers of the admitted
  program; a protocol refused.

In `lean/compiler`, `lake build` builds the core and its tests, `lake test` builds the tests
(the library is the test driver), and `lake exe zkc-audit` audits the core and its tests: the
axioms of every declaration, the replay of every declaration through the kernel, and the rules
on imports.

# Core

The core of the zkc compiler: one type of typed terms over three dialects (a function, a
protocol of all its roles, the program of one role), their meanings as processes, the
projection of a protocol to the programs of its roles with the theorem that every role program
is a projection of its protocol, the elaboration of a program of functions by names with its
erased form and the round trip in both directions, what elaboration decides about a body,
places in a term and replacement, the value form of a term and the decision that a second term
follows the skeleton of a first (two such terms mean the same when neither stops `undefined`),
a transformation of a function as a step that checks both functions and this decision, the data
of an
admitted program and of a deployed scheme, the run of a role under the handlers of
its deployment, and the types of the functions that are still to be built with the statements
that they must satisfy. It is the library `ZkcCore` of the package `zkc_compiler` (`lean/compiler`), in the
namespace `Zkc.Core`; it imports only `Init` and `Std`. Each file is a Lean module whose
definitions are exposed (`@[expose] public section`), so that a proof in another module unfolds
them. The root module, `Zkc/Core.lean`, imports every module of the core. The standard
vocabulary, its keys and its table, is the library `ZkcVocabulary` beside the core
([guide](../Vocabulary/README.md)); it imports the core, and the core does not import it.

## Layers

The directories are layers: a module imports modules of its own directory and of the
directories above it in this table, never of a directory below. A module of proofs, one whose
definitions if any are used only in statements and proofs, is imported only by modules of proofs
and by the root.

| Directory | Holds |
|---|---|
| `Process/` | processes (well-founded trees of effects), the one property on every path (`Process.Every`) and its rules (iteration among them, with an invariant asked of every step or only of the steps below a count), handlers, their composition, and the retry of an attempt; the base relation, two processes that mean the same along every path of permitted replies, an equivalence and a congruence for what a process is built with, which a handler whose replies are permitted keeps, retry included, and a value that a process can return on some path of permitted replies with its rules (`Same`) |
| `Program/` | keys, labels, occurrences, sites, places, stops and names, a name being a number that a definition binds at one place (`Identity`); the position of an item in a list (`Member`, by which a call names a definition among the headers), lists of values of types (`HList`), types, the vocabulary, whose keys say everything that tells a nominal type, a row or a law from another, with the law that the domain row of a restricted row decides it, which types have no value, and its models (`Vocabulary`); contexts of names, a finite map from names to types behind a small interface, the names of a binding, variables (a name with the proof that the context has it at its type) and environments of names, with their lemmas, among them what an environment with one more name bound gives at that name and at another, the structural rule on contexts (a context within another) and environments that agree at some names (`Context`); lemmas about lists and `Except` that the proofs use (`Library`); terms, whose bindings carry the names that they bind, their addresses, whether their case analyses without an arm give nothing, and that every name of a definition is bound at one place (`Term.BoundOnce`) (`Term`); items placed by the low bits of a natural, the keyed collection of the decisions of distinct addresses and of single assignment and of what the check of facts knows (`BitTree`); the decisions of distinct addresses and of single assignment, with what failed and the place of a name bound a second time, each proved to decide its proposition (`Conditions`); linear use, defined by its decision, which says which value, by its name, is not used as it must be and where (`Linear`); located types and role maps (`Located`); the record of a run (`Record`); the kinds of events and the shape of a protocol (`Shape`); the three dialects (`Dialects`); projection, the translation of a protocol's term to a role's (`Project`); a typed program, its definitions with the names of their inputs and what elaboration decided about each body, one definition elaborated against the headers before it and a program extended by it, and the lookup of a definition by its key (`Typed`); the program by names that a frontend gives (`Syntax`); refusals: the rules of the core, what a rule found and the place where it found it, as data (`Refusal`); the elaboration of a region over the rules of a dialect, each refusal made at its place (`Elaborate`); erasure, the program by names of a typed term, and its round trip in both directions over lawful and canonical rules (`Erase`); the written form of each operation of a function and its resolution, with both halves of the law of written forms, and the rules of the local dialect (`LocalRules`); the elaboration of a function, its erased form and their round trip in both directions (`ElaborateLocal`); the erased form of a typed program (`EraseProgram`); what an operation with a domain asks of an application, as data, and the values that it names, and the ranges of naturals with what it is for a natural to be in one (`Requirement`); a term in a wider context, with the same erased form, a term with one place left open and the term that fills it, a term split after its first instructions, and the names that a term reads (`Place`) |
| `Meaning/` | events and what a role holds (`Events`); the fold of a term over the semantics of a dialect, which binds the names of each binding to its values (`Fold`); the semantics of a function, of a protocol and of a role program (`Local`, `Protocol`, `Role`), with the meaning of every operation that the core owns (`Local`); what it is for the functions of a table to keep validity and never stop `undefined`, that every local operation keeps validity, and that a type with a valid value has a value (`Validity`); the meanings of a whole program (`Program`); that a function whose header says that it cannot stop stops only `undefined` (`Stops`); the rule of a call (`Call`); places with their meaning: a term in a wider context means the same, what it is for a run to reach a place and a fact at a place, replacement, and that a term's meaning depends only on the names that it reads (`Place`) |
| `Projection/` | the relation of a role's process to a protocol's and its lemmas (`Proj`), the proof for one term (`Sound`), and the theorem for every definition of a program (`Theorem`) |
| `Value/` | the value form of a term and the decision that a second term follows the skeleton of a first, for any dialect. Following does not decide that the second term is safe: a value has no place in the skeleton, so a value with a domain may be read before the guard that justifies it; two terms of which one follows the other mean the same when neither stops `undefined`, which for a function is its check of facts. The table of applications by written form and operand identifiers, placed by a number computed from the written operation's number and those identifiers and by each result's identifier, the state that carries it (the next identifier, and the refusals and the bounds of loops that the check of facts finds), and the identifiers of the names in scope (`Table`); valuations of identifiers, what the table says of a valuation, a well-formed table, a state and a valuation that agree, and the growth of the state as identifiers are made and applications shared, which keeps every name in scope with an identifier below the next (`Valuation`); the skeleton of a term, what it keeps in order (effects, guards, every form of control) on identifiers of the table, with the table of its values, what a dialect says of its operations, and what a dialect must decide for following a skeleton (`Skeleton`); following a skeleton, the decision (`followsSkeleton`) (`Follows`); what building and following a skeleton do to the state (`Growth`); the reading of an identifier from the leaves through the table, the processes that run a skeleton, and that two of them mean the same (`Runs`); that a term runs its own skeleton and a term that follows a skeleton runs it, so that two terms of which one follows the other's skeleton mean the same when neither stops `undefined` (`Soundness`). An application of an operation that a dialect says commutes is placed in the table with its two operands in one order, the smaller identifier first, whichever way they were written (`ValueRules.order`, `Skeleton`) |
| `Facts/` | the count of every loop that a run reaches (`Term.EveryLoop`), the annotation of an admitted program, which is the bounds of its loops, and what it is for a program to respect it, in its functions and in its role programs (`Facts`); what the check of facts is told about operations: what a written operation requires, the ranges of its results and how its result reads, which operations of a dialect compute, which of its types have no value, and a number for each written operation by which the table places its applications (`OpFacts`); what the check knows beside the table of `Value/`, each part placed by an identifier, and how an identifier reads by the operation that gave it, with the rules that decide a requirement, which read a sum with its operands in either order, and learn from a truth value, the range below `r` of a sum of `x` and `t`, in either order, where a loop made the order `t < r - x` for its index, the check of the requirements of an application, and the lemmas of the ranges that it defines (`State`); the check of facts, one walk over a term of any dialect, which keeps the identifier of each name in scope, in which a region is dead only where what is written says that it never runs, with the range of a carried natural after a loop and its lemmas (`Walk`); what the local dialect tells it, with the arithmetic of ranges (a power's ends computed only when they are small enough) and its lemmas (`Local`); what what is known and the requirements say of a valuation of identifiers, one step of the walk, and the laws of `OpFacts` as propositions (`Valuation`); that the rules of what is known are true (`Learning`); what the walk does to its state whatever the run (`Growth`); the local dialect's reading of values and relation of operations, that the local operations satisfy the laws, and that what an operation requires is enough for it (`LocalLaws`); the soundness for a function (`Soundness`) |
| `Transform/` | transformations of functions, on the value form of `Value/` and the check of facts of `Facts/`: what the decision is told of a function (`localValueRules`, `localSkelRules`), a transformation of a function as a checked step, which elaborates a stored source and a stored target, checks the facts of both and decides that the target follows the skeleton of the source, with what it returns or why it refuses, and whether the functions of a second program over the same headers follow those of a first, one by one (`Step`); the function dialect's value form, its laws, and that two accepted functions of which one follows the other mean the same (`Local`); what a step means: the callees that a statement about a function is made against, the meaning of an accepted function, that two accepted functions mean the same, the theorems of a step, and that a term of a function returns valid values on valid values in scope and means the same against two tables of callees that agree on valid inputs (`StepSound`); two untrusted transformations of a stored function, which drop the operations whose results are not used and share repeated operations, accepted only through the step (`Passes`). The operations of a function that commute, each placed in the table with its two operands in one order, are the sum and the product of naturals, the conjunction and the disjunction of truth values, and the equality of naturals and of truth values (`OwnedName.commutes`, `Step`) |
| `Admission/` | the elaboration of one definition against the headers before it, of a program of functions, and its round trip in both directions (`Elaboration`); the association of a program and its resolution in it, with the arguments of an instance of a generic declaration that it records, and an admitted program (`Admission`); the check of one definition against the headers before it (elaborated, then its facts checked), admission as that check for each definition in order, and the acceptance of a typed program by the check of facts as a proposition (`Check`); the soundness of the check of facts for the functions of a program, and that a program whose functions follow those of another means what the other means (`Programs`); the statements of `Statements.lean` about functions, each a theorem whose type is the statement, for every record of functions whose functions are `admit`, `check` and `elaborateFunctions`, the round trip from a typed program for those without protocols (`Theorems`) |
| `World/` | the description of a layer (a handler of a role), whose code reads its inputs by position, in the one context of the core that binds inputs to the names `0, 1, 2, …` (`Ctx.positional`), and its meaning as a handler; the network of the roles, and the runs of a protocol and of one role alone |
| `Scheme/` | the declaration of a scheme, who proves and who verifies, a deployed scheme and the run of a role under its handlers, and what deployment decides about scopes and keys |
| `Run/` | how a run of the executor ends, the executor, and the prover's and the verifier's runs |
| `Format/` | formats of values and the codecs of a model |

`Functions.lean` and `Statements.lean` come after every directory: they may import any of them.

## What is proved, what is defined, what is still to be built

Proved, with no axiom beyond `propext` and `Quot.sound` (the audit checks every declaration):

- the projection theorem (`Zkc.Core.projection`, `Projection/Theorem.lean`): the program of
  every role of every protocol of a typed program, run on what the role holds of one input, is
  a projection of the protocol's process; where the protocol returns, the role returns what it
  holds of the results;
- the rules of proof on every path (`Process.every_bind`, `every_mono`, `every_iterate`,
  `every_iterate_below`), and the
  rule of a call (`Contract.call`, `Law.call`): a contract of a function, a
  property of its entry in a table, installed at an actual call with the operands and the
  continuation taken from the term;
- that the process with the record of a run is, without the record, the process of the term
  (`Term.observe_fst`), and the lemmas on `Proj`, on what a role holds and on literals;
- the round trip in both directions: for rules whose laws hold, the erased form of a term whose
  case analyses without an arm give nothing elaborates in its context to the term
  (`elabBody_erase`, `Program/Erase.lean`), and elaboration gives only such terms
  (`elabBody_armed`, `Program/Elaborate.lean`); for rules whose written forms are canonical, a
  term that elaboration gives erases to what was elaborated (`eraseBody_elab`); the local rules
  are lawful over headers with distinct keys and canonical, and the written form of a local
  operation names it (`localRules_lawful`, `localRules_canonical`, `LocalOp.print_injective`,
  `Program/LocalRules.lean`); the erased body of every typed function elaborates as its input
  names, its body and its conditions, and a function that elaboration gives erases to the region
  that was elaborated (`elabFn_erase`, `eraseFn_elab`, `Program/ElaborateLocal.lean`); the erased
  form of every typed program of functions elaborates as the program, and a program that
  elaboration gives erases to the program by names that was elaborated
  (`elaborateFunctions_erase`, `erase_elab`, `Admission/Elaboration.lean`);
- that every local operation keeps validity: on valid operands, the results that it gives are
  valid (`localOp_valid`, with `localOp_row_valid`, `localOp_owned_valid`,
  `localOp_literal_valid`, `localOp_call_valid` and `ownedOp_valid` for the operations that the
  core owns, `Meaning/Validity.lean`);
- the decisions of distinct addresses and of single assignment: the first repeated address, or
  none exactly when the addresses are distinct (`Term.repeatedAddress_eq_none`), and the first
  name bound a second time, or none exactly when every name of a definition is bound at one
  place (`Term.rebound_eq_none`, `Program/Conditions.lean`); elaboration refuses a name bound a
  second time by the rule `assignment`, at the instruction that binds it again. Linear use is
  defined by its decision, by name (`Term.UsedOnce` is `Term.misuse … = none`,
  `Program/Linear.lean`), so it has no separate statement to prove;
- the laws of the base relation (`Process.SameWhen`, `Process/Same.lean`): an equivalence, a
  congruence for `bind`, `map`, `mapHalt`, `recover` and bounded iteration, which carries a
  property on every path, and which a handler whose replies are permitted keeps, retry included
  (`Handler.run_same`); between processes without effects it is equality
  (`Process.SameWhen.eq_of_noSig`); and the rules of a value that a process can return
  (`Process.CanReturn`);
- places (`Program/Place.lean`, `Meaning/Place.lean`): a term in a wider context, by the one
  structural rule on contexts, erases to the same program (`eraseBody_reindex`) and means the
  same on environments that agree (`Term.denote_reindex`); a term is its first instructions
  filled with what follows them (`Term.fill_splitAt`); replacement: two terms that mean the same
  wherever a run reaches a place give wholes that mean the same (`Hole.fill_same`); and the
  meaning of a term depends on its environment only at the names that it reads
  (`Term.denote_reads`);
- the value form and the decision, for any dialect (`Value/`): an identifier read through the
  table has one value (`Reads.functional`); two processes that run one skeleton mean the same
  (`Skel.Runs.same`); a term that never stops `undefined` runs its own skeleton
  (`Term.skeleton_runs`), and a term that follows a skeleton whose leaves are made in order above
  the values of the run runs it (`Term.follows_runs`); so two definitions of which the second
  follows the skeleton of the first mean the same on every input on which neither stops
  `undefined` (`followsSkeleton_sound`). For functions (`Transform/Local.lean`): the local operations
  that are values satisfy the laws of the value form against callees with distinct keys of which those
  that cannot stop stop only `undefined` (`localValueRules_binding`), following is lawful over
  headers with distinct keys (`localSkelRules_lawful`), and two bodies accepted by the check of
  facts of which the second follows the skeleton of the first mean the same on every valid
  input, for any replies permitted, so that their processes are equal (`functions_follow_same`,
  `functions_follow_equal`). The decision knows one law, the order of the two operands of an
  operation that commutes, sound by the law `commutative` of `ValueRules.Binding`, which the six
  operations that the core owns whose meaning is symmetric satisfy for all values
  (`localValueRules_binding`): `x + y` and `y + x` are found the same; associativity, and a law
  of a row of the vocabulary, which would be the model's, are not known;
- transformations as checked steps (`Transform/StepSound.lean`, `Admission/Programs.lean`):
  the stored form of what a stored function is accepted as is that stored function
  (`acceptFn_erases`), and an accepted
  function never stops `undefined` on valid inputs and returns valid values (`AcceptedFn.safe`); a step
  that `transform` accepts relates functions with the same meaning on every valid input, against
  callees with distinct keys that are safe, keep validity and stop only `undefined` where their
  headers say that they cannot stop (`transform_sound`); the stored forms of what a step returns
  are what it was given (`transform_erases`), and two steps compose (`transform_then`). On valid
  values in scope, a term of a function returns valid values against callees that keep validity
  (`Term.denote_valid`), and means the same against two tables of callees that agree on valid
  inputs when one keeps validity (`Term.denote_tables`); so a program whose functions follow
  those of another over the same headers, both accepted by the check of facts, gives every
  function the meaning on valid inputs of the function of the other with its header, the callers
  of a replaced function included (`Defs.functionsFollow_sound`); the protocols of the two
  programs are not compared, and nothing is said of them. This is the family of relations "the
  same meaning", stated for functions as equality of what they return; the other families
  (guards compared by segment, representations, reductions) are not built, and neither is the
  acceptance of a target by the places where its source evaluates an operation with a domain;
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
- the statements of `Statements.lean` about functions (`Admission/Theorems.lean`): each theorem
  has the statement as its type, for every record of functions whose `admit`, `check` and
  `elaborate`, those that the statement reads, are the definitions `admit`, `check` and
  `elaborateFunctions`. A program that elaboration gives erases to the program by names that
  was elaborated (`eraseOfElaborated`), and the erased form of a typed program elaborates as the
  program, for the typed programs without protocols (`roundTrip`). What `admit` returns is the
  elaboration of what was given, with the association resolved in it (`admitsWhatWasGiven`);
  `check`, one definition at a time from no headers, gives the headers of the admitted program
  (`checkAgrees`); a function of an admitted program never stops `undefined` on valid inputs
  and returns valid values (`functionsSafe`, `functionsKeepValidity`); an admitted program
  respects its annotation (`annotationHolds`); a function whose header says that it cannot
  stop does not stop (`headersSayWhoStops`), since such a function stops only `undefined`
  (`Defs.fnTable_stops_undefined`, `Meaning/Stops.lean`); two accepted functions of which
  the second follows the skeleton of the first mean the same (`functionsSame`, which is
  `functions_follow_same`); a step of transformation that `transform` accepts relates functions
  with the same meaning (`transformSound`, which is `transform_sound`), and every function of a
  program whose functions follow those of another means what the function of the other with its
  header means (`replacedFunctionsSame`, which is `Defs.functionsFollow_sound`).

Defined: everything else, from the terms and their meanings to deployment, the network and
the runs.

Still to be built:

- the functions of the record `Functions` (`Functions.lean`), with their types. For a program
  of functions, `elaborate`, `admit` and `check` are built as the definitions
  `elaborateFunctions`, `admit` and `check` (`Admission/Elaboration.lean`,
  `Admission/Check.lean`); the record gets them when protocols are elaborated, which needs the
  rules of the protocol dialect and the walk of role programs by the check of facts (until
  then `admit` and `check` refuse a protocol). `eraseRole`, `format`, `deploy`, `identity`,
  `execute` and `schedule` are still to be built;
- the theorems that `Statements.lean` states and does not prove, each with what it preserves
  (execution and state, a view, validity or progress): those about functions are proved of
  the definitions above for a program of functions (`Admission/Theorems.lean`); `rolesSafe`,
  `realized`, `anyOrder`, `replayed`, `recordsAreValid`, `schedulerRuns`, those of deployment
  from `deployKeeps` to `identityReads`, `executorRuns` and `formats` are not, and neither is
  `roundTrip` for a program with protocols;
- for transformations, only the family "the same meaning" is built, for functions, as a pair of
  accepted functions (`Transformed`). Not built: a transformation as a record of its contract,
  its relation and its evidence; the other families of relations (guards compared by segment,
  representations, reductions) and claims with their evidence; the acceptance of a target by
  the places where its source evaluates an operation with a domain, so the safety of a target
  is its own check of facts and not part of following; a guard whose condition is already known
  true dropped or added on either side (every guard of the second term must be the skeleton's
  next entry); a loop or a choice that only computes and that nothing uses dropped, and two
  loops fused (every form of control stays in the skeleton); the comparison of the protocols of
  two programs; the place at which following refuses (`followsSkeleton` gives a truth value);
- the index of a definition (bindings, uses, captures of a region, summaries, each query with
  its lemma) and the facts that the check of facts knows at a place, as one thing that a
  transformation and a proof can ask: of the index only `Term.reads` is built, and the check of
  facts keeps what it knows to itself;
- single assignment is decided for every admitted function and no theorem uses it yet: the
  value form reads names through a scoped context of identifiers. It is, for now, a contract of
  the stored form and of the untrusted transformations.

`Process/`, `Program/`, `Meaning/` and `Projection/`, and the data of `Admission/`, are what
the projection theorem and the meanings stand on; `Value/` is built for any dialect; `Facts/` is
built for functions; `Transform/` gives the value form its instance for functions. `World/`,
`Scheme/`, `Run/` and `Format/` are defined and type-checked, and no implementation has
exercised them yet: the code that first builds one of these parts changes its definitions here
first.

## Tests

The tests of the core are the library `ZkcCoreTests` (`Zkc/Tests/Core/`), whose checks the
kernel runs when they are built:

- `Shapes.lean`: protocols of different shapes written as typed programs by names, with what
  elaboration decides about each, and meanings that compute; it gives the other tests `var`, the
  notation for a variable of a typed term written by hand, whose proof that the context has the
  name is decided by evaluating the context;
- `Controls.lean`: controls at the edges of the definitions (the world, the scheduler, handlers
  and the retry of an attempt, distinct keys, codecs, linear use, who proves, forks, the start
  of a layer, laws and contracts of functions at their calls, the lookup of a definition), and
  the theorems that are the reasons for the definitions' shape;
- `Consumers.lean`: each consumer's side, written against the core;
- `Operations.lean`: for each written name of an operation that the core owns, a function that
  elaborates, whose erased form elaborates back and is the function by names; written forms
  with other types, numbers or item types refused;
  the operations that would copy or drop a part refused at a linear type, and so is giving a
  sequence of linear items a size; each meaning at a value, and each domain at a value outside
  it;
- `Elaboration.lean`: for each rule of elaboration that a program of functions can break, except
  `row` (over the standard vocabulary, `Tests/Vocabulary/Core.lean`) and `association`
  (`Admission.lean`), and each condition of a body, a program by names that is accepted and one
  that is refused, compared with the whole refusal (rule, place and what the rule found); where
  a refusal is at each construct (a name not in scope, the number of results, a refusal inside
  or after a region, the first missing name); the literals of each type; linear use at each
  construct, each refusal naming the value, and each kind of type that is linear, with a
  vocabulary whose nominal type is linear; single assignment at each place that binds a name (a
  result bound twice in one body, two results of one instruction, an input of the definition
  bound again by a result and two inputs with one name, an input of a region with the name of a
  value around it, sibling regions of a choice and sibling arms of a case analysis, the blocks
  of a stepped loop, a name bound again as the results of a choice, of a case analysis and of a
  loop, and of a choice inside a block, whose place has the block), each refused by the rule
  `assignment` with its place and the name, and one
  name in two definitions accepted; the case analysis without an arm that the erased form
  cannot tell apart; and the round trip of each accepted program in both directions;
- `Facts.lean`: the check of facts on functions written by names: the conformance cases of the
  reference that a function can express, by their identifiers, accepted or refused as the case
  says with the whole refusal; for each operation with a domain and for a restricted row, an
  application accepted and one refused; sharing and the scope of facts in sibling regions, in
  loops, after a choice, and of a new name where a program would bind a name again (which
  elaboration refuses by the rule `assignment`); a loop over a range whose end is a
  run-time value; a power too large to compute, and the limit; what the check does not conclude
  (a range from a comparison with a value whose range is not one number, an order with an
  offset, the range of a sum from its first value), each refused with the whole refusal; which
  code does not run: the body of a loop of the written count zero, an arm whose payload has no
  value, a function with an input that has none, and not the arm that a loop's index never
  takes (`N-TY9e`) nor the code after a guard that contradicts what is known; what each
  condition teaches (`and`, `or`, `==`, `!=`, an order, a sum, a difference, the shapes of a
  choice); what case analyses, choices, blocks, payloads and carried sums give of a natural;
  the ranges of each arithmetic operation and conversion; code that does not run after an
  operation or a loop whose results have no value; the place of a refusal and of a bound inside
  a block, and the order of the bounds; and which types have no value;
- `Same.lean`: whether a function follows the skeleton of another, on pairs of functions
  written by names, elaborated and decided: a repeated computation shared, computations reordered between
  guards or moved around them with the guards in their order, a computation moved out of a loop,
  other names for the values, a call of a function that cannot stop shared, `x + y` against
  `y + x`, and a product and a sum with their operands exchanged in a loop after a guard, each
  accepted; `x - y` against `y - x`, `(x + y) + z` against `x + (y + z)` (the decision does not
  know associativity), a row of the vocabulary with its operands exchanged, guards in the other
  order, a guard dropped, a call of a function that can stop moved across a guard, two loops
  against one (the decision does not fuse loops), and another key on a guard, each refused;
  each instruction kept in order, accepted: a choice, a case analysis, a block, a loop as often
  as a value says and a call of a function that can stop, each with other names, a value moved
  out of and into a region of a choice, and a value moved across a call of a function that can
  stop; pairs that differ only in a guard's condition, a loop's initial values, a block's number
  or the operand of a call of a function that can stop, each refused by that comparison; the
  theorem for functions applied to two accepted pairs, `x + y` and `y + x` the second;
  and the two controls on the definitions of the value form: two terms that follow one skeleton
  whose leaf is not made above the values in scope and do not mean the same (why following asks
  for `Skel.Fresh`), and an attempt whose end cannot return followed by what stops `undefined`
  (why what follows an attempt runs only from an end that can return);
- `Transform.lean`: transformations of functions as checked steps: a function with unused and
  repeated operations, in its body and in a loop, given to `removeUnused` and then to
  `shareRepeated`, each stored result compared whole, each step accepted by `transform`, and the
  two steps composed by `transform_then`; the two passes on a function with a choice, a case
  analysis and a block, with unused and repeated operations inside and around them, each result
  compared whole and each step accepted; a target refused by elaboration; three targets that
  follow the skeleton of their source and that the check of facts refuses, which shows that
  following leaves the target's safety to the step (an inverse moved above the guard that it is
  not zero, read before a choice in whose region it was justified, read before a loop in whose
  body a guard justified it); a target that is accepted but not decided (two guards exchanged),
  and a source that is not accepted, each with its whole refusal; a target that computes another
  result, not decided; a target with the operands of a sum exchanged, accepted; a program of two
  functions whose callee is replaced by what `removeUnused` gives, which follows the first, with
  `Defs.functionsFollow_sound` applied to the caller; and a callee replaced by one that computes
  another result, which does not follow. The decision of equality of stored functions is written
  there;
- `Place.lean`: places inside a term, on a dialect of truth values written there (it has guards
  and attempts): replacement (`Hole.fill_same`) of a value that nothing uses in the body of a
  loop inside an attempt, and there of the carried value by the input, which differ only on
  environments of the body that no run reaches; a replacement after a guard that differs only
  where the guard stops, accepted, and the control, one that differs where the guard holds, for
  which the premise of replacement fails and the wholes do not mean the same; a term that means
  the same in two environments that agree on what it reads (`Term.denote_reads`), and gives
  different results in two that differ there; a term split after two of its instructions and
  after more than it has, each filled back (`Term.fill_splitAt`); and a term in a wider context,
  with its meaning (`Term.denote_reindex`), and the control of an environment that does not
  agree, on which the meaning differs, and with its erased form (`eraseBody_reindex`);
- `Admission.lean`: `admit` and `check` on programs of functions: a program of two functions
  admitted with its whole annotation; admission stopped at the first refused definition, with
  every refusal of it and nothing of a later one, for a refusal of the check of facts and for
  one of elaboration; `check`, one definition at a time, giving the headers of the admitted
  program; an association whose key names a definition, resolved in the admitted program, and
  one whose key is no definition, refused by the rule `association`; a protocol refused.

In `lean/compiler`, `lake build` builds the core, the vocabulary, their tests and the audit;
`lake test` builds the tests of the core (the library is the test driver), which need those of
the vocabulary; and `lake exe zkc-audit` audits the core, the vocabulary and their tests: no
axiom beyond `propext` and `Quot.sound` in any declaration, the replay of every declaration
through the kernel, and three rules on imports (a module of the core imports only the core,
`Init` and `Std`; no module of the core imports a module of the tests or of the tools; the root
imports every module of the core). The audit does not check the order of the layers or the rule
on modules of proofs.

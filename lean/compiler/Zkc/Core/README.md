# Core

The core of the zkc compiler: one type of typed terms over three dialects (a function, a
protocol of all its roles, the program of one role), their meanings as processes, the
projection of a protocol to the programs of its roles with the theorem that every role program
is a projection of its protocol, the elaboration of a program of functions by names with its
erased form and the round trip in both directions, what elaboration decides about a body,
places in a term and replacement, the evidence that a statement about what a program does is
made with (claims in a scope, being assured, facts at a place, the relation "same meaning",
summaries of definitions), the analysis of a term for any dialect (one walk that gives its value
form, checks its facts, and follows the analysis of another term) with its soundness, the
judgments about a function (assured, the same meaning) with the two decisions that produce them,
a transformation of a function as a step from an assured function that follows its analysis with
the target and never admits the source again, the data of an admitted program and of a deployed
scheme, the run of a role under the handlers of its deployment, and the types of the functions
that are still to be built with the statements that they must satisfy. It is the library
`ZkcCore` of the package `zkc_compiler` (`lean/compiler`), in the namespace `Zkc.Core`; it
imports only `Init` and `Std`. Each file is a Lean module whose definitions are exposed
(`@[expose] public section`), so that a proof in another module unfolds them. The root module,
`Zkc/Core.lean`, imports every module of the core. The standard vocabulary, its keys and its
table, is the library `ZkcVocabulary` beside the core ([guide](../Vocabulary/README.md)); it
imports the core, and the core does not import it.

## Layers

The directories are layers: a module imports modules of its own directory and of the
directories above it in this table, never of a directory below. A module of proofs, one whose
definitions if any are used only in statements and proofs, is imported only by modules of proofs
and by the root, with two exceptions in `Transform/`: `Step` imports `Facts/LocalLaws.lean` for
the callees (`Callees`) that the judgments about a function quantify over, and `Assured` imports
`StepSound`, whose theorems the assured functions that it makes carry.

| Directory | Holds |
|---|---|
| `Process/` | processes (well-founded trees of effects), the one property on every path (`Process.Every`) and its rules (iteration among them, with an invariant asked of every step or only of the steps below a count), handlers, their composition, and the retry of an attempt; the base relation, two processes that mean the same along every path of permitted replies, an equivalence and a congruence for what a process is built with, which a handler whose replies are permitted keeps, retry included, and a value that a process can return on some path of permitted replies with its rules (`Same`) |
| `Program/` | keys, labels, occurrences, sites, places, stops and names, a name being a number that a definition binds at one place (`Identity`); the position of an item in a list (`Member`, by which a call names a definition among the headers), lists of values of types (`HList`), types, the vocabulary, whose keys say everything that tells a nominal type, a row or a law from another, with the law that the domain row of a restricted row decides it, which types have no value, and its models (`Vocabulary`); contexts of names, a finite map from names to types behind a small interface, the names of a binding, variables (a name with the proof that the context has it at its type) and environments of names, with their lemmas, among them what an environment with one more name bound gives at that name and at another, the structural rule on contexts (a context within another) and environments that agree at some names (`Context`); lemmas about lists and `Except` that the proofs use (`Library`); terms, whose bindings carry the names that they bind, their addresses, whether their case analyses without an arm give nothing, and that every name of a definition is bound at one place (`Term.BoundOnce`) (`Term`); items placed by the low bits of a natural, the keyed collection of the decisions of distinct addresses and of single assignment and of what the check of facts knows (`BitTree`); the decisions of distinct addresses and of single assignment, with what failed and the place of a name bound a second time, each proved to decide its proposition (`Conditions`); linear use, defined by its decision, which says which value, by its name, is not used as it must be and where (`Linear`); located types and role maps (`Located`); the record of a run (`Record`); the kinds of events and the shape of a protocol (`Shape`); the three dialects (`Dialects`); projection, the translation of a protocol's term to a role's (`Project`); a typed program, its definitions with the names of their inputs and what elaboration decided about each body, one definition elaborated against the headers before it and a program extended by it, and the lookup of a definition by its key (`Typed`); the program by names that a frontend gives (`Syntax`); refusals: the rules of the core, what a rule found and the place where it found it, as data (`Refusal`); the elaboration of a region over the rules of a dialect, each refusal made at its place (`Elaborate`); erasure, the program by names of a typed term, and its round trip in both directions over lawful and canonical rules (`Erase`); the written form of each operation of a function and its resolution, with both halves of the law of written forms, and the rules of the local dialect (`LocalRules`); the elaboration of a function, its erased form and their round trip in both directions (`ElaborateLocal`); the erased form of a typed program (`EraseProgram`); what an operation with a domain asks of an application, as data, and the values that it names, the items of a list at positions (`atPositions`), by which an operand names the operands of a written operation, and the ranges of naturals with what it is for a natural to be in one (`Requirement`); a term in a wider context, with the same erased form, a term with one place left open and the term that fills it, a term split after its first instructions, and the names that a term reads (`Place`) |
| `Meaning/` | events and what a role holds (`Events`); the fold of a term over the semantics of a dialect, which binds the names of each binding to its values, a value with its type and the values of a list with their types (`Semantics.Dyn`, `Semantics.dyns`) with their lemmas, and a loop, which holds what it collects latest first and reverses it once where it becomes one value (`Fold`); what a requirement says of values: how a value reads (`Reading`), the values that the operands of a requirement name, and that it holds (`Requirement.Holds`), the language in which an operation states its domain and a definition its summary (`Requirement`); the semantics of a function, of a protocol and of a role program (`Local`, `Protocol`, `Role`), with the meaning of every operation that the core owns (`Local`); what it is for the functions of a table to keep validity and never stop `undefined`, that every local operation keeps validity, and that a type with a valid value has a value (`Validity`); the meanings of a whole program (`Program`); that a function whose header says that it cannot stop stops only `undefined` (`Stops`); the rule of a call (`Call`); places with their meaning: a term in a wider context means the same, what it is for a run to reach a place and a fact at a place, replacement, and that a term's meaning depends only on the names that it reads (`Place`) |
| `Projection/` | the relation of a role's process to a protocol's and its lemmas (`Proj`), the proof for one term (`Sound`), and the theorem for every definition of a program (`Theorem`) |
| `Evidence/` | what every statement about what a program does is made with, for any dialect and interpretation, with nothing of an analysis: the starts of a term that a statement is about (`Entry`), claims on every authorized start and permitted reply (`Claim`), claims under a handler, whose returns and stops carry the observer's state (`Claim.Under`), and what it is for a term to be assured in a scope: never stopping undefined and returning valid values (`Assured`) (`Claim`); facts at a place (`Fact`), the relation "same meaning" in a scope (`Equivalent`), which composes and along which claims and being assured move (`Equivalent.claim`, `Equivalent.trans`, `Assured.transfer`), replacement under a fact (`replace_with_fact`), and laws with a premise applied where the premise is a fact (`ConditionalLaw`) (`Relation`); the summary of a definition in the language of requirements and what it is for one to hold, which with no requirement and no guarantee is being assured (`Summary`, `Summary.Holds`, `Summary.holds_empty`) (`Summary`). It imports nothing of `Value/` or `Facts/` |
| `Value/` | the value form of a term, for any dialect: the table of applications by written form and operand identifiers, placed by a number computed from the written operation's number and those identifiers and by each result's identifier, the state that carries it (the next identifier, and the refusals and the bounds of loops that the analysis finds), and the identifiers of the names in scope (`Table`); valuations of identifiers, what the table says of a valuation, a well-formed table, a state and a valuation that agree, and the growth of the state as identifiers are made and applications shared, which keeps every name in scope with an identifier below the next (`Valuation`); the skeleton of a term, what it keeps in order (effects, guards, every form of control) on identifiers of the table, what the value form reads of the operations of a dialect (`ValueRules`), and what a dialect must decide for following a skeleton (`Skeleton`); the leaves of a skeleton, apart from the table, below a number and made in order, as the table grows (`Leaves`); the laws that tie the values of a dialect, with their types (`Semantics.Dyn`, `Meaning/Fold.lean`), to a semantics (`ValueRules.Binding`), the reading of an identifier from the leaves through the table, the processes that run a skeleton, and that two of them mean the same (`Runs`); names that agree with a table, the count of a loop on identifiers, and what a shared application reads, with the operands of an operation that commutes in the table's order (`Agrees`). An application of an operation that a dialect says commutes is placed in the table with its two operands in one order, the smaller identifier first, whichever way they were written (`ValueRules.order`) |
| `Facts/` | the count of every loop that a run reaches (`Term.EveryLoop`), the annotation of an admitted program, which is the bounds of its loops, and what it is for a program to respect it, in its functions and in its role programs (`Facts`); what the analysis is told about the operations of a dialect, the one description of them (`FactRules`): which operations are values and how they are written, which written operations commute, what a written operation requires, the ranges of its results and how its result reads, which types have no value, and a number for each written operation by which the table places its applications, with the part that the value form reads (`FactRules.values`) (`OpFacts`); what the analysis knows beside the table of `Value/`, each part placed by an identifier, and how an identifier reads by the operation that gave it, with the rules that decide a requirement, which read a sum with its operands in either order, and learn from a truth value, the range below `r` of a sum of `x` and `t`, in either order, where a loop made the order `t < r - x` for its index, the check of the requirements of an application, and the lemmas of the ranges that it defines (`State`); the analysis, one walk over a term of any dialect, which keeps the identifier of each name in scope, shares each value in the table, decides the requirements of a value from what is known where it is evaluated, learns from guards, choices, loops and the ranges of operations, records the bound of each counted loop and gives the skeleton of the term, or, given the analysis of another term, follows its skeleton and records each place where the term is not the skeleton's next entry (`Analysis.walk`, `Analysis.analyse`, `Analysis.follow`), in which a region is dead only where what is written says that it never runs, with the range of a carried natural after a loop and its lemmas; and the check of facts, the refusals of the analysis or the bounds that it recorded (`checkFacts`) (`Walk`); what the local dialect tells it: which operations of a function are values and which commute, the arithmetic of ranges (a power's ends computed only when they are small enough) and its lemmas, and what following decides for a function (`localFactRules`, `localSkelRules`) (`Local`); what what is known and the identifiers of the values that the requirements name say of a valuation of identifiers, one step of the walk, and the laws of `OpFacts` as propositions, against a reading of values and what a requirement says of them (`Meaning/Requirement.lean`) (`Valuation`); that the rules of what is known are true (`Learning`); the laws that a dialect proves of its rules and its semantics (`FactRules.Lawful`, `Laws`); what the walk does to its state, to the places that differ and to the skeleton, whatever the run, on which the runs of the walk and its soundness both rest, and that the check of facts gives bounds at the places of its definition (`Growth`); that a term runs the skeleton of its walk (`WalkRuns`); the soundness of the walk where no skeleton is followed (`Soundness`) and while one is followed (`SoundnessFollowing`); the theorems of the analysis, among them that a term that follows a safe term, however that is known, is safe and means the same (`Theorems`); the local dialect's reading of values and relation of operations, the laws of the function dialect, the callees that a statement about a function is made against, the soundness of the check of facts for a function, and that a summary of a function that holds of its entry is its contract (`LocalLaws`) |
| `Transform/` | functions, the judgments about them, and transformations of functions, on the analysis of `Facts/`: a function elaborated against the headers before it (`TypedFn`, `typeFn`), its meaning on inputs against callees, what it is for it to be safe, to have its loops bounded, to be assured with bounds, and for two of them to mean the same, as propositions against every `Callees`, the check of facts of a function and whether a second follows the analysis of a first, as decisions, why a step is refused (`StepRefusal`), and whether the functions of a second program over the same headers follow those of a first, one by one, with no refusal and no place that differs (`Step`); the two producers of assurance, the check of facts (`TypedFn.check_assured`) and following a function that is safe by any route (`TypedFn.follows_assured`), "the same meaning" symmetric and transitive, that a function is safe exactly when its body is assured in the sense of `Evidence/`, that two functions of which the second follows an accepted first mean the same, and that a term of a function returns valid values on valid values in scope and means the same against two tables of callees that agree on valid inputs (`StepSound`); an assured function, made only with its assurance, by admission (`admitFn`) or by a step from an assured function (`AssuredFn.step`), which never admits its source again, and the theorems of a step (`Assured`); two untrusted transformations of a stored function, which drop the operations whose results are not used and share repeated operations, accepted only through the step (`Passes`). The operations of a function that commute, each placed in the table with its two operands in one order, are the sum and the product of naturals and the equality of naturals and of truth values (`OwnedName.commutes`, `Facts/Local.lean`); the conjunction and the disjunction of truth values, whose meaning is symmetric too, keep the order written, since the check of facts learns their operands in that order |
| `Admission/` | the elaboration of one definition against the headers before it, of a program of functions, and its round trip in both directions (`Elaboration`); the association of a program and its resolution in it, with the arguments of an instance of a generic declaration that it records, and an admitted program (`Admission`); the check of one definition against the headers before it (elaborated, then its facts checked), admission as that check for each definition in order, and the acceptance of a typed program by the check of facts as a proposition (`Check`); the soundness of the check of facts for the functions of a program, and that a program whose functions follow those of an accepted program means what the other means and is safe and keeps validity, with no acceptance asked of it (`Programs`); the statements of `Statements.lean` about functions, each a theorem whose type is the statement, for every record of functions whose functions are `admit`, `check` and `elaborateFunctions`, the round trip from a typed program for those without protocols (`Theorems`) |
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
- the analysis, for any dialect (`Value/`, `Facts/`): an identifier read through the table has
  one value (`Reads.functional`), and two processes that run one skeleton mean the same
  (`Skel.Runs.same`). One walk analyses a term and follows the analysis of another
  (`Analysis.walk`). For rules that are lawful for a semantics (`FactRules.Lawful`), a body with
  distinct addresses that the analysis refuses nowhere, on valid inputs and permitted replies,
  respects the bound that the analysis recorded for each of its loops, never stops `undefined`,
  returns valid values, and its process runs the skeleton of the analysis over its table
  (`Analysis.analyse_sound`, `Facts/Theorems.lean`); a body that follows the analysis of a body
  that is safe on the given inputs, however that is known, with no refusal and no place that
  differs is safe in the same way and means the same as it (`Analysis.follow_assured`), which
  reads neither the first body's addresses nor whether its analysis refuses anything; a body that
  follows an accepted body is its case (`Analysis.follow_sound`). Nothing is assumed of the
  safety of the second; its addresses are distinct, which elaboration decides; and that it is
  safe does not need the first to be safe (`Analysis.follow_safe`), only that the two mean the
  same does. Beneath them: what the walk
  adds to its state, how it grows it, and the skeleton that it builds (`Analysis.Facts.walk_adds`,
  `Analysis.Facts.walk_grows`, `Analysis.Facts.walk_skeleton`, `Facts/Growth.lean`),
  that a body runs the skeleton that the walk builds or follows
  (`Analysis.ValueSide.walk_runs_built`, `Analysis.ValueSide.walk_runs_followed`), and the
  soundness of the walk construct by construct (`Analysis.Facts.walk_sound_fresh`,
  `Analysis.Facts.walk_sound_follow`). Following decides what the value form shows: sharing,
  values that nothing uses, the order of values, and one law, the order of the two operands of an
  operation that commutes, sound by the law `commutative` of `ValueRules.Binding`: `x + y` and
  `y + x` are found the same, and so is a fact on `i + 1` of `1 + i`; associativity, and a law of
  a row of the vocabulary, which would be the model's, are not known. It keeps all control;
- the laws of the function dialect and the check of facts of a function (`Facts/LocalLaws.lean`):
  against callees with distinct keys that never stop `undefined` on valid inputs, keep validity,
  and stop only `undefined` where their headers say that they cannot stop (`Callees`), the rules
  of the function dialect are lawful for the semantics of a function, for any permitted replies
  (`localFactRules_lawful`): the local operations that are values satisfy the laws of the value
  form (`localFactRules_binding`), among them that the four operations that the core owns that
  commute give the same result on their operands exchanged, for all values; what the
  analysis knows of the written operations is true;
  the requirements of every local operation are enough for it (`localOp_defined`) and name values
  that exist (`localRequires_runs`); following is lawful over headers with distinct keys
  (`localSkelRules_lawful`). So the check of facts is sound for a function (`checkFacts_sound`):
  for a body with distinct addresses that `checkFacts (localFactRules V fns) (localSkelRules V
  fns)` accepts, against such callees, on valid inputs the process never stops `undefined`,
  returns valid values, and every loop as often as a count runs at most the bound given for its
  place. For a typed program each of whose functions the check accepts (`Defs.Accepted`), every
  function is safe and keeps validity, and the functions' part of `Respects` holds
  (`Defs.FunctionsRespect`; `functions_sound`, `typed_functions_sound`, `Admission/Programs.lean`),
  which for a program without protocols is `Respects` (`Respects.of_functions`,
  `Facts/Facts.lean`); there the callees of a function, the functions before it, stop only
  `undefined` where their headers say that they cannot stop with no check of facts
  (`Defs.fnTable_stops_undefined`, `Meaning/Stops.lean`);
- the evidence layer (`Evidence/`), for any dialect: a claim moves along the relation "same
  meaning" in a scope, stops included (`Equivalent.claim`), which composes (`Equivalent.trans`),
  so that a term that means the same as an assured term is assured (`Assured.transfer`); two
  terms that mean the same where a fact holds give wholes that mean the same, at any place where
  the fact holds (`replace_with_fact`, from `Hole.fill_same`), and so does a law with a premise
  where the premise is a fact (`ConditionalLaw.apply`); the summary with no requirement and no
  guarantee holds of a definition exactly when, on valid inputs, it never stops undefined and
  returns valid values (`Summary.holds_empty`); and for the function dialect, a summary holds of
  a function's entry in a table exactly when the entry has the contract (`Contract`) whose
  precondition is valid inputs that satisfy the requirements, whose postcondition is valid
  results that satisfy the guarantees, and whose stops are not `undefined`
  (`localSummary_contract`, `Facts/LocalLaws.lean`);
- the judgments about a function and transformations as steps from an assured function
  (`Transform/StepSound.lean`, `Transform/Assured.lean`, `Admission/Programs.lean`): a function
  that the check of facts accepts is assured, safe and with its loops bounded by what the check
  gives, against `Callees` (`TypedFn.check_assured`); a function that follows the analysis of a
  function that is safe, by whatever route, with no refusal and no place that differs is assured
  with the bounds recorded while it follows, and the two mean the same on every valid input
  (`TypedFn.follows_assured`, from `Analysis.follow_assured`): the second is not analysed by
  itself, and the refusals of the first's own analysis are not read. A function is safe exactly
  when its body is assured, in the sense of `Evidence/`, in the scope of the empty path and its
  inputs bound to valid values (`TypedFn.safe_iff_assured`); "the same meaning" of functions is
  symmetric and transitive (`TypedFn.SameAs.symm`, `TypedFn.SameAs.trans`). An assured function
  (`AssuredFn`) is made only with its assurance: by admission (`admitFn`) or by a step from an
  assured function (`AssuredFn.step`), which never admits its source again. A step relates
  functions with the same meaning (`AssuredFn.step_same`); two steps compose with no condition
  on the middle function (`AssuredFn.step_then`); two steps from one function give functions
  with the same meaning (`AssuredFn.step_both`); and the stored form of what admission and a step
  return is what they were given (`admitFn_erases`, `AssuredFn.step_erases`). On valid values in scope, a term of a function returns valid values
  against callees that keep validity (`Term.denote_valid`), and means the same against two tables
  of callees that agree on valid inputs when one keeps validity (`Term.denote_tables`); so a
  program whose functions follow those of another over the same headers, of which only the other
  is accepted by the check of facts, gives every function the meaning on valid inputs of the
  function of the other with its header, the callers of a replaced function included, and its
  functions are safe and keep validity (`Defs.functionsFollow_sound`); the protocols of the two
  programs are not compared, and nothing is said of them. This is the family of relations "the
  same meaning", stated for functions as equality of what they return; the other families
  (guards compared by segment, representations, reductions) are not built;
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
  (`Defs.fnTable_stops_undefined`, `Meaning/Stops.lean`); a function that follows the analysis
  of a safe function is assured and means the same (`functionsSame`, which is
  `TypedFn.follows_assured`); a step of transformation from an assured function relates functions
  with the same meaning (`transformSound`, which is `AssuredFn.step_same`), and every function of
  a program whose functions follow those of a program that the check of facts accepts means what
  the function of the other with its header means, and the second's functions are safe and keep
  validity (`replacedFunctionsSame`, which is `Defs.functionsFollow_sound`).

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
- for transformations, only the family "the same meaning" is built, for functions, as a step
  from an assured function (`AssuredFn.step`). Not built: a transformation as a record of its
  contract, its relation and its evidence; the other families of relations (guards compared by
  segment, representations, reductions); facts carried from one program to another by a
  correspondence of their places; summaries decided at calls and assumed of callees (`Callees`
  asks safety and validity of every callee, not a summary); a guard whose condition is
  already known true dropped or added on either side (every guard of the second term must be the
  skeleton's next entry); a loop or a choice that only computes and that nothing uses dropped,
  and two loops fused (every form of control stays in the skeleton); the comparison of the
  protocols of two programs;
- the index of a definition (bindings, uses, captures of a region, summaries, each query with
  its lemma) and the facts that the analysis knows at a place, as one thing that a
  transformation and a proof can ask: of the index only `Term.reads` is built, and the analysis
  keeps what it knows to itself;
- single assignment is decided for every admitted function and no theorem uses it yet: the
  value form reads names through a scoped context of identifiers. It is, for now, a contract of
  the stored form and of the untrusted transformations.

`Process/`, `Program/`, `Meaning/` and `Projection/`, and the data of `Admission/`, are what
the projection theorem and the meanings stand on; `Evidence/`, `Value/` and the analysis of
`Facts/` are built for any dialect, with the instance of the function dialect in
`Facts/Local.lean` and `Facts/LocalLaws.lean`; `Transform/` is built for functions. `World/`,
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
  says with the whole refusal, except one that the table accepts since it places the operands of
  a sum in one order, named for what it shows (`facts-commutativity-recovered`: a fact on
  `i + 1` holds of `1 + i`, as it does of a new name bound to `1 + i`); for each operation with a domain and for a restricted row, an
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
  choice), and that the operands of a conjunction are learned in the order written: `e && t`
  accepted and `t && e` refused, where `e` gives a number that `t` needs, and that an equality
  learned false teaches the same in either order of its operands; what case analyses, choices,
  blocks, payloads and carried sums give of a natural;
  the ranges of each arithmetic operation and conversion; code that does not run after an
  operation or a loop whose results have no value; the place of a refusal and of a bound inside
  a block, and the order of the bounds; and which types have no value;
- `Following.lean`: whether a function follows the analysis of another, on pairs of functions
  written by names, elaborated, the first analysed and the second following its analysis, with
  whether the second differs nowhere (`decided`) and the whole verdict, no place that differs and
  no refusal (`safelyFollows`): a repeated computation shared, computations reordered between
  guards or moved around them with the guards in their order, a computation moved out of a loop,
  other names for the values, a call of a function that cannot stop shared, `x + y` against
  `y + x`, `x == y` against `y == x` of naturals and of truth values, and a product and a sum with
  their operands exchanged in a loop after a guard, each accepted; `x - y` against `y - x`,
  `(x + y) + z` against `x + (y + z)` (following does not know associativity), a row of the
  vocabulary with its operands exchanged, `e && t` against `t && e` (a conjunction keeps the order
  written), guards in the other order, a guard dropped, a call of a function that can stop moved
  across a guard, two loops against one (following does not fuse loops), and another key on a
  guard, each refused; each instruction kept in order, accepted: a choice, a case analysis, a
  block, a loop as often as a value says and a call of a function that can stop, each with other
  names, a value moved out of and into a region of a choice, and a value moved across a call of a
  function that can stop; pairs that differ in one thing, each refused by the comparison of that
  thing: a guard's condition or reason, a choice's condition, the subject of a case analysis, a
  loop's initial values or count, a block's number or key, and the operand, the callee or the key
  of a call of a function that can stop; the theorem for functions applied to two pairs accepted
  whole, `x + y` and `y + x` the second; and, on the walk of the analysis over a toy dialect, an
  attempt followed by the same attempt with other names, accepted, and by one with another key,
  which differs at the attempt, and the two controls on the definitions of the value form: two
  terms that follow one skeleton whose leaf is not made above the values in scope, with no place
  that differs, and do not mean the same (why following asks for `Skel.Fresh`), and an attempt
  whose end cannot return followed by what stops `undefined`, whose term runs the skeleton that
  the walk builds (why what follows an attempt runs only from an end that can return);
- `Transform.lean`: transformations of functions as steps from an assured function: a function
  with unused and repeated operations, in its body and in a loop, admitted (`admitFn`), a step to
  what `removeUnused` gives and a step from the result to what `shareRepeated` gives of it, each
  stored result compared whole, each step accepted, and the chain composed by
  `AssuredFn.step_then`, its middle function never admitted again; the two passes on a function
  with a choice, a case analysis and a block, with unused and repeated operations inside and
  around them, each result compared whole and each step accepted, the second from the result of
  the first; one admitted function whose loop runs as often as a value with an upper end, and one
  step from it, with the bounds of both, `checkFacts_sound`, the safety and the bounds that an
  assured function carries, `TypedFn.safe_iff_assured`, `admitFn_erases`, `AssuredFn.step_erases`
  and `AssuredFn.step_both` applied to them; a target refused by elaboration; three targets that
  read a value with a domain before what justifies it (an inverse moved above the guard that it
  is not zero, read before a choice in whose region it was justified, read before a loop in whose
  body a guard justified it), which follow their source with no place that differs and which the
  analysis refuses while it follows, so that the step refuses each with the target's refusal, and
  the control that, in the field of two elements written there, the first of these targets stops
  `undefined` on the input zero where the source stops at its guard; a target refused while it
  follows that also differs, refused with both; a target that differs from its source (two guards
  exchanged), refused with the place where it differs; a source that the check of facts refuses,
  which `admitFn` refuses with its whole refusal, so that no step can be asked of it; a target
  that computes another result, refused where it returns; a target with the operands of a sum
  exchanged, accepted; three functions as the passes treat them, each with its whole verdict: two
  linear values that `shareRepeated` shares, which the step refuses by the rule `linear`, `a + b`
  then `b + a`, which `shareRepeated` leaves as they are and whose sharing written by hand is
  accepted, and an unused restricted subtraction after the guard that justifies it, which
  `removeUnused` drops, accepted; a program of two functions whose callee is replaced by what
  `removeUnused` gives, which follows the first, with `Defs.functionsFollow_sound` applied, from
  the first program's acceptance alone, to the caller and to the safety and validity of the
  second program's functions; and a callee replaced by one that computes another result, which
  does not follow and whose meaning on a concrete input is another. The decision of equality of
  stored functions is written there;
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

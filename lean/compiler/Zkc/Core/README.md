# Core

The zkc compiler uses one typed term for functions, protocols and individual role programs. A
term returns its outputs or executes one instruction and continues with its results in scope.
The core defines its meaning as a process, the projection of a protocol to the programs of its roles
with the theorem that every role program is a projection of its protocol, the elaboration of a
program of functions and protocols by names with its
erased form and the round trip in both directions, what elaboration decides about a body,
places in a term and replacement, the evidence that a statement about what a program does is
made with (claims in a scope, being assured, facts at a place, the relation "same meaning",
summaries of definitions, and what is known of the subject of an instruction, a contract or a
witness, of which the rule of a call is the instance at a call), the analysis of a term for any
dialect (a walk that checks a body and builds its skeleton, with comparison of two such skeletons), of a body under a summary of its definition, with its soundness, the summary of a function
in its header, over no written operation, whose requirements the analysis decides at a call and
whose guarantees it learns there, the judgments about a function (that it satisfies its summary,
the same meaning on the inputs that satisfy its requirements) with the two decisions that produce
them, a transformation of a function as a step from an assured function that follows its analysis
with the target and never admits the source again, the data of an admitted program and of a
deployed scheme, the run of a role under the handlers of its deployment, and the types of the
functions that are still to be built with the statements that they must satisfy. It is the library
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
and by the root, with two exceptions, each a module that makes data with its proof:
`Transform/Assured.lean` imports `StepSound`, whose theorems the assured functions that it makes
carry, and `Admission/Admit.lean` imports `Programs`, whose theorem the admitted programs that it
makes carry. Across the directories, the rule of layers separates the modules for any dialect
from those about one dialect or about the vocabulary: a module for any dialect imports, directly
or through other modules, no module about one dialect or about the vocabulary. The audit lists the generic modules explicitly in
`coreGeneric`. They include the shared expression table, range and knowledge domains, assertion
typing, body traversal, skeleton comparison and their proofs. Its concrete roots include the
vocabulary and the dialect implementations. Each generic module's entire import closure is checked
against those roots.

| Directory | Holds |
|---|---|
| `Process/` | processes (well-founded trees of effects), the one property on every path (`Process.Every`) and its rules (iteration among them, with an invariant asked of every step or only of the steps below a count), handlers, their composition, and the retry of an attempt; the base relation, two processes that mean the same along every path of permitted replies, an equivalence and a congruence for what a process is built with, which a handler whose replies are permitted keeps, retry included, and a value that a process can return on some path of permitted replies with its rules (`Same`) |
| `Program/` | keys, labels, occurrences, sites, places, stops and names, a name being a number that a definition binds at one place (`Identity`); the position of an item in a list (`Member`, by which a call names a definition among the headers) and lists of values of types (`HList`), which are about no vocabulary (`Lists`); types, the vocabulary, whose keys say everything that tells a nominal type, a row or a law from another, with the law that the domain row of a restricted row decides it, which types have no value, and its models (`Vocabulary`); contexts of names, a finite map from names to types behind a small interface, the names of a binding, variables (a name with the proof that the context has it at its type) and environments of names, with their lemmas, among them what an environment with one more name bound gives at that name and at another, the structural rule on contexts (a context within another) and environments that agree at some names (`Context`); lemmas about lists and `Except` that the proofs use (`Library`); terms, whose bindings carry the names that they bind, their addresses, whether their case analyses without an arm give nothing, and that every name of a definition is bound at one place (`Term.BoundOnce`) (`Term`); items placed by the low bits of a natural, the keyed collection of the decisions of distinct addresses and of single assignment and of what the check of facts knows (`BitTree`); the decisions of distinct addresses and of single assignment, with what failed and the place of a name bound a second time, each proved to decide its proposition (`Conditions`); linear use, defined by its decision, which says which value, by its name, is not used as it must be and where (`Linear`); located types and role maps (`Located`); the record of a run (`Record`); the kinds of events and the shape of a protocol (`Shape`); the three dialects, the header of a function with its summary, over no written operation, and headers of which no function's summary has a requirement (`Headers.Unconditional`) (`Dialects`); projection, the translation of a protocol's term to a role's (`Project`); a typed program, its definitions with the names of their inputs and what elaboration decided about each body (of a function, that the positions that the summary of its header names are in range), one definition elaborated against the headers before it and a program extended by it, and the lookup of a definition, as a typed reference, and of a protocol, by its key, with the definitions that a definition reaches (`Ref.closure`) (`Typed`); the program by names, for any operations and any performers, with the decision of equality of its instructions and regions, by which stored programs are compared whole (`Syntax`); refusals: the rules of the core, what a rule found and the place where it found it, as data, for any types and written operations (`Refusal`); the operations of the three dialects by names, the program by names of them that a frontend gives, a function with its summary over no written operation, and a refusal of such a program (`ProgramRefusal`) (`NamedProgram`); the elaboration of a region over the rules of a dialect, each refusal made at its place, with the equality of types that elaboration and following share (`TypeEquality`) (`Elaborate`); erasure, the program by names of a typed term, and its round trip in both directions over lawful and canonical rules (`Erase`); the written form of each operation of a function and its resolution, with both halves of the law of written forms, and the rules of the local dialect (`LocalRules`); the elaboration of a function, which refuses by the rule `summary`, at the definition, a summary of its header that names a position beyond its inputs, and for a guarantee beyond its inputs and results, its erased form and their round trip in both directions (`ElaborateLocal`); the erased form of a typed program (`EraseProgram`); what an operation with a domain asks of an application, as data, and the values that it names, the items of a list at positions (`atPositions`), by which an operand names the operands of a written operation, the ranges of naturals with what it is for a natural to be in one, and the summary of a definition, a list of requirements on its inputs and a list of guarantees on its inputs followed by its results (`Summary`), the summary with neither (`Summary.empty`), the summary of a function, a summary over no written operation (`Summary Empty`), which names inputs and results by their positions only by construction and which an analysis reads as a summary over the written operations of its dialect (`Summary.lift`), and the decision that the positions that such a summary names are in range (`Summary.misplaced`, `Summary.InRange`) (`Requirement`); a term in a wider context, with the same erased form, a term with one place left open and the term that fills it, a term split after its first instructions, and the names that a term reads (`Place`); instruction prefixes, composition and splitting (`Stepped`) |
| `Meaning/` | events and what a role holds (`Events`); the fold of a term over the semantics of a dialect, which binds the names of each binding to its values, a value with its type and the values of a list with their types (`Semantics.Dyn`, `Semantics.dyns`) with their lemmas, the payload of a variant that satisfies a predicate (`Pick.All`), and a loop, which holds what it collects latest first and reverses it once where it becomes one value (`Fold`); what a requirement says of values: how a value reads (`Reading`), the values that the operands of a requirement name, and that it holds (`Requirement.Holds`), an order, a bound, a number or a difference saying that its values read as naturals, the language in which an operation states its domain and a definition its summary, what it is for a definition to satisfy a summary (`Summary.Holds`), and that a requirement or a summary over no written operation, read with no relation of written operations (`Empty.elim`), holds exactly when, read over the written operations of a dialect (`Summary.lift`), it holds with any relation (`Requirement.holds_lift`, `Summary.holds_lift`) (`Requirement`); the semantics of a function, of a protocol and of a role program (`Local`, `Protocol`, `Role`), with the meaning of every operation that the core owns (`Local`); the validity of values for any dialect: values valid with their types are those valid in the form `HList.All` (`Semantics.dyns_valid_iff`, the one conversion between the form of the statements about any dialect and that of the statements about functions), the values of the variables in scope, and what a loop collects (`CollectedOK`, `collected_valid`) (`ValidValues`); what it is for the functions of a table to keep validity and never stop `undefined`, how a requirement reads a value of a function (`localReading`), the relation of its written operations (`LocalReturns`), that the requirements of a header's summary hold of inputs (`FnHeader.Required`), that every function of a table satisfies the summary of its header (`FnTable.SatisfiesSummaries`), each summary read with no written operation, and so the same against any callees (`Summary.holds_tables`), the callees that a statement about a function is made against (`Callees`), that functions that satisfy summaries of which none has a requirement never stop `undefined` on valid inputs (`FnTable.safe_of_unconditional`), that every local operation keeps validity, that a type with a valid value has a value, and what a valid value of a function is (`ValidDyn`) (`Validity`); that a term of a function returns valid values on valid values in scope against callees that keep validity, and means the same against two tables of callees that agree on valid inputs (`Tables`); the meanings of a whole program (`Program`); that a function whose header says that it cannot stop stops only `undefined` (`Stops`); places with their meaning: a term in a wider context means the same, what it is for a run to reach a place and a fact at a place, replacement, and that a term's meaning depends only on the names that it reads (`Place`); the meaning of a prefix, in continuation-passing form and as a process of the environment that it ends in (`Prefix.denote`, `Prefix.run`, `Prefix.denote_fill_run`) (`Stepped`) |
| `Projection/` | the relation of a role's process to a protocol's and its lemmas (`Proj`), the proof for one term (`Sound`), and the theorem for every definition of a program (`Theorem`) |
| `Evidence/` | what every statement about what a program does is made with, for any dialect and interpretation except the rule of a call, which is for functions, with nothing of an analysis: the starts of a term that a statement is about (`Entry`), claims on every authorized start and permitted reply (`Claim`), claims under a handler, whose returns and stops carry the observer's state (`Claim.Under`), and what it is for a term to be assured in a scope: never stopping undefined and returning valid values (`Assured`) (`Claim`); facts at a place (`Fact`), the relation "same meaning" in a scope (`Equivalent`), which composes and along which claims and being assured move (`Equivalent.claim`, `Equivalent.trans`, `Assured.transfer`), replacement under a fact (`replace_with_fact`), and laws with a premise applied where the premise is a fact (`ConditionalLaw`) (`Relation`); that the summary with no requirement and no guarantee is being assured: a definition satisfies it (`Summary.Holds`, `Meaning/Requirement.lean`) exactly when it is assured as a function of its inputs (`Summary.holds_empty`) (`Summary`); the subject of an instruction, what it runs before its continuation, a process as a function of the path and the environment (`Subject`): of an application, the operation on its operands (`Subject.op`), of a block, its body under the block's frame (`Subject.block`), the meaning of each being its subject then its continuation (`Term.op_subject`, `Term.block_subject`), and what is known of a subject in two strengths, a contract (`Subject.Satisfies`) and a witness, that it returns exactly what a function of the environment gives (`Subject.Yields`), with one rule for the continuation each (`Subject.Satisfies.then`, `Subject.Yields.then`), on terms (`Term.op_satisfies`, `Term.op_yields`, `Term.block_yields`), a witness as a contract (`Subject.Yields.satisfies`), a law lifted through witnesses (`Subject.Yields.same`, and on terms `Term.equivalent_of_yields`), and what is known of a block's body known of the block along "same meaning" of the body under the block's frame (`Subject.block_transfers`, `Subject.block_yields_transfers`) (`Subject`); for the function dialect, the contract and the law of a function at its entry in a table (`Contract`, `Law`), each knowledge of the subject of every call of it (`Contract.satisfies`, `Law.yields`), the rule of a call as the rule of an instruction at a call (`Contract.call`, `Law.call`), and a summary of a function that holds of its entry as its contract (`localSummary_contract`), so knowledge of every call of it (`localSummary_satisfies`) (`Call`); for the term in steps, the subject of every instruction (`Instr.subject`), a step being its subject then the rest, with the two rules for the rest (`Term.step_satisfies`, `Term.step_yields`), and a property on every path of a step (`Term.every_step`), of each kind of instruction in terms of its condition and its regions, a loop by an invariant over its iterations (`Instr.every_loop`), and of a prefix filled with a term (`Prefix.every_fill`) (`Stepped`). It imports nothing of `Value/` or `Facts/` |
| `Value/` | Expression identifiers, applications and selections, table lookup and semantic readings (`Expressions`). |
| `Facts/` | `Range` and `Local` supply arithmetic and the local operation catalog. `Knowledge/` stores and proves facts about the values in the expression table. `Domains/` specifies dialect and domain laws. `Contracts/` checks assertions and supplies function and role instances. `Body/` walks stepped bodies, builds and compares skeletons, records refusals and loop bounds, and proves the public verdicts. `Loops`, `SteppedLoops` and `Facts` relate the bounds to program execution. |
| `Transform/` | functions, the judgments about them, and transformations of functions, on the analysis of `Facts/`: a function elaborated against the headers before it (`TypedFn`, `typeFn`), its meaning on inputs against callees, what it is for it to be safe (to satisfy its header's summary), to have its loops bounded, to be assured with bounds, and for two of them to mean the same, as propositions against every `Callees`, on the inputs that satisfy the requirements of its header's summary, the check of facts of a function and whether a second follows the analysis of a first, each under its header's summary, as decisions, and why a step is refused (`StepRefusal`) (`Step`); the two producers of assurance, the check of facts (`TypedFn.check_assured`) and following a function that is safe by any route (`TypedFn.follows_assured`), "the same meaning" symmetric and transitive, and that a function is safe exactly when its body is assured in the sense of `Evidence/` on the inputs that satisfy its requirements and returns what satisfies its guarantees (`StepSound`); an assured function, made only with its assurance, by admission (`admitFn`, the one path by which admission's check of a definition and transformations admit a function) or by a step from an assured function (`AssuredFn.step`), which never admits its source again, and the theorems of a step (`Assured`); two untrusted transformations of a stored function, which drop the operations whose results are not used and share repeated operations, accepted only through the step (`Passes`). The operations of a function that commute, each placed in the table with its two operands in one order, are the sum and the product of naturals and the equality of naturals and of truth values (`ownedContract`, `Facts/Local.lean`); the conjunction and the disjunction of truth values, whose meaning is symmetric too, keep the order written, since the check of facts learns their operands in that order |
| `Admission/` | Named function and protocol elaboration, both round trips, and association resolution. The incremental checker and whole-program admission use the same function or projected-role checks. `Projections` collects each declared role's bounds. `CheckedTables` composes callee guarantees in declaration order, including calls at external roles. `Programs` proves loop bounds for all functions and role processes and validates function replacements. `Theorems` connects these results to the core statements. |
| `World/` | the description of a layer (a handler of a role), whose code reads its inputs by position, in the one context of the core that binds inputs to the names `0, 1, 2, …` (`Ctx.positional`), and its meaning as a handler; the network of the roles, and the runs of a protocol and of one role alone |
| `Scheme/` | the declaration of a scheme, who proves and who verifies, a deployed scheme, whose entry is the protocol that its declaration names, found in its program, and the run of a role under its handlers, and what deployment decides about scopes and keys |
| `Run/` | how a run of the executor ends, the executor, and the prover's and the verifier's runs |
| `Format/` | formats of values and the codecs of a model |

`Functions.lean` and `Statements.lean` come after every directory: they may import any of them.

## What is proved, what is defined, what is still to be built

Proved, with no axiom beyond `propext` and `Quot.sound` (the audit checks every declaration):

- the projection theorem (`Zkc.Core.projection`, `Projection/Theorem.lean`): the program of
  every role of every protocol of a typed program, run on what the role holds of one input, is
  a projection of the protocol's process; where the protocol returns, the role returns what it
  holds of the results;
- a returning send preserves its sender's local payload. A receiving role gets its own
  typed value. `UnaryMeasurements.lawful` supports a measurement whenever its interpretation
  respects the preserved subject. A guard and a dynamic loop both register numeric comparisons
  through `Knowledge.rememberComparison_sound`. This lets the sender index the original
  array using the loop bound on the sent array, including when the range starts above zero.
- the rules of proof on every path (`Process.every_bind`, `every_mono`, `every_iterate`,
  `every_iterate_below`), and the rules of an instruction (`Evidence/Subject.lean`): every
  instruction that binds results is its subject, then its continuation (`Term.op_subject`,
  `Term.block_subject`), and what is known of a subject, of an application of an operation, a
  call or a block alike, has one rule for the continuation: a subject that satisfies a contract,
  followed by a continuation correct on every result that the contract promises, is correct
  (`Subject.Satisfies.then`, `Term.op_satisfies`), and a subject that yields a function, followed
  by a continuation, is the continuation on what the function gives (`Subject.Yields.then`,
  `Term.op_yields`, `Term.block_yields`); a witness is a contract with no stop
  (`Subject.Yields.satisfies`); two subjects that yield functions which agree on the authorized
  starts are the same process there, so two instructions with them and the same continuation
  mean the same (`Subject.Yields.same`, `Term.equivalent_of_yields`); and what is known of a
  block's body is known of the block, along "same meaning" of the body under the block's frame
  (`Subject.block_transfers`, `Subject.block_yields_transfers`). The rule of a call
  (`Contract.call`, `Law.call`, `Evidence/Call.lean`), a contract or a law of a function, a
  property of its entry in a table, installed at an actual call with the operands and the
  continuation taken from the term, is their instance: a contract and a law of a function are
  knowledge of the subject of every call of it (`Contract.satisfies`, `Law.yields`);
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
  form of every typed program elaborates as the program, and a program that
  elaboration gives erases to the program by names that was elaborated
  (`elaborateProgram_erase`, `erase_elab`, `Admission/Elaboration.lean`);
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
- `Term.denote_step` runs the instruction and binds its results for the continuation.
  `Prefix.denote_fill_run` composes a prefix with the rest of a term. The rules
  `Term.step_satisfies` and `Term.step_yields` apply contracts and witnesses to that same
  instruction process. `Term.everyLoop_step` covers nested instructions and the continuation
  on permitted returns. `BodyAnalysis.prefixFact` gives the analysis invariant at the hole
  reached after an accepted prefix.
- For any dialect, `BodyAnalysis.checkFacts_safe` gives loop bounds, safety, valid results and the
  stated guarantees on valid inputs satisfying the requirements. Its hypotheses include lawful
  rules and assertion typing, distinct addresses, and evidence for reached annotations.
  Operation requirements are checked on shared and ordered operations alike. A refused obligation
  carries its place, clause index, assertion, cause and the operand ranges supplied by the dialect.
- `BodyAnalysis.followChecked` checks each definition in its own context. Both walks allocate
  their own leaves while sharing the expression table. The checker compares their skeletons and
  reports the candidate's refusals and places that differ, or its bounds in traversal order.
  `follows_checked_assured` relates the candidate to an independently safe source. The public
  function theorems specialize these judgments to a model and callees satisfying their contracts.
- `FunctionContracts.lawful` discharges the operation laws from the concrete local semantics.
  `Facts/LocalLaws.lean` proves the operand range, return and domain facts used by those laws,
  including `localCall_holds`, `ownedOp_defined`, `ownedOp_yields` and `row_yields`.
  The comparison of printed typed operations uses `Rules.skel_lawful` and the elaborator's laws.
  Every accepted function satisfies its summary and keeps validity. Its loop bounds use the
  places with no role. Each protocol's bounds use the actual projected role under every
  invocation path. Together these give `typed_program_sound` and `Typed.Assured`
  (`Admission/Programs.lean`). The callees of a
  function, the functions before it, stop only `undefined` where their headers say that they
  cannot stop with no check of facts (`Defs.fnTable_stops_undefined`, `Meaning/Stops.lean`), keep
  validity with no check of facts (`Term.denote_valid`), and satisfy their summaries against the
  whole table as against the functions before them, since a summary of a function applies no
  written operation (`Summary.holds_tables`); read over the written operations of a dialect, it
  holds whatever the relation of written operations it is read with (`Summary.holds_lift`);
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
  (`localSummary_contract`, `Evidence/Call.lean`), so it is knowledge of every call of the
  function (`localSummary_satisfies`);
- the judgments about a function and transformations as steps from an assured function
  (`Transform/StepSound.lean`, `Transform/Assured.lean`, `Meaning/Tables.lean`,
  `Admission/Programs.lean`): each is said on the valid inputs that satisfy the requirements of
  the function's header's summary. A function that the check of facts accepts under its header's
  summary carries safety and bounds against `Callees` (`TypedFn.check_assured`). A successful
  comparison with an independently safe function gives the candidate's assurance and equality
  of meaning on those inputs (`TypedFn.follows_assured`). A function is safe exactly
  when its body is assured, in the sense of `Evidence/`, in the scope of the empty path and its
  inputs bound to valid values that satisfy its requirements, and on each such input every return
  satisfies its guarantees (`TypedFn.safe_iff_assured`); "the same meaning" of functions is
  symmetric and transitive (`TypedFn.SameAs.symm`, `TypedFn.SameAs.trans`). An assured function
  (`AssuredFn`) is made only with its assurance: by admission (`admitFn`), which the check of a
  definition of a program uses too, or by a step from an assured function (`AssuredFn.step`),
  which never admits its source again. A step relates
  functions with the same meaning (`AssuredFn.step_same`); two steps compose with no condition
  on the middle function (`AssuredFn.step_then`); two steps from one function give functions
  with the same meaning (`AssuredFn.step_both`); and the stored form of what admission and a step
  return is what they were given (`admitFn_erases`, `AssuredFn.step_erases`). On valid values in scope, a term of a function returns valid values
  against callees that keep validity (`Term.denote_valid`), and means the same against two tables
  of callees that agree on valid inputs when one keeps validity (`Term.denote_tables`); so a
  program whose functions follow those of another over the same headers, of which no summary has a
  requirement and only the other is accepted by the check of facts, gives every function the
  meaning on valid inputs of the function of the other with its header, the callers of a replaced function included, and its
  functions are safe and keep validity (`Defs.functionsFollow_sound`); the protocols of the two
  programs are not compared, and nothing is said of them. This is the family of relations "the
  same meaning", stated for functions as equality of what they return; the other families
  (guards compared by segment, representations, reductions) are not built;
- the proved statements of `Statements.lean` (`Admission/Theorems.lean`): each theorem
  has the statement as its type: for every record of functions whose `admit`, `check` and
  `elaborate`, those that the statement reads, are the definitions `admit`, `check` and
  `elaborateProgram`, and for every admitted program. A program that elaboration gives erases
  to the program by names that was elaborated (`eraseOfElaborated`), and the erased form of a
  typed program elaborates as the program, including protocols
  (`roundTrip`). What `admit` returns is the elaboration of what was given, with the association
  resolved in it (`admitsWhatWasGiven`); `check`, one definition at a time from no headers, gives
  the headers of the admitted program (`checkAgrees`). An admitted program carries that it is
  assured with its annotation (`Admitted.assured`), which `admit` gives it from the theorem of the
  check of facts for a program, that every function satisfies its summary; so of every admitted
  program, however it was made, a function never stops `undefined` on valid inputs that satisfy
  its requirements (`functionsSafe`), returns valid values on every valid input
  (`functionsKeepValidity`), the program respects its annotation (`annotationHolds`), and a
  function whose header says that it cannot stop does not stop on such inputs
  (`headersSayWhoStops`), since such a function stops only `undefined`
  (`Defs.fnTable_stops_undefined`, `Meaning/Stops.lean`); a function that follows the analysis
  of a safe function is assured and means the same (`functionsSame`, which is
  `TypedFn.follows_assured`); a step of transformation from an assured function relates functions
  with the same meaning (`transformSound`, which is `AssuredFn.step_same`), and, over headers of
  which no summary has a requirement, every function of a program whose functions follow those of
  a program that the check of facts accepts means what the function of the other with its header
  means, and the second's functions are safe and keep
  validity (`replacedFunctionsSame`, which is `Defs.functionsFollow_sound`). An execution of the
  network is replayed from its record: a step with a given record has one successor under any
  source (`Step.unique`), so two executions from one configuration with one record end in one
  configuration (`replayed`, which is `Reach.unique`, `World/Network.lean`).

Defined: everything else, from the terms and their meanings to deployment, the network and
the runs.

Still to be built:

- `elaborateProgram`, `admit` and `check` implement the entries of `Functions` for mixed programs.
  The open entries are `eraseRole`, `format`, `deploy`, `identity`, `execute` and `schedule`;
- `rolesSafe` holds for every admitted open role on valid inputs and permitted replies.
  Its projection establishes the requirements of each function it calls.
  Remaining statements include `realized`, `anyOrder`, `recordsAreValid`,
  `schedulerRuns`, deployment from `deployKeeps` to `identityReads`, `executorRuns` and `formats`.
  A partial external source can leave the network quiescent while a role waits for a draw.
  The current scheduler contract then requires a report other than `limit`, but its `blocked`
  report recognizes only a missing message. This case needs a progress premise or a reporting rule.
- for transformations, only the family "the same meaning" is built, for functions, as a step
  from an assured function (`AssuredFn.step`). Not built: a transformation as a record of its
  contract, its relation and its evidence; the other families of relations (guards compared by
  segment, representations, reductions); facts carried from one program to another by a
  correspondence of their places; the comparison of two programs whose functions have
  requirements (`Defs.functionsFollow_sound` asks that no summary has one: its general form needs
  that the requirements hold at every call that a run reaches); deployment for programs whose
  functions have requirements (`deployedSafe` still assumes unconditional headers);
  deciding, where a definition returns, a guarantee that names an application of a
  written operation (it is refused there: the analysis does not know that the application has a
  value); a guard whose condition is
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
  elaboration decides about each, and meanings that compute; a deployed scheme whose admitted
  program is built by hand with the proof that it is
  assured, every loop respecting an annotation that bounds none; it gives the other tests `var`, the
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
  `row` (over the standard vocabulary, `Tests/Vocabulary/Core.lean`), `association`
  (`Admission.lean`) and `summary` (`Summaries.lean`), and each condition of a body, a program by names that is accepted and one
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
- `Facts.lean`: the check of facts on functions written by names, typed (`typeFn`) and checked
  (`TypedFn.check`): the conformance cases of the
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
  written by names with one header, typed (`typeFn`), the second following the analysis of the
  first (`TypedFn.follows`), with whether the second differs nowhere (`decided`) and the whole
  verdict, no place that differs and no refusal (`safelyFollows`): a repeated computation shared, computations reordered between
  guards or moved around them with the guards in their order, a computation moved out of a loop,
  other names for the values, a call of a function that cannot stop shared, `x + y` against
  `y + x`, `x == y` against `y == x` of naturals and of truth values, and a product and a sum with
  their operands exchanged in a loop after a guard, each accepted; `x - y` against `y - x`,
  `(x + y) + z` against `x + (y + z)` (following does not know associativity), a row of the
  vocabulary with its operands exchanged, `e && t` against `t && e` (a conjunction keeps the order
  written), guards in the other order, one of two guards dropped, a call of a function that can stop moved
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
  which differs at the attempt. Comparison distinguishes returning an input from returning
  a fresh reply to the same question, and the two terms give different answers. An attempt
  whose settlement cannot return runs its actual skeleton. The failing continuation alone cannot
  run the return skeleton;
- `Transform.lean`: transformations of functions as steps from an assured function: a function
  with unused and repeated operations, in its body and in a loop, admitted (`admitFn`), a step to
  what `removeUnused` gives and a step from the result to what `shareRepeated` gives of it, each
  stored result compared whole, each step accepted, and the chain composed by
  `AssuredFn.step_then`, its middle function never admitted again; the two passes on a function
  with a choice, a case analysis and a block, with unused and repeated operations inside and
  around them, each result compared whole and each step accepted, the second from the result of
  the first; one admitted function whose loop runs as often as a value with an upper end, and one
  step from it, with the bounds of both, `TypedFn.check_assured`, the safety and the bounds that an
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
  the first program's acceptance and that no summary of its headers has a requirement, to the
  caller and to the safety and validity of the second program's functions; and a callee replaced by one that computes another result, which
  does not follow and whose meaning on a concrete input is another;
- `Domain.lean`: the domain of an operation kept in order, what an operation kept in order
  guarantees, and a body under a summary, on a dialect written there with a natural and a positive
  natural and four operations, each kept in order: the decrement, from either type to a natural,
  which stops `undefined` on zero and otherwise asks the world one question and returns its operand
  less one, and whose written form requires its operand to be at least one; the half of a natural,
  which asks one question and returns the half of its operand, and whose written form guarantees
  that its result is at most its operand; the opaque half, which computes the same and guarantees
  nothing; and the subtraction, which stops `undefined` when its second operand is larger than the
  first and whose written form requires it to be at most the first: its rules lawful for its
  semantics, with every law and for every permitted reply (`domainRules_lawful`); the decrement
  applied to a positive input accepted by the check of facts, with `BodyAnalysis.checkFacts_safe` applied
  to give that it never stops `undefined`; applied to a natural input, refused at the operation
  with the requirement that is not justified and what was known of the operand; the control that
  on the input zero the term on naturals is the stop `undefined`, and on a positive input the
  question followed by the return; the term on positive naturals with other names, which follows
  the first and is accepted; the decrement applied to a natural input under the summary that
  requires the input to be at least one, accepted, with `Summary.Holds` for it from
  `BodyAnalysis.checkFacts_safe`, and the control that the input zero is excluded by the summary's
  requirement; a body that returns its input under a summary that guarantees the result to be at
  least one, accepted when the summary also requires the input to be at least one and refused at
  the definition's exit by the rule `guarantee` when it does not; and the subtraction of the half of
  the input from the input, accepted, since what the half guarantees is learned where it returns,
  and with the opaque half refused at the subtraction, each with the whole verdict;
- `Summaries.lean`: summaries of functions, on functions written by names over the vocabulary
  with a field of `Facts.lean`, each with its whole verdict: a function that divides by its second
  input, admitted under the summary that requires that input to be at least one and refused at the
  division under the empty summary; a caller that guards that its divisor is at least one and calls
  it, admitted, and one that calls it on inputs of which nothing is known, refused at the call with
  the callee's requirement, and the same call of the function with the empty summary admitted; a
  decrement after a guard whose summary guarantees that its result is at most its input, admitted,
  and refused at its exit by the rule `guarantee` under a guarantee that its body does not
  establish; a caller that subtracts the decrement's result from its input, admitted, the
  guarantee learned where the call returns, and refused at the subtraction when the guarantee is
  removed from the callee's summary; `Summary.Holds` for the dividing function in every model,
  from what admission carries and from `TypedFn.check_assured`, and the control in the field of two
  elements of `Transform.lean`: on the divisor zero, which the summary's requirement excludes, the
  function's process is the stop `undefined`, and on the divisor one it returns the quotient; a step
  from the dividing function admitted with an unused product to what `removeUnused` gives,
  accepted, with `AssuredFn.step_same` applied; summaries that elaboration refuses by the rule
  `summary` at the definition (a requirement on the result's position, a guarantee on a position
  beyond the inputs and the result), and one whose guarantee names the result, elaborated (a
  requirement on an application of a written operation cannot be written: a summary is over no
  written operation); and the round trip of a program of a function with a summary and its caller
  in both directions, the summary in the header that elaboration gives;
- `Subjects.lean`: what is known of a computation, said of the subject of the instruction that
  runs it, on the vocabulary with a field of `Facts.lean`: one function, the sum of two products
  `a * b + c * d` of naturals, presented three ways in a caller of four inputs, as typed terms
  written with `var`: a callee whose body computes it, called by the caller (its body is the callee
  by names, which the check of facts accepts); a block in the caller whose body is the same
  instructions; and the instructions in line. For each, a witness, in every model, that the subject
  yields the function: the call by the law of the callee (`Law.yields`), the block by its body, and
  the last instruction in line, the sum, on the starts that the two products before it give, each
  body known from the operations that the core owns (`ownedOp_yields`) and the rule of an
  instruction (`Term.op_yields`). One law of the function, proved once as mathematics, that
  exchanging the two products gives the same number, and from it, for each presentation, by the
  same lemma (`Term.equivalent_of_yields`), that the caller means the same as the caller with the
  two products exchanged (the call's operands, the operands that the block's body reads, the last
  instruction's operands). The controls: the call of the sum of two products and the call of a
  callee that returns the first product only both satisfy "the result is at least zero", and the
  second yields no witness of the sum of two products (a contract is not a witness); and a callee
  that stops at a guard on some valid input, whose call satisfies the contract that it returns the
  sum of two products with that stop allowed, and does not yield it;
- `Stepped.lean` checks splitting and filling prefixes on the function bodies of `Subjects.lean`,
  and exact erasure of the elaborated choice inside a loop in `N-TY9e`. It proves the meaning
  of the sum of two products from the instruction equations, including the process of the first
  two steps as a prefix. A loop that runs twice satisfies a bound of two and violates a bound
  of one.
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
  one whose key is no definition, refused by the rule `association`; a protocol refused. The headers
are compared whole, by the kernel.

In `lean/compiler`, `lake build` builds the core, the vocabulary, their tests and the audit;
`lake test` builds the tests of the core (the library is the test driver), which need those of
the vocabulary; and `lake exe zkc-audit` audits the core, the vocabulary and their tests: no
axiom beyond `propext` and `Quot.sound` in any declaration, the replay of every declaration
through the kernel, and four rules on imports (a module of the core imports only the core,
`Init` and `Std`; no module of the core imports a module of the tests or of the tools; the root
imports every module of the core; and the rule of layers: no module for any dialect, as the
audit lists them (`coreGeneric`, `Tools/Audit.lean`), imports, directly or through other modules,
a module about one dialect or about the vocabulary (`coreConcrete`), and no module is in both
lists). The audit does not check the
order of the directories or the rule on modules of proofs.

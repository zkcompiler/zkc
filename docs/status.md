# Status

## Active Core build

The compiler admits named functions and protocols in definition order. On valid inputs satisfying
a function's declared requirements, admission proves its summary and recorded bounds. Protocol
admission checks each role's projected body. The public role-safety theorem excludes an
undefined stop for valid inputs and permitted replies, including calls with checked preconditions.
See the [Core guide](../lean/compiler/Zkc/Core/README.md) and the
[active build targets](development.md).

## Interactive source proofs on typed Core

The frontend emits the protocol into typed Core. Admission checks the program,
and projection gives the process for each role. The formal theorems describe the admitted
entry or its selected reduction call. The source clients check that the typed call and its
emitted attachment select the same operands and function instance. For the table extension
and GKR summand they also check the formal symbol named by that instance's `external` declaration.
Interpreting the symbol in the mathematical model is a separate obligation. The tests exercise
this source path with trusted elaboration and lowering.

| Entry checked | Result and assumptions |
|---|---|
| Sumcheck verifier | A false sum is accepted with probability at most `n/S` for `n` rounds and a challenge set of size `S`, under the arithmetic and reached-challenge laws. The written-charge client also derives the VCVio bound over an answering uniform service from the closed rational ceiling and all emitted draw addresses at 0, 1 and 10 rounds. It checks the deciding role, public operands, sum relation and source table extension. Each executed member may use the verified barycentric or affine interpolation. |
| Honest joint Sumcheck | A valid table of length `2ⁿ` with its true sum returns successfully for every reply under the table and arithmetic laws. Full reply mass at reached calls gives return probability one. |
| GKR layer verifier | At the four-round `Reduce<Gate>` call, a false incoming claim yields a correct residual with probability at most `8/S`, under the gate, reached-challenge and polynomial laws for those four rounds. The issued component binds the source summand, admitted call, gate primitive and four degree-two challenges. Its VCVio bound assumes an interpretation of that summand and the gate and restriction laws. Whole-circuit soundness also needs the wiring, line reduction, layer composition and terminal evaluation. |

Run `just test-interactive` for the source checks, their mutation controls and the
kernel audit. The [formal package guide](../lean/formal/README.md) gives the
theorem entry points and the [source checks](../lean/formal/checks/SourceProtocols.lean)
exercise the certificates.

## Judgment with fees

Written soundness issuance records each resolved goal and its deciding clause in the package of its scheme. The source record carries the scheme's qualified path and defining file module. This distinguishes an imported scheme from a nested scheme with the same path, even when both deploy the same protocol with the same roles. The issuer selects goals from that compilation and shares a decision when both its source position and its instantiated function agree. A kernel-checked lookup ties each goal to one row. The source comparison reads the operands from the original clause and checks that the lookup and the numerical fields refer to the selected goal. What a goal publishes, its named views and the facts of its table of caps are declared by commands of the formal library over the typed subject; the issuer writes a data module without a proposition, and a challenge, a views module and a fees module that are each one command. [Compiler issuer](../lean/compiler/Zkc/Frontend/Written/Subject.lean) · [Independent consumer](../lean/formal/ZkcFormalTests/WrittenSource.lean)

The `zkc-check written-goals` command issues each requested written soundness goal independently. It preserves an issued goal when a sibling fails selection, admission, model coverage or statement generation. Aliases share a target, and any refused required goal makes the command exit unsuccessfully. Each successful result identifies its admitted package and challenge. A `requires` whose absence from the soundness experiment cannot be established receives an SX7 diagnostic. Proof acceptance requires the subsequent comparator judgment. See the [frontend guide](../lean/compiler/Zkc/Frontend/README.md#issuing-written-soundness-goals).

A process is judged within a budget when, at every effect, a fee chosen before the reply pays for the replies excluded there and every other permitted reply is judged within what is left. The budget is a nonnegative rational. Under the fees of samplers, a fee pays for a set of replies whose probability under the sampler of the effect is at most the fee. One theorem takes the judgment to VCVio's probability for any signature: a process judged within a budget not to return badly returns badly with probability at most the budget, under every service with a state that answers only permitted replies and draws as the samplers do. The run against a service is VCVio's simulation: a process is a computation that asks the oracles of its effects, a service is a handler of their queries with a state and a possible failure, every such handler is the handler of a service, and the run is `simulateQ` of the one by the other (`ZkcFormal.OracleProcess`). A result about a compiled program is stated about that simulation. Draws are VCVio's uniform sampler of the type drawn. A test on one uniform draw of a field of five elements meets the hypotheses with a service that answers, reaches the bound of one fifth, for the run and for the simulation, and shows that no budget below one fifth judges the process.

A fee can also be held to what its effect is allowed: under the fees within allowances, a fee is paid by the sampler of the effect and is at most the allowance of that effect. A written charge gives the allowance. In a run of the definition that owns it, it allows each effect at one of its draws its ceiling and every other effect nothing; in a run of another definition it allows nothing. Its draws together are allowed its budget, which as a probability is the total that the earlier endpoints state. The allowance is of the event at an address: the role that owns a draw and a role that hears it are allowed the same, and which of them can pay is said by the samplers. The occurrence of a draw is defined where no loop with a count read at run time, no application and no attempt stands around the instruction.

The form of a stored program is its computation written out: the queries of its effects, the monad's bind, `for` and `if`, the reading of a called definition, and the values of the program at their own types. The formal library states what the computation of a stored definition is by one recursion on the stored syntax, proves once that it is the reading of the definition's meaning, and a command writes the computation out for a definition, with the equation as one application of that theorem, which the kernel checks (`ZkcFormal.Form`). `publish_forms` declares and registers the forms of every definition in a written subject's reach. A form is checked, before the kernel sees it, to be type-correct as a tactic compares types (without unfolding a definition that is not reducible): the type of what a role has of a value, the vocabulary of a package and the header of a definition are reducible for that, the state of a loop and the results of a call are read by their places, and a numeral is written as Lean's elaborator writes one. A value that is no variable is named once in a form by a `let`, so a value that the program uses twice is written once. `lean/formal/checks/ProgramForms.lean` publishes the forms of eleven sources (a loop with a carried value and one that collects, a choice, a stepped loop, applications of protocols that call functions, a callee with two callers, a callee whose roles are bound in another order, one that is passed a value that both roles hold, a chain of values each used twice, a draw of a vector with functions over matrices, a count over a sequence) and refuses two controls; `checks/FormProof.lean` proves two goals on registered forms. The walk does not read a choice among the alternatives of a variant or an attempt yet, and refuses each by name.

The Count check reads both tolerances and their caps from the source, changes the comparison in the relation and compares the deployed definitions and tables. It also checks that a goal is issued at its ceiling, below the total of its charges too (a goal whose bound is one or more, and a goal on a verifier with a coin that the prover does not hear, are refused; a goal with a ceiling is issued without a table of caps where its root reaches what a table has no place for yet: a charge on an application or an attempt; a charge on a site of an applied protocol; a charged draw, or any application, under a loop whose count is read at run time or in an attempt; a goal without a ceiling is refused there, though the language gives such charges a total. For a goal without a ceiling the challenge's command decides by the kernel that the counts of the goal's table are those of the stored program and that the table adds up to the bound; the caps, the set of charged draws and whether the source writes the bound are the issuer's reading of the source, compared with the source by the checks only), and that rows whose reach the standard interpretation does not cover get views and no step to the published result. The other four charge subjects exercise repeated draws, applications, choices and the field-order charge of Freivalds.

A goal publishes two theorems, stated by the formal library from the goal's row: the result (coverage, and the bound for every admitted program at the goal's bound) and the receipt (a served model and a rejected input). A goal is issued at its bound, the ceiling that it writes or else the total of its charges; the fee facts of a row are declared where the table's budget is within the bound.

The proofs of the views check, of the fees check (a draw followed for free, and a fee paid within its cap), of Operands and RenumberedOperands, the always-true relation's two endpoints and the Honest fixture have comparator challenges. The charge subjects check their source data.


## Printed packages

The frontend prints an admitted package as a Lean module that holds the program by names and nothing computed from it. In the module the kernel elaborates each definition against the headers of those before it; the typed definition is the kernel's normal form of what the elaboration returns, with the equation between the two, and the typed program is those definitions in order. The header of each definition is marked reducible, so that a tactic reads the types of a definition's inputs and results from it. The program of any admission of the program by names is then that typed program. The frontend's own elaboration is not read by the module, so a module cannot hold a typed program that differs from what the Core elaborates. The printer has a case for every constructor of the program by names and reads no source identifier. The module imports the Core's admission theorems, the vocabulary of a package and the kernel command, and nothing of the frontend.

The command that asks the kernel to compute (`kernel_ok` of `Zkc.Kernel`) is meta code outside the audited libraries. Each definition and each equation it adds is checked by the kernel like any other; Lean's unifier is not asked to compute. A normal form takes the parameters and the indices of a constructor from the expected type and not from the computation that produced the term, a proof is stated at the proposition of its field, and a numeral is written as Lean's elaborator writes one (`OfNat.ofNat` at a literal), since a tactic that matches terms as they are written tells the two apart.

A module holds one printed form of a program, so the kernel cannot find a wrong print that still elaborates. `just test-packages` covers that in two ways: the program and the association that Lean read from each module are compared, by value, with those that the frontend gave to admission; and a fixture is printed, read by Lean and compared with the fixture by value. A check computes, from the types of the fixture, every constructor that a program by names, an association and the rows of a project can hold, with the keys of the standard vocabulary and the parameters of a project primitive, and fails when the fixture lacks one; a constructor added later makes `just test-packages` fail until the fixture holds it. The comparison is by constructor, not by field, and numbers and strings are not counted. The fixture is data for the printer and is not elaborated.

`just test-packages` prints every admitted root of eight examples: Schnorr, Chaum–Pedersen, Sumcheck with two rounds and with ten (sixty-five definitions), a client that applies the reduction of Sumcheck twice with two representations of a round, GKR with its fifteen project primitives, the inner-product argument, a protocol over variants and the fragments. Lean checks each of the sixteen modules, and four controls are refused: a call of a definition that the program does not have, which the kernel command refuses as an elaboration error; a key changed in a definition, which elaborates and which only the comparison with the source refuses; the comparison with the program of another source; and an association with a claim that the package was not printed with, which admits and which only the comparison of the association refuses. The packages of this check are printed with no association of a scheme.

## Written three-message knowledge

The source-issued Schnorr and Chaum–Pedersen knowledge theorem covers the admitted verifier, extractor and relation. The extractor takes a sized sequence of nominal run records for the selected closed protocol. Source-level checks cover the owning contract, explicit roles and available statement fields. Both protocols use the same exact returning-trace characterization, row interpretation laws and group-action proof. An independent companion can prove the Core target directly. Finite-model controls falsify it after deleting a verifier guard or changing a selected function. Oracle names and opening operands survive resolution; full source oracle elaboration is pending. Run `just test-written-knowledge` and `just test-interactive`. See the [proof and model boundaries](written-knowledge.md).

Resolved goals and contracts retain declaration identity and named statement arguments. Ordinary resolution enforces unique contract ownership. The compiler checks its property catalog against the language and library references. A per-use environment closes specification-only numerals independently of the deployed callee. Two uses of `Count<8>` share an admitted verifier and close the declared charge to `3/8` and `3/4` respectively. The emitted returning-record equality compares ordered keys and nominal types. A named `special_soundness` goal at `written` selects a scheme and its knowledge clause. A `soundness` goal at `written` reads the `proves` or `reduces` clause that it names by `clause = label`, or the only one of the contract (GL3): the clause is given as the source wrote it, with its kind, label, deciding role, the relation it applies and the operands in the order of the relation's parameters, and its deciding role is the verifier of the scheme. A label that no clause has, or that a clause of another kind has, refuses the goal. GL3 refuses a goal that names none of several clauses, and a goal on a protocol without a clause of the kind. That is enforced where a claim is formed, not where a goal is read: such a goal still reads the charge at a site, which states no claim, because a caller without a contract reads the charges of its callees through its goal. Extra scheme context remains in the public statement. The independent consumers supply their own role inputs, function arguments and observed addresses. The formal arithmetic model constructs the group interfaces from a Mathlib field action. A separate process interpretation uses VCVio for challenge probabilities. Run `just test-formal` to build and audit the public package.

## Source conformance

For each concrete module instance the frontend records the applied interface that declares each
member. Signature elaboration, member-body checking and row emission read that binding.
Function calls on a concrete receiver check the selected member’s own static bounds
and `where` conditions after resolving the static arguments, for both bodies and primitive rows.
The default search chooses the first fully formed module that satisfies the required applications.
It evaluates interface conditions with access to the members each predicate reads through `Self`.
Eligibility checked with a provisional receiver produces a judgment. The frontend discards
its direct and indirect query results even when the predicates hold. It forms the real module
and checks its conditions before committing their dependencies. Stable instance numbers,
diagnostics, budget consumption and observations of project primitives survive the eligibility check.
A module reached only through a member selection can stay unformed and receive none of the
checks of SP8, including when a signature uses its type or natural, a literal constructs its
record or enum, a call uses its own `pub def` or its protocol member, a clause uses its
relation, or a `use` imports its function.
A bound that no module can satisfy is not diagnosed where it is written.
In the opaque typing of an application at a fresh type, the first of two applications
that declare the member gives its signature.
Before a module is given, a member name that two interfaces of a bound declare resolves to
the first, so the order of the bound can change the verdict.

`just test-frontend` exercises parsing and formatting across the reference corpus, compares
assembly and name resolution with the expected rules, takes every reference case through the typing of the program and fixes the counts of the outcomes, and checks generated views at closed
protocol instances. It also checks that guarded indexing survives a send at its sender,
requires local evidence at the receiver, and reports the role missing a bound at a shared
binding. The admission controls emit and check their positive roots. Resolution checks the statement/witness split of a top-level relation in
`proves`, `reduces` and `through`, the form of knowledge branches, named algorithms and loop references.
Where a `proves` clause or the source of a `reduces` clause applies a relation, the application is typed at the instance of the protocol as an application in an expression is: the static arguments of the relation are inferred from the operand types, a `where` on its head holds at the instance, the operands have the types of its parameters, and its body is typed. Where a goal or an application gives values to specification-only parameters, the `where` is checked at those values and the body of the relation is typed at them, so an index or a size that is a proof argument is checked against the value of each use. A relation or a specification function that a specification item calls is reached at the values of its own specification-only parameters, which it shares with the caller or is given in a specification argument; a call that leaves one out is refused (SP11). A definition generic over a module parameter waits where one place of its text is typed more than once and stands for different functions at an instance: members of two modules, as in a loop whose receiver goes from a value of one module's type member to a value of another's, or a member in one typing and a function of the type's own module in another. The typing at the instance reads one resolution for a place, and before this such a program was admitted and called one function for all (39 written out, 99 as a loop). `just test-formal` runs thirteen such programs, which wait, and nineteen written-out forms and places with one member, which mean what the source says (`ZkcFormalTests.MemberResolution`): dot calls and an operator, functions and a protocol, and module parameters among naturals and under a section. Not changed: a `where` that equates a type member with itself (`where X::T == X::T`) makes the member count as equated with a type, so an operator on a value of it is the function of the type's own module and not the member of the interface. A clause runs nowhere, so an operand or a body of a relation that waits for a later layer of the language leaves the clause untyped and the protocol unaffected; an operand that waits is met before the instance of the relation, so the `where` is then not checked, at a goal either. No clause of the examples is left so: each is typed with its body. The short application of a relation with witness parameters, at the top of a `proves` clause or of the source of a `reduces` clause, is typed on its statement operands (SX3); before this it was refused there.

What written soundness goals of one scheme claim is read as one package (`Written.goalClaims`): the definitions of the scheme's protocol first, with the keys and the stored definitions of its own package, then the relation of each goal's clause at the goal's proof values, instantiated in one state so that each has a key of its own; the operands at the statement and at the witness are inputs of the deployed header, given by their places there. `checks/GoalClaim.lean` compares the stored definitions, and Lean's kernel accepts that the processes of the root's roles in that package are those of the deployed package.

The formal library also accepts an explicit bound at a package's selected decision. A Lean author can prove that return bound directly or derive it from a fee judgment and an inequality on its total. Coverage and the existence of a valid rejected input with a served model have separate statements. The source issuer publishes soundness at the goal's bound (`Soundness.Result` at the bound's limit); a judgment by fees is one way to prove it. [Formal interface](../lean/formal/ZkcFormal/Written/Soundness.lean)

The contract of a protocol generic over a module parameter is typed in both typings of SP12, as its body is: a clause reads of a type member what the interface declares, calls the members that a body may call, and the instance keeps the resolutions for the typing at a goal. A specification argument of an application that reads the index of a loop that is one loop for every iteration is refused (SP11); in a loop typed per iteration each application gives its own value. A sum of naturals over a static range is written term by term where its index is an operand of arithmetic in the term, which is TY8's condition, and is one loop where the index is read as a position or in a condition; before this every sum whose term named the index was written term by term, so that the count of a relation over a table of `n` entries was `n` blocks. No deployed function of an example changes. An operand that is no port is not read yet, and a claim whose relation links a primitive that no deployed definition links is not compared with the deployed package. Not typed yet: the relation of a `knowledge` clause, what a clause states under the results or under the index of a loop, a formula that applies no relation, and `requires`. Typing the full contract at each instance remains open. The
[language and frontend review](source-elaboration.md) describes the proposed boundary.

The frontend driver checks locations in the reference tables, compares emitted programs across
formatting, and runs independent conformance cases.

A specification function, relation or instantiated law can wait for the checked form of a
specification. The rational sum in `bound` and the quotient in `fragments::birthday` wait
because the frontend cannot decide body facts across these operations. A reachable signature
with a rational or a formal library type such as `MvPoly` can also leave a root waiting, as
in `sumcheck::PartialSum` and the laws of `Round`. Indexing a sequence inside a rational
quotient waits both with and without a bounds guard, and so does every other fact of such a
body: an index beyond a fixed length, or any fact of a natural body behind a signature with a
formal type. The local typing fixtures and the Layer A reference suite compare every waiting or
typed-only report with its expected instance or counted family, class and reason. This includes
reports beside an admitted or refused root. A waiting or typed-only report that is missing or
unexpected fails either suite; an admitted report that goes missing is not compared here.
A required source refusal can be deferred only for its recorded block and rule. Only core
admission counts as an admission. A function bound to a vocabulary row has no package report.
The example and library suites report waits separately. Selected library modules also require
admitted default instances of their public functions with bodies.

Selecting a member of an applied module checks its interface conditions, applicable member
bodies and laws. Concrete associated types are checked against their declared sorts. Protocol heads
are checked even when a sibling member is the only one used. An open head equality that the
checker cannot decide leaves that use waiting. Ordinary checking counts declarations reached
through those checks before choosing public defaults. Written issuance checks the modules
used by each selected goal in its protocol, proof arguments, clause, charges and ceiling. See the [frontend guide](../lean/compiler/Zkc/Frontend/README.md#checking-selected-module-members).

The function member `pair` of the catalogue's BLS12-381 module is the standard row
`pairing.pair`. A module instance
stores the row name of each function member. Calls use the member's interface for its mode,
static arguments and operands. A concrete call checks the selected row against that signature.
In a generic definition the opaque pass uses the interface alone.

Participant programs have no concrete executor and standard runtime model in this compiler.
The historical commands to run, prove, verify and read trees have been removed. Derived
construction awaits the constructed stage on the library's protocol objects. Written scheme
selection checks the deployed roles (SC3) and checks that the statement operands of a written
claim come from inputs held by both prover and verifier (SC4). The scheme-wide SC4 requirement
to mark a verifier-only input private currently has no checker. The construction-time check of draws
(SC5) awaits that stage too.

## Earlier source and execution pipeline

Use [the previous Lean compiler at `10ed903fc`](https://github.com/zkcompiler/zkc/tree/10ed903fc22d3f20b22ff2d1bbf607a740ef0718) for the historical execution commands, scheme construction and formal examples. The table records coverage at that revision.
The current default targets build the core, vocabulary, subject library, core and vocabulary tests, and audit.
The earlier receipt suite is preserved with its original Core API in the [historical package](../lean/historical-formal/README.md).

| Area | Coverage at `10ed903fc` |
|---|---|
| Source language | `.zkc` source of the frozen layer, and the scheme declarations that derive a proof by Fiat–Shamir with the canonical layout. A root that uses a form of a later layer waits, with the form it waits for |
| Admission | elaboration of a package of the core language, its types, the check of facts (an admitted program never stops `undefined`) and the check of copies |
| Construction and projection | the Fiat–Shamir and serialize steps that construct a non-interactive scheme; projection of a protocol to one program per role |
| Execution | role programs run by the total executor of the core, in Lean. Rows of G2, Gt, the pairing and the hashes other than SHA-256 have no arithmetic in it and do not run |
| Proofs | statements and proofs over the meaning of the core: the completeness of the Schnorr scheme of `examples/schnorr_example.zkc` in the model that runs, under named hypotheses about the curve; an invariant of ten rounds of `Sumcheck<Fr, 10>` in the model of any arithmetic (when the claims are the sum of the table, the verifier's ten checks pass). No statement of soundness, knowledge or zero knowledge |
| Native execution | not supported |
| WASM and EVM targets | not supported |
| Oracles and commitments, STARK, constraint systems and the other forms beyond the frozen layer | not supported; being rebuilt on this structure |

The earlier implementation, a C++ compiler with a Rust runtime, is at the tag
`old-route-2026-11-14`.

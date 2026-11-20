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

A process is judged within a budget when, at every effect, a fee chosen before the reply pays for the replies excluded there and every other permitted reply is judged within what is left. The budget is a nonnegative rational. Under the fees of samplers, a fee pays for a set of replies whose probability under the sampler of the effect is at most the fee. One theorem takes the judgment to VCVio's probability for any signature: a process judged within a budget not to return badly returns badly with probability at most the budget, under every service with a state that answers only permitted replies and draws as the samplers do. A test on one uniform draw of a field of five elements meets the hypotheses with a service that answers, reaches the bound of one fifth, and shows that no budget below one fifth judges the process. The judgment has no admitted program as a subject yet.

## Printed packages

The frontend prints an admitted package as a Lean module that holds the program by names and nothing computed from it. In the module the kernel elaborates each definition against the headers of those before it; the typed definition is the kernel's normal form of what the elaboration returns, with the equation between the two, and the typed program is those definitions in order. The program of any admission of the program by names is then that typed program. The frontend's own elaboration is not read by the module, so a module cannot hold a typed program that differs from what the Core elaborates. The printer has a case for every constructor of the program by names and reads no source identifier. The module imports the compiler package only.

The command that asks the kernel to compute (`kernel_ok` of `Zkc.Kernel`) is meta code outside the audited libraries. Each definition and each equation it adds is checked by the kernel like any other; Lean's unifier is not asked to compute. A normal form takes the parameters and the indices of a constructor from the expected type and not from the computation that produced the term, and a proof is stated at the proposition of its field.

A module holds one printed form of a program, so the kernel cannot find a wrong print that still elaborates. `just test-packages` covers that in two ways: the program and the association that Lean read from each module are compared, by value, with those that the frontend gave to admission; and a fixture is printed, read by Lean and compared with the fixture by value. A check computes, from the types of the fixture, every constructor that a program by names, an association and the rows of a project can hold, with the keys of the standard vocabulary and the parameters of a project primitive, and fails when the fixture lacks one; a constructor added later makes `just test-packages` fail until the fixture holds it. The comparison is by constructor, not by field, and numbers and strings are not counted. The fixture is data for the printer and is not elaborated.

`just test-packages` prints every admitted root of seven examples: Schnorr, Chaum–Pedersen, Sumcheck with two rounds and with ten (sixty-five definitions), GKR with its fifteen project primitives, the inner-product argument, a protocol over variants and the fragments. Lean checks each of the fifteen modules, and four controls are refused: a call of a definition that the program does not have, which the kernel command refuses as an elaboration error; a key changed in a definition, which elaborates and which only the comparison with the source refuses; the comparison with the program of another source; and an association with a claim that the package was not printed with, which admits and which only the comparison of the association refuses. The packages of this check are printed with no association of a scheme.

## Written three-message knowledge

The source-issued Schnorr and Chaum–Pedersen knowledge theorem covers the admitted verifier, extractor and relation. The extractor takes a sized sequence of nominal run records for the selected closed protocol. Source-level checks cover the owning contract, explicit roles and available statement fields. Both protocols use the same exact returning-trace characterization, row interpretation laws and group-action proof. An independent companion can prove the Core target directly. Finite-model controls falsify it after deleting a verifier guard or changing a selected function. Oracle names and opening operands survive resolution; full source oracle elaboration is pending. Run `just test-written-knowledge` and `just test-interactive`. See the [proof and model boundaries](written-knowledge.md).

Resolved goals and contracts retain declaration identity and named statement arguments. Ordinary resolution enforces unique contract ownership. The compiler checks its property catalog against the language and library references. A per-use environment closes specification-only numerals independently of the deployed callee. Two uses of `Count<8>` share an admitted verifier and close the declared charge to `3/8` and `3/4` respectively. The emitted returning-record equality compares ordered keys and nominal types. A named `special_soundness` goal at `written` selects a scheme and its knowledge clause. Extra scheme context remains in the public statement. The independent consumers supply their own role inputs, function arguments and observed addresses. The formal arithmetic model constructs the group interfaces from a Mathlib field action. A separate process interpretation uses VCVio for challenge probabilities. Run `just test-formal` to build and audit the public package.

## Source conformance

`just test-frontend` exercises parsing and formatting across the reference corpus, compares
assembly and name resolution with the expected rules, takes every reference case through the typing of the program and fixes the counts of the outcomes, and checks generated views at closed
protocol instances. It also checks that guarded indexing survives a send at its sender,
requires local evidence at the receiver, and reports the role missing a bound at a shared
binding. Positive cases emit a root and pass Core admission. Resolution checks the statement/witness split of a top-level relation in
`proves`, `reduces` and `through`, the form of knowledge branches, named algorithms and loop references.
Where a `proves` clause or the source of a `reduces` clause applies a relation, the application is typed at the instance of the protocol as an application in an expression is: the static arguments of the relation are inferred from the operand types, a `where` on its head holds at the instance, the operands have the types of its parameters, and its body is typed. Where a goal or an application gives values to specification-only parameters, the `where` is checked at those values. A clause runs nowhere, so an operand or a body of a relation that waits for a later layer of the language leaves the clause untyped and the protocol unaffected; an operand that waits is met before the instance of the relation, so the `where` is then not checked, at a goal either. No clause of the examples is left so: each is typed with its body. Not typed yet: the relation of a `knowledge` clause, what a clause states under the results or under the index of a loop, a formula that applies no relation, and `requires`; and a soundness goal does not check that the deciding role of the clause is the verifier of its scheme. Typing the full contract at each instance remains open. The
[language and frontend review](source-elaboration.md) describes the proposed boundary.

## Earlier source and execution pipeline

Use [the previous Lean compiler at `10ed903fc`](https://github.com/zkcompiler/zkc/tree/10ed903fc22d3f20b22ff2d1bbf607a740ef0718) for the working `.zkc` frontend,
`zkc-check`, scheme construction and formal examples. The table records coverage at that revision.
The current default targets build the redesigned Core, vocabulary, their tests and audit.
The full frontend CLI is still being migrated. The earlier receipt suite is preserved with its original Core API in the [historical package](../lean/historical-formal/README.md).

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

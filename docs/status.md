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
| Sumcheck verifier | A false sum is accepted with probability at most `n/S` for `n` rounds and a challenge set of size `S`, under the arithmetic and reached-challenge laws. The written-charge client also derives the VCVio bound over an answering uniform service from the closed rational ceiling and all emitted draw addresses at 0, 1 and 10 rounds. It checks the deciding role, public operands, sum relation and source table extension. Each executed member supplies its law at the remaining depth. The shifted pair example uses two distinct representations, and exchanging its callees fails certification. A written soundness goal can request a ceiling on the accumulated charge. |
| Honest joint Sumcheck | A valid table of length `2ⁿ` with its true sum returns successfully for every reply under the table and arithmetic laws. Full reply mass at reached calls gives return probability one. |
| GKR layer verifier | At the four-round `Reduce<Gate>` call, a false incoming claim yields a correct residual with probability at most `8/S`, under the gate, reached-challenge and polynomial laws for those four rounds. The issued component binds the source summand, admitted call, gate primitive and four degree-two challenges. Its VCVio bound assumes an interpretation of that summand and the gate and restriction laws. Whole-circuit soundness also needs the wiring, line reduction, layer composition and terminal evaluation. |
| Written table spot-check | Under the ideal registration and opening service, at most 768 matching rows among 1,024 give return probability at most `(3/4)^40` for the selected verifier. Its 40 indices are uniform, independent and sampled with replacement. The model supplies the equations for the admitted evaluation and comparison operations. |
| Constructed Schnorr verifier | The selected scheme installs ordered Merlin absorption and challenge handlers. The regression executes the admitted guard, checks all 64 challenge bytes, and exercises stateful cache hits. The experiment takes the deployment identity, encodings, message policy and query law as inputs. Security against a querying adversary requires a separate reduction. |

Run `just test-interactive` for process and constructed-verifier checks, and `just test-written-charge` for source issuance, independent quantitative consumers, mutation controls and kernel replay. The [formal package guide](../lean/formal/README.md) gives the
theorem entry points and the [source checks](../lean/formal/checks/SourceProtocols.lean)
exercise the certificates.

## Written three-message knowledge

The source-issued Schnorr and Chaum–Pedersen knowledge theorem covers the admitted verifier, extractor and relation. The extractor takes a sized sequence of nominal run records for the selected closed protocol. Source-level checks cover the owning contract, explicit roles and available statement fields. Both protocols use the same exact returning-trace characterization, row interpretation laws and group-action proof. A companion can import the checked definition closure and prove the target for a helper-factored verifier, extractor or relation. The Schnorr regression discharges the target for a helper-factored extractor. Finite-model controls falsify it after deleting a verifier guard or changing a selected function. Run `just test-written-knowledge` and `just test-interactive`. See the [proof and model boundaries](written-knowledge.md).

Resolved goals and contracts retain declaration identity and named statement arguments. Ordinary resolution enforces unique contract ownership. The compiler checks its property catalog against the language and library references. A per-use environment closes specification-only numerals independently of the deployed callee. Two uses of `Count<8>` share an admitted verifier and close the declared charge to `3/8` and `3/4` respectively. The emitted returning-record equality compares ordered keys and nominal types. A named `special_soundness` goal at `written` selects a scheme and its knowledge clause. Extra scheme context remains in the public statement. The independent consumers supply their own role inputs, function arguments and observed addresses. The formal arithmetic model constructs the group interfaces from a Mathlib field action. A separate process interpretation uses VCVio for challenge probabilities. Run `just test-formal` to build and audit the public package.

## Source conformance

`just test-frontend` exercises parsing and formatting across the reference corpus, compares
assembly and name resolution with the expected rules, and checks generated views at closed
protocol instances. It also checks that guarded indexing survives a send at its sender,
requires local evidence at the receiver, and reports the role missing a bound at a shared
binding. Positive cases emit a root and pass Core admission. Resolution checks the statement/witness split of a top-level relation in
`proves`, `reduces` and `through`, the form of knowledge branches, named algorithms and loop references.
Typing the full contract at each instance remains open. The
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

# Status

## Active Core build

The compiler admits named functions and protocols in definition order. On valid inputs satisfying
a function's declared requirements, admission proves its summary and recorded bounds. Protocol
admission checks each role's projected body. The public role-safety theorem excludes an
undefined stop for valid inputs and permitted replies under unconditional function headers.
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
| Sumcheck verifier | A false sum is accepted with probability at most `n/S` for `n` rounds and a challenge set of size `S`, under the arithmetic and reached-challenge laws. The source checks instantiate 0, 1 and 10 rounds. |
| Honest joint Sumcheck | A valid table of length `2ⁿ` with its true sum returns successfully for every reply under the table and arithmetic laws. Full reply mass at reached calls gives return probability one. |
| GKR layer verifier | At the four-round `Reduce<Gate>` call, a false incoming claim yields a correct residual with probability at most `8/S`, under the gate, current-layer and challenge assumptions. Whole-circuit soundness also needs the wiring, line reduction, layer composition and terminal evaluation. |

Run `just test-interactive` for the source checks, their mutation controls and the
kernel audit. The [formal package guide](../lean/formal/README.md) gives the
theorem entry points and the [source checks](../lean/formal/checks/SourceProtocols.lean)
exercise the certificates.

## Written three-message knowledge

The source-issued Schnorr and Chaum–Pedersen knowledge theorem covers the admitted verifier, extractor and relation. Both protocols use the same exact returning-trace characterization, row interpretation laws and group-action proof. An independent companion can prove the Core target directly. Finite-model controls falsify it after deleting a verifier guard or changing a selected function. Oracle names and opening operands survive resolution; full source oracle elaboration is pending. Run `just test-written-knowledge` and `just test-interactive`. See the [proof and model boundaries](written-knowledge.md).

## Earlier source and execution pipeline

Use [the previous Lean compiler at `10ed903fc`](https://github.com/zkcompiler/zkc/tree/10ed903fc22d3f20b22ff2d1bbf607a740ef0718) for the working `.zkc` frontend,
`zkc-check`, scheme construction and formal examples. The table records coverage at that revision.
The current default targets build the redesigned Core, vocabulary, their tests and audit.
The full frontend CLI and historical formal receipt suite still await migration.

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

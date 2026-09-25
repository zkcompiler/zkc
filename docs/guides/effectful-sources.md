# Effectful sources, selection and installed inputs

This guide applies the normative [local Sumcheck source](../spec/profiles/sumcheck/local-prover.md#local-prover-state-and-code)
and [captured/service sources](../spec/profiles/README.md#service-components)
and [domain values](../spec/domains/values.md). They own the constructor equations
and requirements. The profiles share execution laws while retaining explicit
frontend and probability interpretations.

## 1. Local finite code

[Local code and cuts](../spec/profiles/sumcheck/local-prover.md#local-prover-state-and-code)
explain which state is retained and why local abort is returned data.
The maintained [source](../../formal/Zkc/Protocols/Sumcheck/LocalProver/Source.lean)
elaborates this code into common execution and proves conformance, a public
coin bound and retained inputs. Register writes and branch decisions appear
in local history, whose public visibility depends on the enclosing observer.

The optional [ArkLib interpretation](../../formal/integrations/arklib/ZkcArkLib/LocalProver/Source.lean)
adds `execution_exact` against its probabilistic interpreter and `normalized`
for both kinds of cut. Those are additional laws with an optional import
closure. The field cast of a local sample does not replace its retained
natural outcome; injectivity is a separate premise where needed.

## 2. Checked source selection

[Literal issuance](../spec/profiles/services/affine.md#literal-selection-and-issuance)
uses the root [selection module](../../formal/Zkc/Protocols/CapturedPrograms/Selection.lean).
Its conservative whole-tree check includes dormant leaves and guards. The
result retains the actual selected code and values. A code generator reading
hidden data before selecting the tree is outside the fixed-tree agreement law.

The optional [input law](../../formal/integrations/arklib/ZkcArkLib/CapturedPrograms/Inputs.lean)
proves fallback independence through the actual probabilistic interpreter.
The root issuer already establishes the input bounds consumed by that law.
This separates source admission from the choice of probability semantics.

## 3. Installed namespace interpretation

[Installed environments](../spec/profiles/services/affine.md#installed-source-environment)
connect declarations to the actual installed world. The root
[adapter](../../formal/Zkc/Protocols/CapturedPrograms/Inputs.lean) proves
`installed_environment` and `install_admission_exact`, while
[installation](../../formal/Zkc/Protocols/CapturedPrograms/Installation.lean)
connects the captured setup to the service controller and finite mass law.

The optional [probability adapter](../../formal/integrations/arklib/ZkcArkLib/CapturedPrograms/Installation.lean)
adds the installed source's fallback and experiment laws. A native namespace
label still needs authority and lifetime interpretation; it cannot replace
the actual installation/capture correspondence.

## 4. Rounds as supplied endpoints

[Scalar rounds](../spec/profiles/sumcheck/scalar-rounds.md#supplied-early-round-adapter)
keep message selection before challenge delivery. The maintained
[early-source theorem](../../formal/Zkc/Protocols/AlgebraicRounds/EarlySource.lean)
preserves the complete result, endpoint state and ordered events. It returns
a residual scalar, whose enclosing protocol must supply its terminal meaning.

The [table-bound Sumcheck entry](../spec/profiles/sumcheck/interactive.md#checked-evaluation-and-table-bound-entry)
provides that full connection for the selected table-expression profile.
Its [Formal implementation](../../formal/Zkc/Protocols/Sumcheck/TableSource.lean)
uses the original table cells, variable order and factor multiplicity before
running the checked verifier. Its exact-run theorem includes incomplete tapes;
its security theorem uses the declared independent uniform finite-field tape.

## 5. Services, partial delivery and scheduling

[Partial services](../spec/profiles/services/affine.md#requests-delivery-and-history)
and [scheduled sessions](../spec/profiles/services/commitment-sessions.md#finite-commitment-session-machine)
have different return/stop boundaries. Their root implementations are
[issued service execution](../../formal/Zkc/Protocols/CapturedPrograms/Execution.lean)
and [session execution](../../formal/Zkc/Protocols/CommitmentSessions/Source.lean).
The former preserves delivered history when its provider stops; the latter
returns session failures so a scheduler can continue another action.

A native scheduler must preserve the declared atomic action or prove its new
interleaving relation. Several lower-level emissions are not automatically
several permitted controller observations. Shared provider/preparation state
also requires its actual framing and distribution laws.

## 6. Theory application and limits

Structural source laws, explicit effects and whole-tree dependency analysis
supply the reusable connections. [Theory](../theory.md) records their broader
context; the [table-expression rationale](../rationale/table-expression-meaning.md)
explains the ordered-table bridge and its alternatives. The
[correspondence map](../spec/correspondence/domains.md) distinguishes
root laws, optional probability results and remaining native adapter obligations.

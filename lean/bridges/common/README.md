# Derived Common scalar clients

Common clients use `protocol-structured`, the strict Structured serializer and
Lean's phased unit admission. `Common.Import`, `Common.Format`, the flat Common
program AST, its Python program/proof renderer, `common-source`, and the native
`protocol-lean` export are retired. There is no compatibility reader.

`Common.Vocabulary` and `Common.Scalar` retain mathematical scalar vocabulary.
The checked `Structured.CommonAdapter` projects actual typed participant actions
to the interfaces of the existing mathematical Schnorr, quadratic Sumcheck and
factor-opening contracts. It is a derived observation, not source admission.
Projection refuses the additional Structured message sorts.

The maintained exports are the actual Schnorr library protocol, the two-round
unrolled quadratic Sumcheck fixture, their helper/arithmetic variants, and the
factor-opening fixtures. Positive variants retain their completeness,
Schnorr special-soundness and Sumcheck property consumers. Early challenge,
wrong residual and wrong opening point remain admitted counterexamples to those
specific contracts; they cannot borrow a positive certificate.

## Regeneration and checks

Build `structured-source` in the prepared core Lean package and build the native
compiler and `zkc-structured_reference-test` in this checkout. Then run:

```sh
python3 lean/bridges/common/generate.py --compiler build/compiler/zkc-compile --check
python3 lean/bridges/common/check.py --report build/common-comparison.json
python3 lean/bridges/common/verify_tests.py --output build/common-requests
python3 lean/bridges/common/intent_tests.py --compiler build/compiler/zkc-compile --output build/common-intent
```

The native comparison reads original SSA independently of the export. Both
references use the existing Structured tool's BLS scalar field, with an additive
group model. The former Common differential executable used Z/97. Its independent
SSA comparison has moved to the existing Structured reference rather than adding
another evaluator. Symbolic certificates still quantify over their stated
fields/modules; the negative mathematical controls can still specialize to Z/97.
The exact old native Z/97 differential claim is retired, not transferred: the
existing `StructuredSource.Evaluation.scalarModel` and
`compiler/test/structured_reference.cpp::modulus` fix the BLS scalar modulus.
Keeping that numeric claim would require a different executable interpretation.
The maintained comparison uses those existing engines and records their scope.
None of these comparisons implements a production curve or validates native
sampling, compiler correctness or resource equivalence.

The controls compare complete canonical Structured observations before exposing
scalar outcomes for test assertions. They preserve arbitrary reply and stop
prefixes, mismatched sites, absent inputs, unread replies, helper equality,
honest and dishonest transcripts, and a deliberately corrupted export control.
Python constructs requests and transcripts and adapts wire values; it never
interprets source instructions.

## Explicit requests

```sh
python3 lean/bridges/common/verify.py \
  --snapshot lean/ZkcExamples/NativePrograms/fixtures/factor-horner.json \
  --request lean/bridges/common/requests/factor-openings.json \
  --output build/factor-request
```

`--module NAME=PATH --subject MODULE::PROTOCOL` obtains a fresh native Structured
export instead. The versioned request selects a registered mathematical
contract, its exact properties and experiment, verifier role, nominal domains,
input availability and wiring. Unknown or unsupported requests stay unresolved.

The candidate proposes only Structured constructor data. The strict serializer
accepts no Lean expression or command. The existing Lean printers emit typed
bodies, phased admission and a complete returned-row source equation. Each is
compiled with the kernel. The process presentation elaborator checks definitional
equality; it supplies no semantic evaluator.

The expected subject is separately serialized and admitted from the untouched
request/source copies. Its verifier uses fresh request-fixed input constructors
and wiring. Source and program identity, requested contracts and exact registered
properties are checked separately from candidate generation. A separate kernel
module checks literal candidate/request source identity before dependent process
transport, so a different subject fails promptly within the existing budget.
Every selected
theorem is audited transitively for axioms other than `propext`,
`Classical.choice`, and `Quot.sound`. Mutation controls include candidate source
and request mutation, command injection, copied identities and wrong subjects.

The present-input view covers exactly the declared availability pattern: visible
inputs are present and foreign inputs absent. It does not prove arbitrary-input
validity. Missing-input and foreign-role behavior have separate Structured
participant controls. Open-process equalities retain every independent reply,
continuation, handler state, event and stop; honest-message restrictions are
confined to the mathematical experiment or theorem premises.

Success remains **`verified-in-model`**. It is neither a canonical established
claim nor native security. Receipts retain the exact registered experiment and
premises, and explicitly exclude native sampling/arithmetic conformance,
Fiat-Shamir security, PCS binding and whole native prover correctness.

## Authored targets

`--spec lean/bridges/common/requests/schnorr-dsl.json` resolves named DSL ports,
roles and the authored target using the native interface. The selected formula
is retained as a named helper in the same Structured source unit. The relation
candidate and expected relation copies are separate. Kernel equations connect
its actual table invocation to the discrete-log predicate and connect two
accepting verifier executions to a witness for that predicate. A constant-true
formula, swapped selector or different relation subject cannot pass.

Native name/selector resolution, source export, strict serialization, Python
orchestration and the chosen toolchain remain tested or trusted boundaries.
The existing ArkLib Sumcheck and honest-verifier simulation consumers retain
their original scopes and independent dependency packages.

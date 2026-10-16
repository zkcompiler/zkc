# Architecture

A certificate has a source subject, an interpretation, a contract, a selected
property and explicit experiment assumptions. Those are separate objects.
`Zkc.Verification.Imported` ties a program to successful deterministic admission
of exact raw input. `Certificate` proves its interpreted contract. `Consumer`
transports that contract to a property's conclusion under its stated assumptions.
`Certificate.verify` composes those proofs. `Adapter` changes contracts only with
a proved preservation law. Property conjunction combines conclusions and their
assumptions; it never invents independent randomness or multiplies error bounds.

## Package boundaries

`Zkc.Semantics` defines effects, execution, refinement and continuation laws.
`Zkc.Source.Structure` defines the canonical local compiler carrier: intrinsically
typed regions with ordered result lists, closed region inputs and shared binding.
`RegionMeaning` supplies operation contracts; its interpretation returns the same
open processes. Contextual equality, semantic totality and explicitly compatible
higher-order effect translation are reusable laws over this carrier.
`ScalarRegion` bridges the maintained single-result `Source.Program` reference
profile. Mathematical projection directly produces canonical regions.
`Common.Region` lowers the participant profile and admitted scalar programs with
proved full-process equations; their bounded contracts and security consumers
remain intact.
See [structured computations](design/structured-computations.md) for ownership,
formation, examples and the native correspondence boundary.

`Zkc.Source.Participant` owns typed sends, receives and service queries, together
with the shared exchange, query, guard and restriction rules over optional
components. It depends on typed contexts, role families and process semantics,
without a mathematical language or scalar vocabulary. `Common.Program.denote`
and `Common.participantMeaning` both compose these rules; action consumers name
the same `Participant` interface directly. Services declare argument and result
types while handlers supply behavior and sampling policy.

`Zkc.Source.Mathematical` supplies a typed language/meaning interface. Role-local
programs combine mathematical interpretations with those participant rules.
`Zkc.Source.Common` instantiates a deliberately bounded native scalar profile.
A mathematical dialect can supply another language and interpretation; this
does not require putting every dialect in one untyped universal evaluator.

The structured profile keeps formed evidence in `Structured.CheckedData`:
exact signatures, raw bodies, typed regions and their erasure equations.
`Meaning`, component interpretation and participant semantics depend on these
records without importing the JSON reader or source admission. `Formation`
forms raw regions and retains typed diagnostic causes. `Checked` and the
admission modules own lowering, declaration ordering, preparation selection and
profile checks. Dependency tests enforce this separation for participant
semantics and the optional VCVio uniform-service adapter.

`Zkc.Protocols` owns mathematical experiments and reusable verifier contracts.
It may use generic source semantics; source semantics may not import protocols.
`ZkcExamples.NativePrograms` owns particular native exports and correspondence
proofs. `ZkcSecurity` owns optional external consumers and connection laws;
its generic adapters do not import particular source examples. Its `Examples`
subtree instantiates those consumers. `ZkcClean` remains a separate relation
adapter. Module-header checks and declaration dependency audits enforce these
boundaries, including proof bodies and generated/private declarations.

## Structured proof construction

Retained declaration contracts and explicit formula links belong to original
PIR and the independently admitted snapshot. They do not change executable
participant operations. Selected-Entry metadata refers to the canonical owned
target clause; component contracts remain reusable at ordinary protocol calls.

`Structured.ContractBinding`, `ContractBoundary` and `ContractMeaning` connect
those declarations to typed port/role selections and actual formula invocation.
Logical assignments are scoped by owner and explicit invocation labels; those
labels do not prove dynamic reachability. A shared interpretation
environment fixes opaque relation meanings. `ContractExecution` projects
boundaries from actual outcomes, preserving absent participants and stops.

`Source.RegionDerivation` and its tactics derive process correspondence from the
same typed body using local rules. `Structured.ContractCalls` enumerates lexical
calls; `ContractComposition` proves actual callee substitution and continuation
laws. `ContractObligations` records selected mathematical uses, residual or
terminal requests and call coverage. It does not select a security experiment.
Optional library consumers supply that experiment and its proved transport.

The [design rationale](design/protocol-verification.md) explains why structural
proof construction, logical interpretation and property application have separate
owners. [Verification](spec/verification.md#structured-contracts) defines their
proof obligations.

## Reuse and composition

A source certificate proves exact equality of an open process, including all
requests and continuations. It can therefore be reused under deterministic,
stateful or probabilistic handlers. Schnorr's same certificate supports
completeness, special soundness, a custom rejection property, and VCVio simulation.
Original, helper-based and reordered sources reuse these consumers. Sumcheck's
original, helper-based and Horner forms reuse finite soundness and ArkLib's
reached-query probability experiment.

Sequential refinement uses `ExactRefinement.bind_congr`; execution threads the
actual successor state and concatenates ordered events. `Common.ResidualContract`
connects Sumcheck rounds to a terminal checker. `FactorOpening` composes rounds
with adaptive factor replies and an explicit bad-opening event. Its conditional
bound is the Sumcheck error **plus** an opening error bound; independent events
are not assumed. Public polynomial checks prove that opening error is zero.
A PCS needs its own proved opening consumer and assumptions.

This supports many compatible source × contract × property combinations.
Incompatible views, adversary access or sampling policies need an explicit
adapter theorem. Adding one consumer does not promise that it applies to every
contract. A downstream Lean module can define a property and consumer directly;
`CustomProperty.lean` demonstrates this without editing the CLI registry.

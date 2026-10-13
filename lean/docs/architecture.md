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
`Zkc.Source.Mathematical` supplies a typed language/meaning interface. Role-local
programs use that interface and typed services. `Zkc.Source.Common` instantiates
a deliberately bounded native scalar profile. A mathematical dialect can supply
another language and interpretation; this does not require putting every dialect
in one untyped universal evaluator.

`Zkc.Source.Constructed` admits an actual constructed participant separately from
its original interactive program. Its typed SSA retains selected Local bodies,
primitive descriptors, every result of a provider call, guards and returned
state. It reuses the existing typed `Program` and `Proc` semantics. A protocol
adapter supplies fixed primitive meanings and proves the actual imported body's
equation before projecting a security observation. An abstract transformation of
the original program alone does not establish that equation.

`Zkc.Protocols` owns mathematical experiments and reusable verifier contracts.
It may use generic source semantics; source semantics may not import protocols.
`ZkcExamples.NativePrograms` owns particular native exports and correspondence
proofs. `ZkcSecurity` owns optional external consumers and connection laws;
its generic adapters do not import particular source examples. Its `Examples`
subtree instantiates those consumers. `ZkcClean` remains a separate relation
adapter. Module-header checks and declaration dependency audits enforce these
boundaries, including proof bodies and generated/private declarations.

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

## Construction and security experiments

Construction is a separate proof boundary within this architecture. The checked
native exporter records the actual constructed candidate and its policy. Lean
admission proves that the exported instructions form a typed program. A fixed
primitive interpretation then gives that program a mathematical meaning. Its
normalization theorem connects it to a protocol construction; a separate game
equation connects the selected observation to an external security experiment.
Each of these steps has a different conclusion and may fail independently.

Schnorr uses a fixed-statement cached-oracle extraction experiment from VCVio.
Two-round Sumcheck uses ArkLib's all-prefix knowledge conditions and restoration
bound. Its full-prefix adapter encodes the earlier challenge in a restoration
salt and proves the resulting cached-game equation. These constructions reuse
the source contracts and the same admission/execution interfaces, but their
adversaries, observations and quantitative conclusions differ.

Transcript bindings include the source, construction, application context and
public statement. An ideal transcript interpretation does not establish that a
native Merlin descriptor realizes a random oracle. Provider conformance, byte
encodings, field/group implementations and subsequent native lowerings remain
separate connection obligations. The request and receipt identify this selected
interpretation explicitly.

## State, observations and resources

`Proc.runM_interpret` transports complete execution through an interpretation in
any lawful monad. `Cost` records a selected operation charge while preserving
outcomes, events and provider state, and proves the cost of actual lower-operation
expansions. One source call is not automatically one oracle access. `Provider`
proves disjoint-state composition and concrete memoization laws; neither law
asserts independent randomness for providers sharing mutable state.

`FiniteControl` supplies runtime-selected bounded iteration and conditional
completion over the existing process model. Its call bounds and retained state
are formal-model laws; the constructed importer still rejects unsupported native
control. A selected iteration count can reveal private data through observations
or costs even if both executions return the same Boolean.

Exact process or cache equations support subsequent compatible computation.
Acceptance-only correspondence has a narrower use: the Sumcheck completion game
may make queries after the actual verifier has rejected. Its acceptance bound
does not justify replacing the actual execution's final cache, trace or cost in
an arbitrary continuation.

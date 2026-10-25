# Architecture

A certificate has a source subject, an interpretation, a contract, a selected
property and explicit experiment assumptions. Those are separate objects.
`Zkc.Verification.Imported` ties a program to successful deterministic admission
of exact raw input. `Certificate` proves its interpreted contract. `Consumer`
transports that contract to a property's conclusion under its stated assumptions.
`Certificate.verify` composes those proofs. `Adapter` changes contracts only with
a proved preservation law. Property conjunction combines conclusions and their
assumptions; it never invents independent randomness or multiplies error bounds.

The [checked component architecture](spec/components.md) connects generated full-process
bindings to both honest completeness and adversarial reductions. Its canonical
claim authority fixes the experiment before either proof method is selected.

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

`Zkc.Construction` owns the compiled-stage carrier: exported constructed
participants, their ideal and interactive meanings, and the checked stage rules
between them and the structured original (transcript construction, participant
projection), with soundness theorems that compose
([checked compiler stages](design/checked-stages.md)). It depends on structured
participant semantics; the structured import does not depend on it.
`Zkc.Executable` owns the next stage down: the validator participant of a
`zkc.program/0` candidate, its meaning under a native proof host and the
checked lowering rule from the constructed validator
([executable stage](spec/executable.md)). It depends on `Zkc.Construction`; no
construction module depends on it.

`Zkc.Protocols` owns deterministic mathematics, execution and reusable verifier
contracts. Adaptive tapes, causal equivalences and observation fibers live in
`Zkc.Semantics`; their existing declaration namespaces remain available.
Pointwise Sumcheck completeness retains its `CommSemiring` assumptions.
`ZkcExamples` owns deterministic source clients.

| Package directory | Package name | Library and test module roots | Dependencies |
|---|---|---|---|
| `lean/` | `zkc` | `Zkc`, `ZkcExamples`, `ZkcTools`, `Tests` | Mathlib |
| `lean/security/` | `zkc_security` | `ZkcSecurity`, `TestsSecurity` | Core, VCVio, PolyFun, CompPoly, Mathlib |
| `lean/integrations/arklib/` | `zkc_arklib` | `ZkcArkLib`, `TestsArkLib` | Core, security, ArkLib and coherent shared pins |
| `lean/integrations/clean/` | `zkc_clean` | `ZkcClean`, `TestsClean`, `CleanExamples` | Core, Clean and coherent shared algebra pins |

Library roots and globs are disjoint across packages, including module names
without a source file. Module paths express ownership; declaration namespaces
and theorem names are retained independently. Core has no forwarding imports of
security. `checks/check_package_ownership.py` checks actual Lake resolution.

`ZkcSecurity.Probability.UniformTape` owns uniform finite-tape expectation.
`ZkcSecurity.Families.Sumcheck` owns quantitative verifier, source, common,
committed and factor-opening results. Their deterministic counterparts remain
in core, including full execution contracts, arbitrary causal strategies,
states, events and stopped prefixes. No quantitative bound or malformed-input
case is changed by the partition.

Reusable VCVio execution, Sigma composition, Schnorr-family mathematics,
Fiat–Shamir and commitment machinery belong to security. VCVio's upstream
`Examples.Schnorr.SigmaProtocol` and `ToMathlib` modules are classified by their
actual provider. `ZkcSecurity.Commitment.Opening` owns the reusable one-opening
family, with its original declaration namespace; `HashChain.JointOpening`
imports this library module. Four Sigma subjects live under security's
`Examples.Subjects`. ArkLib Sumcheck, causal Sumcheck, FRI, GKR,
`FiatShamir.Upstream` and the Guess/Sumcheck subjects live under `ZkcArkLib`.
All examples and tests remain default targets of their owning package.

`ZkcSecurity.Registry` contains generic schemas and endpoints.
`ZkcArkLib.Registry` contains optional schemas. Its `reportTable` and `reportEndpoints` provide the combined
generic and optional context when emitting declaration details; the owning entry
lists remain disjoint. Record readers combine compatible
entries and reject identifier or endpoint collisions. Neither registry imports
subjects into a reusable library; package audits validate the named schemas in
the environment containing the actual providers.

## Dependency policy and retained exceptions

The allowed-edge table in `ZkcTools/DeclarationAudit.lean` is shared data for
`checks/check_library.py` and the Lean declaration audit. The source audit
uses Lean's header parser and checks transitive imports; the declaration audit
checks actual type and proof-body references, including private and generated
declarations. During elaboration, the shared JSON literal becomes ordinary Lean
data with typed module names; the policy remains reducible by the kernel. Both cover `CleanExamples` as well as all selected packages' library
and test modules. Prefixes classify responsibilities during migration; they do
classify dependencies independently of declaration namespaces.

| Owner layer | Allowed repository layers |
|---|---|
| Core language/compiler | Core |
| Probability foundation | Core, probability |
| Deterministic families | Core, deterministic families |
| General security | Core, deterministic families, probability, general security, security families |
| Security families | Core, probability, deterministic families, general security, security families |
| External security adapters | The preceding layers and other adapters |
| Clean adapter | Core, deterministic families, Clean |
| Subject evidence/examples | Their upstream libraries and other subjects |
| Tests/tooling | Any repository layer |

`ZkcSecurity.Realizations` owns reusable laws for concrete source implementations.
For example, its Sumcheck helper laws accept checked body-membership evidence
for any admitted program containing the installed library bodies. These are
source-bound realizations, so the dependency audit assigns them the same
boundary as subject evidence; general security and family mathematics cannot
import them. Moving them out of `Examples` introduces no new allowed edge or
exception. Existing underlying source-library templates remain in `ZkcExamples`
until their separately planned migration.

Mathlib/Lean foundations are available throughout; VCVio and PolyFun
belong to generic security, ArkLib to its optional package, Clean to the Clean
package, and CompPoly is available to the packages that require it. More specific guards preserve generic
execution's independence from protocols/ArkLib, causal Sumcheck's independence
from source syntax, source's independence from compiler code, and probability's
independence from source/compiler code.

Legacy violations are exact module pairs grouped by the rule they break, with
a reason for each group. A reachable-pair exception does not authorize a new
direct import: the table also records which pairs were direct. A new violation,
a new direct edge, a removed owner, or an exception whose edge no longer exists
fails the source audit. Remove obsolete entries when the corresponding module
moves or dependency disappears. An optional package not selected for a run is
not declared stale. The Lean audit accepts the same exact pairs but does not
check list freshness, because a client audit may select only one module.

The only retained exception is `CleanExamples` importing `TestsClean.NativeClients`.
The former family-to-probability, generic-security-to-adapter and
`JointOpening`-to-example exceptions have been removed. ArkLib upstream is a
separate policy layer from VCVio/PolyFun upstream. In addition to header and
stored-declaration checks, `check_library.py` validates exact path providers,
coherent pins, complete default targets and package closure: core excludes
security ecosystems, and generic security excludes ArkLib and Clean.

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
`ReplyScript` fixes the replies of one role-local run by type and site, so a
transcript's actual returned outputs and ordered sends can be observed; it is an
experiment choice, not a provider law.

`Structured.UnitViews` emits a unit's literal checked payload from its typed
bodies: `structured_views` writes the checked declarations, the payload and one
named kernel equation per admission phase, ordering declarations with the
admission orderers themselves; `structured_associations` writes each body's
membership, signature and raw-tree association. The commands produce ordinary
declarations, so a stale or mistyped body fails a phase equation. Phase
equations use `kernel_rfl`, which checks a definitional equality in the kernel
only, for every value of the goal's binders at once.

`bridges/structured/normal_forms.py` generates the role-local facts of an
admitted unit from its retained snapshot and a short request: site constants,
positional input builders, each participant's normal form with its process
equation, carried-state embeddings, reply scripts and observed runs, and the
relation binding and observed decision of a contract clause. A root equation
that holds definitionally is checked by `kernel_rfl` alone. Every other process
equation is an instance of one soundness theorem: `Structured.NormalForm`
defines participant forms (`Syntax`) and their processes (`Denote`), a
normalizer that computes one role's form of a typed body by symbolic
evaluation under the participant rules (`Normalize`), and
`NormalForm.normalize_sound` with its uniform-meaning corollaries
(`Soundness`, `Presentation`). The compiled normalizer
(`structured-source normal-form`) prints the form as a Lean literal; the kernel
checks by evaluation that the normalizer returns it and that its process is the
readable one, and the request's helper laws and callee summaries discharge the
theorem's premises. For a body that applies other protocols the callee's
generated normal form stands at the application's child context, between the
callee's input and output masks, and each role's invocation at any caller
context is stated. The generator's output is ordinary source that the kernel
checks; what it cannot derive (helper laws, premises, protocol mathematics) stays authored.

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

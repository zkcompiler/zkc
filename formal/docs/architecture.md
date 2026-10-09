# Formal library architecture

The library has a small execution foundation, typed source and interpretation
APIs, source-relative checking, concrete domain/protocol applications and an
optional external integration. These are semantic dependencies, not a prescribed
stack of native IR dialects. It builds independently of MLIR and Rust.

[Support](support.md) owns established claims; the [model specification](spec/README.md)
owns definitions. [Native correspondence](../../docs/assurance.md#native-correspondence)
requires its own explicit connection.

## Packages and dependencies

Use one main Lake package in `formal/`, depending on a pinned Mathlib, and
separate optional integration packages in `formal/integrations/arklib/` and
`formal/integrations/clean/`.
The ArkLib package depends on the main package and the required ArkLib ecosystem,
including VCVio/PolyFun where their actual adapters use them. Core probability
uses Mathlib distributions and the common monadic execution interface. External
probabilistic-program and polynomial representations enter through explicit
interpretations and correspondence theorems.

Use VCVio/ArkLib definitions and proof tools directly in integration modules
where they fit. Keeping external types out of the core does not require
duplicating their game logic, probability library or protocol proofs. A claimed
property that uses an external theorem has that package as a real proof
dependency, even though ordinary source/compiler clients can omit it.

An optional import is not an optional package dependency. The main package
must neither require ArkLib in its manifest nor reference integration objects.
The integration package has its own build/audit target and compatible exact
pins. A version check rejects conflicting Lean or shared Mathlib revisions.
The root package still resolves Mathlib even when a particular module imports
only `Std`; no zero-dependency installation claim follows from a small import.
Lake supports separate packages and local path dependencies; its configuration
syntax follows the package's pinned toolchain.

Logical areas are not separate repositories or independently versioned packages:

| Area | Owns | Dependency boundary |
|---|---|---|
| `Zkc.Semantics` root | Signatures, complete executions, interaction, observations, contracts and simulation | Lean/Std; independent of source, compiler and protocols |
| `Zkc.Semantics.*` extensions | Interpretation, boundary, local execution and terminal/continuation laws | Narrow foundation; preparation uses `Zkc.Modules` immutable-cache contracts; consumer extensions such as `AuthorizedContinuation` also use source endpoints |
| `Zkc.Modules` | State contracts, immutable preparation, allocation and factor-domain models | Foundation, relevant source/domain objects, narrow Mathlib where needed; factor contracts exclude compiler algorithms |
| `Zkc.Transformations` | Reusable semantic transformation laws, including immutable memoization | Foundation and module contracts; concrete compiler clients instantiate the laws |
| `Zkc.Source` | Structured syntax, typed bindings, elaboration, admission and denotation | Foundation and domain contracts; no optimizer dependency |
| `Zkc.Probability` | Complete execution distributions, initialization, conditioning and persistent resources | Foundation and Mathlib; no source grammar, compiler or protocol dependency |
| `Zkc.Properties` | Experiments, contextual evidence, strategy classes and property transport | Relevant semantics, source and probability APIs; `Judgment` owns conditional evidence |
| `Zkc.Realization` | Value/state/codec relations and logical adapter models | Relevant semantics and source/domain APIs |
| `Zkc.Compiler` | Search, transfer, transformations, source-relative checking and lowering proofs | Relevant semantic, source and realization APIs; property consumers can use Properties |
| `Zkc.Polynomial` | Fixed mathematical objects, evaluation and concrete preparation consumers | Narrow Mathlib and semantic APIs; compilation modules additionally use Compiler |
| `Zkc.Protocols` | Protocol-specific syntax, algorithms, property instances and compiler applications | The preceding library areas; never a dependency of generic library modules |
| `integrations/arklib/ZkcArkLib` | Actual external correspondences and external-dependent proofs | Main library and declared external packages; never the reverse |
| `integrations/clean/ZkcClean` | Export of a Clean flat AIR fragment into the finite AIR model, its ring trees and its prime-field native emission | Main library and the pinned Clean package; never the reverse |
| `Tests`, `Examples`, tools | API clients, controls and maintenance | Library modules; never imported by library definitions |

Directories organize concepts; the actual module graph determines dependencies.
They do not form a strict linear stack. For example, `Source.FactorQueries` uses
`Modules.FactorExecution`, while `Modules.FactorBinding` uses the separate
`Source.FactorInputs` grammar. Neither imports optimization. The graph is acyclic.
Consumer-specific joins have explicit homes:

- `Modules.Factor` owns values, facts, demand-plan meaning and independent finite
  plan admission; `Compiler.Analysis.FactorReuse` owns candidate search.
- `Modules.FactorExecution` owns effects, handlers and readiness refusal;
  `Compiler.FactorExecution` embeds compiled callers into that meaning, and
  `Compiler.FactorGuards` proves preservation through reached refusals.
- `Modules.PolynomialPreparation` proves the actual operation contracts;
  `Compiler.PolynomialPreparation` supplies the optimization-law instance.
- `Compiler.FactorBinding` connects supplied installations to compiled callers.
  `Modules.FactorScopes` owns lexical bindings and their interpreter;
  `Compiler.FactorScopes` and `Compiler.FreshAllocation` own the conservative
  and registered-allocation optimization passes.

`import Zkc` exposes the small execution/interaction foundation. Narrow imports
select other APIs. `Tests.LibraryImports` is generated from all maintained
library, test and example modules for exhaustive declaration auditing; it is not
a public umbrella API. The optional package has its own aggregate. Tool wrappers
are separately compiled and linked. Their orchestration and serialization code
are outside that declaration audit and remain part of the execution trust boundary.


## Semantic organization

- Typed source retains actual context order, captures, domain objects and
  control. Its denotation is an interpretation into complete execution.
- Operation contracts distinguish returned values, stops, residual state and
  ordered events. State framing and immutable preparation have separate laws.
- A transformation fixes the actual source, candidate and relation. Analyses
  provide sound sufficient facts; uncertainty can refuse a transformation.
- Probability fixes the actual joint initialization and reached transitions.
  Property transport also fixes the observer and adversarial experiment.
- Realization relates logical values to native-like representations at actual
  states. Mathematical models of storage and codecs do not verify native code.

The [semantic choices](design/semantics.md), [analysis choices](design/analysis.md)
and [observation choices](design/observations.md) explain these decisions. Exact
rules and theorem premises remain in the specification and support map.

## Public API and proof engineering

Common execution objects use the `PIR` namespace, with operations under their types:
`PIR.Proc.run`, `PIR.Execution`, `PIR.Contract`. Domain APIs use meaningful
namespaces such as `Zkc.Source`, `Zkc.Modules.Factor`, `Zkc.Compiler.FactorReuse` and
`Zkc.Protocols.Sumcheck`. File placement follows dependency and discovery;
it need not add `Semantics` to every common object's qualified name.

New object-specific laws belong with that object's namespace. Existing commonly
used `PIR.run_bind` and `PIR.follow_assoc` remain canonical entry points; do not
add forwarding aliases merely for cosmetic uniformity. Example-only controls
belong in tests, and generic facts belong below their protocol applications.

One definition owns each concept. Do not introduce parallel old/new worlds,
outcomes or source grammars solely to preserve theorem names. A necessary
specialized model has an explicit interpretation into the shared vocabulary.
Remove numbered names from active declarations and documentation. Keep one current API without compatibility aliases or historical wrappers.

Expose equations, introduction/elimination lemmas, compositional laws and
preservation theorems that consumers need. A public proof should not routinely
unfold another area's implementation. Start with definitions and their basic
laws together; split larger topics into descriptive modules when imports or
proof maintenance justify it, rather than creating one file per theorem.

Use universe polymorphism and minimal algebraic assumptions where an actual
client benefits. Executable `Signature`, `Proc`, source sorts and values currently
live in `Type`; supported protocol clients fit that boundary. Contextual
`Properties.Conditional` and observation-fiber equivalences are universe
polymorphic, so contexts can package relation families and interpretations.
A higher-universe executable client would require an explicit carrier extension. Decidability required by a checker does not belong
on every semantic theorem. Keep chosen bindings and observers explicit even
when algebraic parameters can be inferred. Semantic identifiers have distinct
types where mixing them changes meaning; converting a `Nat` wrapper is not an
authentication theorem.

Maintain small, terminating simplification interfaces and scoped notation.
Use `abbrev` for intended transparent aliases, not to make every definition
unfold automatically. Local proof helpers stay private where the selected Lean
module system supports it. Tactics and elaborators live in separate tooling
modules and produce normally checked proof terms. Global instance or simp-set
changes receive both consumer regression checks and elaboration measurements.
This uses Mathlib's experience with proof APIs, transparency and performance,
without importing its repository workflow wholesale.

Public definitions have type signatures and docstrings. A substantial module
explains its mathematical object, central laws, assumptions and a small use
case, with literature where a method is applied. Historical task names and
progress reports are omitted. Named public imports express support intent;
they are not a security boundary against arbitrary Lean metaprograms.


## Validation and references

The [package guide](../README.md#build-and-validate) owns build and audit commands.
The [assurance policy](../../docs/assurance.md) distinguishes proof replay, compiled
checks, finite tests and implementation trust. Keep code, declaration coverage
and consumer checks together when an API changes.

[Primary references](theory.md#references) identify the methods behind the model.
Unadopted research routes do not prescribe a native implementation architecture.

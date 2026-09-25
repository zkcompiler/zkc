# Formal library architecture

[README](README.md) describes use and [SUPPORT](SUPPORT.md) identifies actual claims.
The [selected-model reference](../docs/README.md) routes semantic ownership:
[spec/](../docs/spec/README.md) owns the normative contracts, including
properties, probability, joint release and atomic continuations. The
[PIR guide](../docs/guides/protocol-model.md) explains their use.

The library has a small common execution foundation, typed source and lawful
interpretation APIs, source-relative transformation checking, concrete module
and protocol applications, and a separately resolved ArkLib integration. These
are semantic dependencies, not a prescribed stack of compiler IR dialects.
The [implementation handoff](design/implementation-handoff.md) records which
information each native abstraction must retain before it can be lowered.

The [verification map](design/verification-map.md) separates actual source
adequacy, checker soundness, compiler refinement, native correspondence and
protocol security. [The roadmap](../docs/roadmap.md) orders subsequent
engineering. Exact
MLIR carriers and native ownership/extraction choices still need their stated
implementation evidence. The library builds independently of MLIR and Rust.

## 1. Product and scope

The library serves three clients: a researcher interpreting a protocol, a
compiler author proving or checking a transformation, and an implementer
establishing a realization contract. Each must be able to use it without
knowing the sequence of research tasks that produced it.

Its product is maintained definitions, executable algorithms where promised,
composable theorems, substantive protocol instances, documentation and tests.
Public declarations are organized by meaning. Research numbers, comparison
wrappers and preserved source hashes are not part of the product API.

The selected finite, atomic model is retained. Protocol-security verification
and transport are first-class library uses. The baseline includes scoped interactive completeness/soundness and checked
verifier-evaluation transport. Native correspondence remains a separate delivery. General asynchronous execution, universal choreography projection
and a universal computational-security framework are extensions with their own
obligations. A polished library does not acquire them through a more general-looking
type name.

## 2. Packages and dependencies

Use one main Lake package in `formal/`, depending on a pinned Mathlib, and a
separate optional integration package in `formal/integrations/arklib/`.
That package depends on the main package and the required ArkLib ecosystem,
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
syntax is verified against the toolchain chosen for migration. [1]

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

## 3. Mathematical objects and source representation

Keep one canonical signature, outcome, execution and process vocabulary.
`Proc` remains a well-founded, typed effect-tree denotation. It can branch over
an infinite reply domain; a public uniform call bound remains a separate
property. It is not the optimization representation or an encoding of host
closures. Deterministic interpretation and `m (Execution ...)` interpretation
share sequencing, failure and observation laws.

The process, its interpreter, its contracts and its observer are separate
parameters. Whole executions retain post-state and ordered events on failure.
Recoverable operation failure belongs to its reply type; terminal stopping is
an execution outcome. A former Boolean module result may be interpreted as a
returned Boolean without converting its recovery branch into terminal abort.

The source design uses the following boundaries:

1. **Raw syntax:** finite data suitable for parsing and transport, with explicit
   source references, public shapes, binding slots, operations and regions.
2. **Typed syntax:** values indexed by their sorts and finite local contexts;
   variable references use typed de Bruijn indices. Regions have explicit block
   arguments/results. Branches and public bounded loops retain structure.
3. **Interpreted bindings:** actual inputs, immutable captures, module meanings
   and public configuration are supplied explicitly to denotation/admission.

Static indices and field elements are different sorts. Source identities are
distinct from binder positions and native storage locations. Runtime field
values need not occur in serialized source; a binding can supply them at
execution. Stable symbolic references do not establish equality of interpreted
values or authorization to disclose those values.

Use intrinsic typing for local sorts, arity and scope. Use explicit predicates
and checkers for input availability, phase legality, resource conditions and
protocol properties. Indexing every source node by all semantic proofs would
make transformation and external frontend integration unnecessarily dependent
on proof representation. Conversely, raw syntax alone is not an admitted body.

Each source constructor has an interpretation and compositional laws. Renaming,
substitution, binding and checked erasure are part of the API, not repeated
ad hoc proofs in protocol files. An operation extension supplies a typed
signature, its interpretation and the laws actually consumed by an analysis.
No arbitrary host callback becomes a portable source constructor.

The maintained finite-source clients exercise this extension mechanism with
two field domains, a distinct operation and rejection of accidental sort mixing.
Generic binding/control laws quantify over interpreted signatures; domain
identities do not collapse to the first field or machine representation. Keep observers, provider
laws and requested relations
explicit parameters in their shared APIs, even when the first executable
checker supports only the selected local/representation relations. Adding a
property application must not require replacing a global correctness Boolean
or changing the core execution outcome type.

The generic source API and specialized instruction-source models coexist with
explicit interpretations. A fixed-register instance does not define the entire
source language. Extending its register or return representation requires the
corresponding embedding and preservation law; it is a semantic extension.

### 3.1 Source carrier and upstream reuse

The maintained source carrier is the small owned finite typed calculus in
`Zkc.Source`. The actual Lean-MLIR compatibility trial required proof-script
porting of its first context modules on the selected toolchain, before the full
stateful client could run. That is a bounded maintenance decision, not evidence
that Lean-MLIR cannot express effects or regions. No upstream implementation
was copied into this library. Its monadic SSA/region calculus remains a candidate
for a compatible, useful adapter. [4]

Reconsider that choice using typed captures, a branch, a stateful failed call
and an actual rewrite, with a proved interpretation into the complete execution
model. Compare the proof machinery saved and the maintenance cost. A different
carrier does not change PIR meaning without a corresponding interpretation law.

CSLib's transition-system composition and trace-lifting theorems were inspected
as potential reuse. [5] The core uses its own complete outcome/state/observation
relations; it does not currently claim an LTS bridge. The optional PolyFun path
uses CSLib free-monad foundations through its actual dependencies. These are
different uses. A future LTS adapter must account for terminal outcomes and
observations, not only returned values or transition traces.

The existing `Source.Program`, `Compiler.Plan` and admission clients establish
binding, branches, bounded repetition and stopped execution. The concrete MLIR
review must decide which information to preserve in each native level; the
owned Lean source calculus does not require a one-dialect transcription.

## 4. Contracts, analyses and checking

Phase admission now uses one compact-region checker, including explicit
binding, with a direct conformance/return-cover proof. Tree programs embed with
`toRegion` and keep their existing admission API. This consolidates two source
consumers without flattening or adding a new execution meaning. The certificate
codec and [phase tests](Tests/PhaseAdmission.lean) move with that rule; native
evidence consumption remains a separate compiler boundary.

Use ordinary explicit records for chosen protocol/module interpretations,
observers, providers and backend premises. Use type classes for coherent
algebraic structure, decidable data and standard reusable interfaces. Instance
search must not silently choose which protocol, observer or trust assumption a
theorem concerns. The distinction follows from how instance synthesis selects
registered or local instances. [2]

Generic module framing speaks about interpreted state relations and assertions.
Separate the factor domain from the analysis that reasons about it:

| Concept | Target owner | Reason |
|---|---|---|
| Identity, queries, values/views, facts, `Means` and direct/reuse plan meaning | `Zkc.Modules.Factor` | Source and realization need the domain and its independent plan check |
| World transitions, write frames, readiness, outcome summaries and sound transfer | `Zkc.Modules.FactorState` / `FactorContract` | Producers establish facts and laws without choosing a search algorithm |
| Candidate search and its admission/value proofs | `Zkc.Compiler.Analysis.FactorReuse` | Search consumes the independently stated domain contracts |
| Actual source replacement and source-relative checking | `Zkc.Compiler.FactorOptimization` | The compiler chooses and justifies an implementation of the query |

A factor world is explicitly specialized, not the universal PIR state. A
module's behavioral contract is distinct from an analysis summary derived from
or justified by that contract. This avoids a cycle in which Source needs
Compiler merely to describe a factor query. A semantic assertion and a sound
transfer law are sufficient for the current analysis; a lattice/Galois
connection is introduced only when a real analysis or fixpoint theorem
requires it.

Immutable preparation has a generic key/provider/cache invariant and laws.
The factor-table instantiation lives with its compiler application. Costs use
explicit accounting semantics and retain lookup/insertion overhead. A cache
hit does not license moving a draw, commitment or stateful call.

`Semantics.Preparation` owns one preparation signature extending an arbitrary
external signature, with a product of private cache and external state. Its
contextual law preserves complete external behavior under the provider and
observer premises. `Semantics.Preparation.Emission` is the event-only reference
client; its embedding retains the original preparation interpreter and cost
equations. This is a specialized interpreter correspondence, not a second
general preparation API. Protocol instantiations supply their actual keys,
prepared values and source connection outside the generic dependency direction.

For each supported pass, expose the analysis meaning, proposal or transfer
algorithm, certificate data, executable checker, checker soundness theorem and
actual source-level application. The essential obligation has this shape:

```text
check actualSource actualBinding target certificate = accepted
  -> actual initial/module/provider premises
  -> Preservation actualSource actualBinding target
```

`Preservation` names the appropriate relation, not one universal correctness
bit. The consumer fixes the source, public instance, semantic environment,
binding, target and observer/property being checked. A proposal cannot select
a weaker claim or change the field interpretation through its own metadata.
Hashes can identify bytes for lookup; they do not establish their interpretation
or authorize disclosure of captured values.

The premises need producers: installation establishes a fact, mutation
preserves or invalidates it, and a consumer uses it at the actual point of
execution. A successful certificate check does not establish arbitrary supplied
semantic assertions. Premise satisfiability and at least one substantive
application are reviewed alongside the conditional theorem.

Logical evidence and serializable reports are different types. A Lean result
containing a proof is not a JSON certificate and proof erasure does not make a
native Boolean into evidence. Malformed input, unsupported syntax, exhausted
checking resources, rejected candidates and proved semantic refutations remain
distinct. Failure to prove a claim is not a proof of its negation. Checker
failure is also distinct from a modeled protocol stop.

Support both direct proof composition and reflection through a sound executable
checker. For the first compiler connection, prefer validating a concrete
proposal against a fixed, adequately interpreted source. The producer may use
expensive search. Completeness or optimality requires a separate theorem and
is not a prerequisite for a useful sound checker.

## 5. Probability, protocol properties and realization

Generic probability lemmas quantify over initialization, programs, handlers and
observers without referring to one scalar verifier. Source-specific joins use
these lemmas in Properties or Protocols. Correlated setup remains one joint law
with explicit state evolution; it is not silently replaced by independent draws.
Noncomputable mathematics is permitted here, while executable checker paths
must have computational definitions and a stated native execution boundary.

Keep these proof obligations distinct:

- Local execution refinement: outcomes, related states and the declared view.
- Representation refinement: values, replies, consumed input, malformed input,
  errors and target observations across a concrete representation change.
- Protocol-property transport: a named experiment, actual strategy/context
  translation, initialization/coupling assumptions and quantitative loss.

The same-reply handler theorem remains a useful specialization. Different wire
types or adversarial target contexts require their own relation and simulation;
they are not coerced into its hypotheses. Deterministic joint-release laws and
distributional joint-release laws also remain distinct.

Protocol modules own particular messages, round polynomials, verifier equations
and setup laws. Their names state the implemented scope: a scalar-round
interpretation is not advertised as a complete Sumcheck security development.
Generic algebra and probability results are factored down only when their
statements and proofs are independent of those protocol choices.

The current source-bound authorized export is a logical realization adapter
combining source admission, an installed policy and an isolated ledger. Its
complete laws must survive under Realization; it is not part of the minimal
execution vocabulary. Pure continuation/returned-phase laws remain in Semantics.
Typed identifiers prevent accidental mixing but do not establish native
unforgeability, isolation, alias freedom or generative authority.

A Rust backend may explicitly be trusted to implement a shared mathematical
contract. Native value/state/codec correspondence has a separate home and
assurance status. ArkLib correspondence concerns mathematical representations
and theorem premises; it does not prove Arkworks machine code.

Optional Rust extraction packages depend on this common realization API, never
the reverse. Generated implementation types stay inside the integration package.
The [native design](design/native-correspondence.md) specifies actual-source
extraction, external models, progress/failure obligations and build-input binding.
Proving an extraction-friendly rewrite requires a separate connection to the
production function unless that rewrite is the function actually executed.

### 5.1 Protocol proofs as actual compiler clients

The property interfaces must support both externally proved protocols and
proofs of experiments interpreted from the same PIR that the compiler consumes.
An external-theorem adapter relates the actual statement, program, allowed
strategies, initialization, observations and terminal event. A direct PIR game
interpretation needs the corresponding adequacy law. Neither interface requires
every source construct to fit one universal IOR representation.

Keep the following dependencies explicit:

```text
source security + adequate source/game interpretation
  + property-appropriate transformation evidence
  → transformed-source security
  + adequate runtime/provider correspondence
  → actual-execution claim under the remaining implementation assumptions
```

Generic local preservation, certificate soundness and protocol-property
transport are separate theorems. A protocol-changing pass can require strategy
translation and quantitative loss. Native realization is not inferred from
either theorem. Likewise a verifier soundness theorem quantifying over arbitrary
provers does not by itself establish honest completion after a prover rewrite.

General theorems are developed and audited with the library. Individual
compilations instantiate them for the retained source, target, configuration and
policy; finite certificates supply the decidable evidence. New security ideas
still need proofs, not just executable checker branches. Runtime guards check
actual dynamic conditions, and the protocol verifier separately checks each
received proof. These operations share definitions but have different subjects
and assurance boundaries.

The [first security companion](../docs/roadmap.md#4-the-security-companion)
is an implementation client of these interfaces, not a claim that a scalar
probability theorem alone supplies a whole Sumcheck argument. Reuse is evaluated
on exact declarations and their transitive assumptions; an imported unfinished
theorem is not admitted evidence.

## 6. Public API and proof engineering

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
Remove numbered names from active declarations and documentation. Compatibility
aliases are temporary only when an identified migration consumer needs them;
there is no requirement to publish a historical API.

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
without importing its repository workflow wholesale. [3]

Public definitions have type signatures and docstrings. A substantial module
explains its mathematical object, central laws, assumptions and a small use
case, with literature where a method is applied. Historical task names and
progress reports are omitted. Named public imports express support intent;
they are not a security boundary against arbitrary Lean metaprograms.

## 7. Theory obligations during construction

The following table identifies the obligations to examine while implementing
the architecture. Existing scoped results are inputs; this table does not
claim that every stronger law has already been proved.

| Lens | Concrete obligation | Boundary to retain |
|---|---|---|
| Algebraic effects and structural induction | Sequencing/handler laws over one complete execution model; monadic interpretation agrees with deterministic execution | Well-foundedness is separate from a uniform bound and computational efficiency |
| Dependent typing, binding and logical relations | Typed contexts, renaming/substitution, elaboration soundness and source/denotation correspondence | Type correctness does not establish availability, secrecy or honest computation |
| Hoare reasoning, frames and module refinement | Outcome-sensitive postconditions, explicit state relations and fact transfer through calls | An interpreted write footprint must cover actual aliases; no full separation logic is claimed |
| Abstract interpretation and dependency analysis | `Means`, sound transfer, conservative loss of facts, checked reuse at the consumer | A finite list of facts is not automatically a complete analysis or a fixpoint theory |
| Staging and memoization | Immutable input binding, delayed acquisition, cache validity and accounted work | Pure preparation laws do not justify caching correlated resource acquisition |
| Relational semantics and information flow | Context-scoped observations, compositional simulation and joint disclosure | Same-program correspondence is weaker than preservation under arbitrary target contexts |
| Probability and coupling | One initialized experiment, persistent resources, reached conditional distributions and justified loss | Marginal equality is not joint equality; iid, correlated and fixed-oracle laws differ |
| Session/choreography and affine-resource methods | Returned-phase composition, supplied endpoint legality and actual one-use ledger transitions | Atomic conformance is not asynchronous progress or distributed custody |
| Reflection, translation validation and data refinement | Accepted certificate implies its exact source-relative claim; native adapters implement their representations | Native reports, proof terms and actual checker execution have different trust boundaries |

A useful abstraction must simplify an actual proof or enable a substantive
second application. When existing methods do not supply a required law, record
the mathematical gap and a discriminating target in the maintained roadmap.
Do not turn the absence of a universal theory into repeated reorganization of
the finite model.

## 8. Maintenance

Maintain one definition for each shared concept. Classify subsequent changes as
relocation, proof/API refactoring or a change in mathematical meaning. A changed
proposition requires examination of its premises, failure cases and consumers.
An import cleanup must not silently weaken a claim. Do not recreate a numbered
provenance system to describe ordinary development.

A new capability enters the library with an actual client, a stated law and an
acceptance condition. Reopen an accepted result for a changed supported behavior,
an affected premise or a counterexample. The [research agenda](design/research-agenda.md)
records broader questions without making all of them prerequisites of this baseline.

Toolchain upgrades are separate from semantic changes. Rebuild supported main and
optional targets, recheck declarations and exact pins, and state evidence for any
changed external assumption. Retired scratch packages need not be ported.

## 9. What the compiler consumes

The [handoff](design/implementation-handoff.md) records each abstraction's source
form, denotation, retained information, legal transformations, lowering relation,
runtime requirements and discriminating checks. Construction choice, roles,
logical algorithms and physical representation are separate design decisions.
The shared `Proc` meaning does not flatten them into one native IR. Native
execution, checked optimization and actual-source correspondence are separate
evidence obligations; the Lean library does not itself prove the compiler and
runtime connection.

## 10. Verification and completion

The maintained package needs the following checks, with targets declared
in the maintained Lake configurations:

- Build all declared library modules, normal tests and external-style API
  examples; a passing small default import must not hide an unbuilt component.
- Enforce module dependency boundaries and inspect declaration dependencies at
  heavy import boundaries. Library imports cannot depend on tests or tooling.
- Audit reached axioms for every supported target, including optional adapters.
  Keep standard extensional/classical assumptions explicit; proof holes and
  additional undeclared axioms fail. This does not certify the kernel itself.
  Audit coverage follows the declared module inventory, including `ZkcArkLib`;
  the optional package runs its own complete declaration audit. Tool wrappers
  are compiled and linked separately; their IO/serialization behavior is not
  proved by the library axiom inventory.
- Exercise meaningful negative cases and premise producers. Generic records
  alone do not count as validated applications or complete checkers.
- Run current-source reproduction on pinned dependencies and a corrected
  toolchain; normal cached development builds remain useful. Record theorem
  checking separately from native checker execution and benchmark results.
- Measure representative imports, elaboration, checker cost and proof size
  when the change affects them. Protocol compile-time generosity does not
  justify accidental dependency or proof-search growth in the library.
- Generate documentation from current declarations and verify source/reference
  links from the distribution with ignored history absent.

Completion means a consumer can import the advertised API, understand its
mathematical contract, instantiate it, run the promised checker and reproduce
the supported proof checks from maintained files alone. It is not measured by
retaining a fixed number of files, eliminating all future research questions,
or claiming to have verified external native cryptography.

## 11. Alternatives and decisions

| Alternative | Decision and reason |
|---|---|
| Rename every research module one-for-one | Reject: preserves accidental dependencies and specialized assumptions under generic names |
| Permanent Compat/Legacy layer | Reject: no identified public compatibility requirement justifies it; it prevents the requested deletion |
| Rewrite every proof from scratch | Reject: reuse correct mathematics while changing its ownership/API; reprove the statements that actually change |
| Make every subject a separate Lake package | Reject initially: one main mathematical library plus a real external-integration boundary gives useful isolation without a version matrix for every area |
| Put ArkLib behind an optional root import only | Reject: imports do not remove a declared package dependency or prevent public type leakage |
| Fully intrinsic proof-carrying source for every property | Use only where constructive typing helps; retain external input and semantic checks for the compiler-facing language |
| Replace Proc with a universal coinductive/distributed calculus now | Retain the finite denotation; extend when an actual promised behavior requires different execution observations or termination semantics |
| Verify all C++/Rust/backend code before using the library | Keep explicit realization contracts and prove concrete boundaries incrementally; current claims state the remaining trust |

## References

[1] [Lean reference: Lake](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/).
Package versus module dependencies and local path requirements. Exact syntax
and supported tooling must match the selected implementation toolchain.

[2] [Lean reference: instance synthesis](https://lean-lang.org/doc/reference/latest/Type-Classes/Instance-Synthesis/).
Basis for distinguishing inferred algebraic structure from explicitly selected
semantic interpretations.

[3] [Mathlib library style](https://leanprover-community.github.io/contribute/style.html).
Guidance for readable declaration APIs, imports, transparency and proof
engineering; these are design inputs, not a new agent workflow.

[4] Siddharth Bhat, Alex Keizer, Chris Hughes, Andrés Goens and Tobias Grosser.
[Verifying Peephole Rewriting In SSA Compiler IRs](https://arxiv.org/abs/2407.03685),
ITP 2024. Basis for evaluating SSA/region and rewrite infrastructure reuse;
no claim of current zkc integration or toolchain compatibility.

[5] [CSLib transition-system simulation implementation](https://github.com/leanprover/cslib/blob/main/Cslib/Foundations/Semantics/LTS/Simulation.lean).
The inspected source declares relational composition and finite trace lifting.
PIR terminal-state and observation adequacy still requires an explicit bridge.

The [theory reference](../docs/theory.md) supplies the primary PL,
compiler and cryptographic literature and its existing application boundaries.

## Families and outer iteration

The finite kernel remains the meaning of each admitted step.
`Source.Family` owns complete invocation ingress and local knowledge;
`Source.Protocol.Family` instantiates scoped counts without copying the grammar.
Both target projections commute with substitution. `Semantics.Iteration` adds
coherent prefixes around finite bodies, preserving interpretation and admission
laws; it does not add unrestricted recursion to stored source. Deployment caps
and buffered publication have separate contracts.
`Probability.Iteration` is a Mathlib-dependent application, while the controller
and typed families stay in the Std-only foundation. These APIs do not provide
runtime-symbolic native carriers or a concrete external proof construction.

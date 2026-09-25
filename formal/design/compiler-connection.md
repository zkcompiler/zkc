# Compiler connection and proof checking

**Target design.** Read the [boundary map](verification-map.md) first. API and
format names below describe responsibilities, not existing exported declarations
or a frozen wire ABI.

## 1. One meaning, several useful representations

Keep the semantic effect tree, typed source, MLIR graph and runtime plan distinct.
`Proc` describes interaction. Typed source exposes finite structure for binding,
substitution and analysis. MLIR provides mutable SSA/region infrastructure for
search and transformation. The executable plan exposes scheduling and contracted
operations in a form with a small interpreter.

This plan is a first supported realization/OIR carrier, not a new independent
protocol semantics or a requirement for every future backend to use one graph.

Use the [source architecture](../DESIGN.md#3-mathematical-objects-and-source-representation):
intrinsically typed local operands and contexts, explicit region arguments and
results, public bounded loops, and separate semantic admission. A field modulus,
index domain, challenge site and backend identifier are not interchangeable
attributes. Unknown semantic operations cannot become harmless opaque nodes by
passing an MLIR structural verifier.

The external source representation must be finite data, without arbitrary host
closures. Source-bound captures are explicit. MLIR import/export is an adapter
to that data; it does not become the mathematical definition merely because it
is convenient to serialize. Generic MLIR side-effect interfaces and conversion
legality are useful implementation mechanisms, but require zkc-specific meaning
for transcript order, disclosure, correlation and failed writes.
[S6–S7](sources.md#s6)

## 2. Source and target must be fixed independently of the producer

The consumer retains the admitted original source and selected policy. It gives
the optimizer an input identity and receives target data and evidence. The
checker obtains the original from that retained input, not from a producer's
claim about what it optimized. Otherwise the producer could validate a correct
transformation of the wrong protocol.

Start with validation of original source against the final supported target
plan. Intermediate rewrite witnesses can make checking efficient, but validation
must account for the whole exported result. Proving an isolated rewrite theorem
does not prove that C++ selected the right operands or applied it in a permitted
context. Translation validation is the established separation between an
optimizing algorithm and a checker of its particular result. [S8](sources.md#s8)

A shared schema can generate declarations, parser scaffolding and diagnostics.
It reduces transcription work, but is not a semantic proof of all generated
consumers. The Lean side decodes the actual bytes or checks a justified relation
to them. During implementation, normalize once and explicitly compare the
result consumed by checking and execution. Hashes support artifact identity;
the theorem concerns the decoded/interpreted objects. Hash collision resistance
and loader behavior remain explicit if identity relies on hashes.

## 3. A certificate is data for an established proposition

The architecture separates five objects:

```text
ClaimPolicy     consumer's relation, observer, supported scope and assumptions
SourceSubject   actual source, binding schema and interpreted module environment
Candidate       target plan proposed by MLIR
Certificate     finite rule instances, intermediate subjects and premise evidence
CheckedResult   accepted conclusion with requirements, or a classified non-result
```

Retain this separation in the first executable interface. `ClaimPolicy` identifies
the relation, observer, supported execution scope and permitted assumptions;
source/candidate identities include their interpreted dependencies. Certificate
constructors select registered, versioned rules with their actual judgments.
The first checker implements a finite supported set and rejects unknown claims
or rules. Later property transport and generated-code evidence extend this
dispatch with sound interpretations; they do not reinterpret an existing
successful local check. Artifact packaging retains the realization kind and
required capabilities described in the [runtime design](../../docs/runtime/design.md#3-artifact-and-checking-boundary).

The producer may choose a candidate and a search strategy. It cannot choose a
weaker observer, replace the field interpretation or omit failed-call effects.
Observer weakening is a separate explicit consumer-approved claim, with its own
monotonicity result where one exists.

A first certificate grammar should have renaming/substitution witnesses,
registered local rule applications, region composition, a finite analysis
invariant, and explicit preparation/reuse decisions. It should not contain
arbitrary Lean source supplied by the optimizer. The trusted checking semantics
interprets rule identifiers and checks all operands, premises and intermediate
subject connections.

The intended checker interface is schematic:

```text
check : Policy → Source → Plan → Certificate → Result

check_sound :
  check policy source plan cert = accepted requirements →
  ∀ binding, Holds requirements binding →
    policy.Rel (denote source binding) (denotePlan plan binding)
```

All dynamic values quantified here are those allowed by the fixed schema and
contracts. A specialization to public configuration can instantiate some of
them; specialization to a runtime secret cannot silently turn a universal
statement into one selected execution.

Reusable compilation certificates should quantify over runtime witnesses and
random choices. They carry public structure and admitted specialization data,
not secret inputs merely to make the checker executable. Runtime binding checks
connect actual values privately to that schema. Any certificate, diagnostic or
identifier that depends on secret data belongs in the existing joint-disclosure
account; its serialization is an observable output, not harmless proof metadata.

Requirements need meanings and actual producers. A declared provider law is
retained as a hypothesis unless connected evidence supplies it. Availability
can be proved statically or guarded at the original semantic point. A certificate
cannot simply assume that a guard which may fail succeeds. The existing
[guarded compilation law](../Zkc/Polynomial/Bilinear/Compilation.lean) is the starting
client for this requirement discipline.

Checking and execution admission are separate consumers of those requirements.
The compiler cannot make a local preservation claim vacuous by adding arbitrary
source-domain assumptions. The policy fixes allowed contract assumptions and
the rules for derived native capacity/progress requirements. Evidence discharges
a premise, an interpreted source-aligned guard establishes it at use, or the
consumer explicitly accepts it as trust. Missing disposition prevents execution
admission even when the conditional theorem was checked successfully. Runtime
guards do not test an arbitrary mathematical provider law.

Build source and direct Plan denotations before optimizer rules. The first
checkable path includes actual decoder and representation connections; it is
not closed by reflexivity on a producer-supplied AST. Registered MLIR lowering
and a minimal native executor then exercise the same path without optimization.
Only after this baseline discriminates wrong bindings, failed-state changes and
changed plans does the first shared pass use it as its integration reference.

Malformed input, unsupported syntax, resource exhaustion, missing evidence,
rejected certificates and established counterexamples have different meanings.
Failing to certify does not establish that a transformation is incorrect. Final
diagnostic codes are an implementation decision; this semantic distinction is
required now.

## 4. Analysis checking instead of reimplementing optimizer search

For an analysis domain `A`, define `Means : A → ConcreteState → Prop`. A candidate
annotates relevant program points with facts. A small checker verifies the entry
facts and every control-flow transfer, join and loop back edge. A sound transfer
lemma turns the checked constraints into an invariant. The producer's fixpoint
strategy need not be part of the trusted theorem. A post-fixpoint suffices for
soundness; the least or most precise solution is a separate optimization claim.
This is the useful abstraction from abstract interpretation. [S9](sources.md#s9)

For zkc, the central transfer is through a contracted stateful call. Its write
frame determines which factor facts remain meaningful. Reuse of prepared data
also needs an identity and dependency argument for the immutable inputs. A local
index equal to another index is not proof that two captured values are the same.
Frame reasoning applies to failed calls as well as successful ones.

Abstract interpretation and Hoare/separation reasoning therefore meet at an
explicit contract: the semantic module owns what can change; the analysis owns
what facts survive that change. It is unnecessary to encode every cache in a
general separation-logic framework initially, but disjointness assumptions must
be proved or supplied by the actual allocator when native aliasing matters.
[S10–S11](sources.md#s10)

The first end-to-end pass is demand reduction plus immutable preparation reuse
around an actual module call and a readiness failure branch. It exercises fact
production, invalidation and continuation. It is more discriminating than a
collection of pure arithmetic rewrite identities.

## 5. Proof replay and efficient checking

Prove each reusable checking rule once. For an individual compilation, generate
finite certificate data and instantiate those theorems. The strongest selected
route supplies a proof of the computed acceptance result that the kernel can
check without admitting native-evaluation axioms. Possible implementations are
kernel reduction for small data or proof reconstruction from a compact checking
derivation for larger data. The latter avoids asking the kernel to rerun every
search step.

An SMT solver, e-graph or synthesis engine may produce witnesses. A solver's
`unsat` response alone is not a Lean theorem. Either replay a supported proof
object with a sound checker, reconstruct a Lean derivation, or explicitly retain
solver/encoding trust in a different assurance mode. A proof-producing tactic
also needs an axiom audit: automation and a restricted trust base are separate
questions. [S5](sources.md#s5)

Do not force certificate size to scale with all producer work. Use shared proof
DAGs and reusable local lemmas with checked references. An imperative/native
implementation of a checker may later be related to its functional specification;
it does not acquire that correspondence just by computing the same results on
fixtures. The checker parser, resource accounting and input binding remain part
of the execution boundary.

Heavy compile-time work is justified where protocol artifacts are reused. Spend
it on specialization, counterexample search, invariant inference and candidate
selection. Keep final checking predictable. Record search time, proof generation,
kernel replay, certificate bytes, peak memory and run time separately. Caching
proof results requires the same source, rules, policy, interpreted configuration
and theorem dependencies; an obsolete cache hit is not evidence.

## 6. Composition and heterogeneous lowering

An implementation relation must support different result and state types. A
schematic deterministic execution relation is:

```text
OutcomeRel valueRel stopRel left.outcome right.outcome
∧ StateRel left.state right.state
∧ observeLeft(left.events) = observeRight(right.events)
```

To compose two boundaries, compose value/state/stop relations existentially and
prove that the observations meet at the same intermediate meaning. To sequence
two programs, prove that every pair of related returned values leads to related
continuations in related states. Terminal outcomes bypass continuations while
retaining their state and events. The existing same-reply execution theorems are
special cases. A general relation alone is not useful until actual decoders,
bindings and callers instantiate these obligations.

Local step simulation may allow invisible target steps, but must exclude
unbounded invisible divergence when the claim promises termination. Conversely,
an observer that ignores allocation does not automatically ignore allocation
failure. Cost or leakage observations require explicit extra components, not
erasure from this relation. Relational verification is the relevant established
method; robust security against foreign contexts requires additional hypotheses.
[S12](sources.md#s12), [S4](sources.md#s4)

The first lowering target is a typed/coarse plan with calls to contracted kernels.
Prove erasure into executable operands and instruction dispatch against it.
Backend selection can happen before validation if its configuration is part of
the checked subject. Selection after validation needs a theorem covering all
allowed implementations of the selected contract.

## 7. Library and engineering boundaries

Use `Compiler.Checking` for certificate meanings, functional checking and
soundness; `Compiler.Lowering` for plan interpretation/erasure; `Source` for
formation and binding; `Realization` for native state and value relations.
Executable command-line decoding and reporting belong in a tool target, not
imports required by every theorem. No stable public API should expose generated
names from an extraction tool.

The first implementation uses the small owned finite typed carrier in
`Zkc.Source`. The bounded Lean-MLIR trials exposed a dependency-porting cost at the selected
Lean pin; they did not establish semantic unsuitability. Reconsider that adapter
when a compatible core supports the same effectful client and a useful rewrite
with less maintenance than the owned API. CSLib remains a candidate for
simulation infrastructure. Verification dialects/xDSL-SMT offer a separate
route for candidate checking and counterexamples; their semantic lowering must
agree with PIR before those results become zkc judgments.
[S13–S16](sources.md#s13)

External tool integration does not need to precede the entire library
migration.

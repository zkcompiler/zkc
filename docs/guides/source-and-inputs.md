# Source formation and input binding

Source adequacy connects authored structure to the computation it denotes.
[Formation](#source-formation-and-elaboration) covers endpoint and elaboration
obligations; [input binding](#source-inputs-scoped-expressions-and-captures)
explains scope, availability, immutable captures and their distinct checks.

## Source formation and elaboration

This guide applies the [program](../spec/language/programs.md), [input](../spec/language/inputs.md)
and [interaction](../spec/language/interaction.md) specifications. Those pages own the
common definitions. [Effectful source](effectful-sources.md) describes domain
frontends; [binding](artifact-binding.md) connects their actual interpretations.

### 1. Source adequacy precedes execution correctness

A correct interpreter can execute the wrong polynomial when its source inputs
are misordered. [PROG-02](../spec/language/programs.md#contexts-and-values)
and [INPUT-01](../spec/profiles/source/named-inputs.md#exact-ordered-binding) therefore retain
positions, sorts and actual values. Domain adequacy must then connect that
binding to the intended mathematical object.

The common finite `Program` can use polynomial queries, group operations or
path checks as its vocabulary. Its control is independent of protocol names.
[PROG-04–05](../spec/language/programs.md#denotation) connect its branches,
accumulators, captures and region composition to the same effectful meaning.
The pure closure frontend shares the endpoint boundary, but is not an alias
for every effectful source or an automatically implemented lowering into `Program`.

There is no global bit order. The flat table takes its first coordinate as the
most significant index bit, while the Merkle reference client reads each path
direction from the least significant bit. One order for both would couple
unrelated objects, and equating them silently would corrupt operands; a
conversion proves which coordinate, child order and value it represents.

Forcing every frontend into the pure fragment would destroy effect structure,
and treating the frontends as aliases would hide a missing source-conversion
theorem; a portable frontend that offers a route into `Program` supplies that
theorem.

### 2. Two routes to an endpoint

[INT-05](../spec/language/interaction.md#endpoint-admission)
admits checked finite syntax or a supplied endpoint with correspondence. A
callback whose type exposes only prover memory is useful in a mathematical
model; it does not inspect the captures of arbitrary Rust or Python code.
Both routes establish actual input access and interaction obligations.

Function-valued continuations in `Proc` support mathematical induction and
dependent replies. They do not define a portable callback format. Likewise,
a finite capture vector needs an actual encoding when serialized.

### 3. Constructor meanings and formation requirements

The common grammar and equations are in [PROG-03–04](../spec/language/programs.md#typed-control).
Admission combines several contracts rather than folding them into typing:

| Feature | Contract to apply |
|---|---|
| Public shapes and loop counts | [Public families](../spec/language/interaction.md#public-families-and-semantic-subjects) and [call bounds](../spec/language/programs.md#structural-call-bounds) |
| Expressions, branches and captures | [Input availability](../spec/language/inputs.md), exact operand binding and the selected branch meaning |
| Calls, sequencing and repetition | [Phase and return conditions](../spec/language/interaction.md#all-reply-conformance), plus [module contracts](contracts.md) |
| Mutable state and live references | [State and module interpretation](contracts.md#state-modules-and-reusable-facts) |
| Coins and shared providers | [Probability experiment](security-properties.md#probability-initialization-and-persistent-providers) in addition to the typed draw |
| Session scheduling and partial delivery | [Atomic sessions](../spec/language/interaction.md#atomic-sessions) and the actual decision boundary |
| Accepted continuation | [Verifier decision, custody and export](accepted-continuations.md) |
| Wire bytes and native values | [Realization correspondence](realization.md) |

A dynamic readiness check has a time of use. Materializing an immutable value
and later resolving a live reference have different meanings; the latter needs
a transition/lifetime law.

### 4. Current concrete elaboration and its context law

[INPUT-06](../spec/profiles/source/expressions.md#issuance-and-actor-admission) specifies
pure closure elaboration. `elaboration_exact` relates successful issuance to
evaluation of the original expanded source inside a fixed continuation.
`admitted_context_related` joins equal issued code/values to related handlers,
retaining the continuation's complete stopped or returned execution.

The theorem fixes the closure, binding plan and continuation. It does not
verify secret source generation, the captures of a different continuation,
its phase safety or a native parser. Admission failure does not execute the
continuation and is not silently reclassified as verifier rejection.

### 5. Erasure, wiring and frontend obligations

Erasure, inlining and specialization need the applicable source-relative
correspondence. Scope erasure has an exact law for its fragment; that is not
a theorem about all MLIR attributes. Removing an unused capture can enlarge
the admission domain even when it preserves executions of already-admitted
inputs. A pass should state which of those domains its theorem covers.

[PROG-09](../spec/profiles/compiler/direct-plan.md#checked-plans)
checks the actual candidate against the retained source. Native resolvers and
backends still connect the selected symbols to their declared mathematical
meanings. Copying an annotation does not supply that connection.

### 6. Formal coverage and joined admission

The [correspondence map](../spec/correspondence/programs.md) lists common
source and input laws. [Binding](artifact-binding.md) points to pure and local-code
instances of the same endpoint contract. [Effectful source](effectful-sources.md)
connects rounds, source selection, installed namespaces, repeated services and
session scheduling. These are separately justified interpretations.

The [source/plan implementation](../compiler/source-plan.md),
[phase checker](../compiler/phase-admission.md) and
[native route](../runtime/reference-execution.md) report their achieved scopes.
The common contracts do not require their present implementation choices.

## Source inputs, scoped expressions and captures

This guide applies [common input binding](../spec/language/inputs.md) and the
[pure expression profile](../spec/profiles/source/expressions.md). [Typed programs](../spec/language/programs.md)
define heterogeneous control; the ring fragment is one concrete frontend.

### 1. Scope and availability are separate

[INPUT-01–02](../spec/profiles/source/named-inputs.md#exact-ordered-binding) distinguish
well-typed references, permitted reads and present values. A future challenge
may have a known type while still being unavailable. The reader preserves
that absence instead of supplying zero. Equality of an actor's input view
includes availability and that actor's private values.

The `bindInputs_exact` law connects successful heterogeneous binding to
the exact ordered supplied records. It says nothing about whether a native
supplier has authenticated those records; that remains the adapter's job.

### 2. Concrete expression syntax and meaning

[INPUT-03](../spec/profiles/source/expressions.md#expression-syntax-and-meaning) specifies the
ring expression fragment. Its dependency summary includes the guard and both
branches of a zero test. This is deliberately conservative: an unavailable
variable in the branch not taken is still refused by this admission policy.

### 3. Intrinsic scope and erasure

[INPUT-04](../spec/profiles/source/expressions.md#substitution-and-intrinsic-scope) connects
checked syntax to variables carrying scope membership. Erasure removes the
membership evidence while preserving exact syntax and evaluation. It cannot
supply a missing input or preserve an unrelated dialect annotation by analogy.

### 4. Explicit captures and the readiness check

[INPUT-05](../spec/profiles/source/expressions.md#finite-closures)
checks every declared capture. For example, a body returning a constant may
ignore a forbidden capture; expanding that body would hide the declaration.
The whole-capture policy still refuses it. `closure_agreement` remains a valid
law about the expanded expression, with that narrower scope.

A liveness analysis could admit more closures, but it changes which requests
are refused, so it changes the admitted domain and is not an optimization of
execution. The declared-capture rule is kept because its refusals are easy to
state and issuance is connected to it. A lazy-input feature would first state
its observation and refusal domain and prove the stronger adequacy law.
Replacing positional binding by a named mapping would likewise specify
duplicates and order, then prove its new adequacy law.

### 5. Binding lifetime, generated code and observations

[INPUT-06–07](../spec/profiles/source/expressions.md#issuance-and-actor-admission)
explain immutable issuance and source selection. Invocation reads the retained
values. A pointer that later sees changed storage needs a live-reference
interpretation, even if its earlier contents were hashed.

A secret-dependent host generator can choose between two dependency-free
literals. Both pass the expression scope checker, while their released source
reveals the choice. Fixed-source agreement does not cover that generator.
Likewise, permission for the prover to read its witness does not authorize
publishing the resulting code/value pair.

### 6. Controls and theory choices

[Source controls](../../formal/Tests/Source.lean) distinguish absent input from
zero, own input from foreign input, dormant dependencies, unused captures,
changed snapshots, reordered values and secret source selection.
[Source-plan controls](../../formal/Tests/SourcePlan.lean) also exercise two
actual fields, invalid operand sorts and positions, and ordered typed binding.

### 7. Coverage and connected interpretations

[Expressions](../../formal/Zkc/Source/Expressions.lean),
[Closures](../../formal/Zkc/Source/Closures.lean) and
[Elaboration](../../formal/Zkc/Source/Elaboration.lean) establish the pure path.
[Typed binding](../../formal/Zkc/Source/InputBinding.lean) and
[local inputs](../../formal/Zkc/Source/LocalInputs.lean) establish the common
heterogeneous path. Their [correspondence map](../spec/correspondence/programs.md)
records exact hypotheses. [Effectful source](effectful-sources.md),
[state and modules](contracts.md#state-modules-and-reusable-facts) and [observations](execution.md#observations-and-refinement)
connect source selection, live references and disclosure at their own boundaries.

# Checked libraries and static components

This profile extends [resolved authoring](authoring.md) with interfaces,
representation-independent local bodies and static linking. It does not add
runtime module dispatch or replace PIR's interaction, operation or property
judgments. [Generic requirements](generic-definitions.md) owns static derivation.

## Subjects and identities

A library identity contains its namespace, name, version and captured resolution.
A declaration additionally has a module path and declaration name. These are
qualified semantic identities; lexical spelling and snapshot-local integer IDs
are not sufficient to identify imported declarations.

Static terms have a checked sort: ordinary type, domain of a specified kind,
natural, association or component. Formation checks root declarations, ordered
constructor actuals and declared associated members. Pure application respects
argument equality. It does not imply injectivity, interchangeability of different
constructors, or equality of representations with equal layouts.

A selection key includes the qualified constructor, ordered static actuals and
captured hidden dependencies. Captured subjects contribute their exact descriptor
content. Repeated pure selection shares that key. An explicit seal contributes
its declaration and enclosing selection: it distinguishes selections without
inventing a new identity whenever checking is replayed. A digest may locate a
cache entry; it is not a replacement for exact identity or conformance evidence.

Importing an interface requires exact agreement on its reached public descriptor
closure and installed contracts. Its own formation judgment retains its canonical
owner environment, including owner-private declarations. The importer need not
reproduce unrelated private declarations to use the public interface.

## Interfaces and abstract checking

An interface declares abstract types and their copy/drop permissions, sorted
associated members and equations, function signatures, requirements and supported
evidence facets. Ports retain source types and role constraints. Signatures retain
preconditions, postconditions and allowed effects. Ordered public parameter
labels are part of the authoring contract, independently of implementation-local
binder names and physical wire layout. Named operands evaluate in authored order
exactly once, then their values are permuted by the checked port bijection.

In the conservative installed-operation profile, every authored primitive carries the
`local` effect allowance, including guards and zero-result calls. Capturing an
operation with an empty effect set refuses. Additional effect labels may restrict
its use; they do not establish a new behavioral law.
Generated ownership operations implement the resource discipline at the lower
level. Their insertion is accounted for by lowering; an empty source effect
allowance does not claim that execution produces no bookkeeping events.
The present effect vocabulary also makes no totality or non-stopping promise.
Explicit terminal stops require no additional label; postconditions apply only
to returning executions. An empty effect set therefore cannot justify removing
or speculating a call whose stopped outcome has not independently been ruled out.

A client is checked using its imported interfaces and captured operation/domain
environment, before private representations or implementation bodies are
available. Only those assumptions justify its body. A concrete implementation
that happens to permit copying cannot justify an abstract copy that its interface
does not promise. A generic component body is checked under its own parameter
bounds, rather than only after a convenient concrete selection.
Component declarations retain their imports, ordinary type bounds and static
requirements independently of method bodies. Conformance checks those obligations
even when a component has no methods or a parameter is unused.

Body operands refer to semantic values and field/static-index paths. Products,
nominal records and fixed arrays retain source structure. Aliases and overlapping
projections refer to the same resource. Usage checks precede flattening and count
uses through calls, construction, projections, discards and returns. Construction
does not create an abstract value without its implementation's authority.
Copy and drop permissions are independent: a copyable, nondroppable value must
be used at least once. The zero-storage resource-unit execution profile admits
only its declared noncopyable, droppable case.
These stronger source permissions are checked before lowering. Portable local
execution is affine: its admission checks are necessary for execution, but do not
by themselves re-establish a library interface's mandatory-use guarantee. The
checked source body and its correspondence evidence must remain attached to that
claim; a standalone executable candidate supplies no such evidence.

Finite variants retain a nominal declaration, its ordered static actuals, and
the ordered alternatives' payload types. A constructor owns only the selected
payload. It does not construct, initialize or dispose of any inactive payload.
The variant permits copying or dropping only when every alternative permits
that action. Knowing which constructor was used does not weaken the declared
permission. An exhaustive local match consumes the scrutinee and transfers its
explicit captures once. Each alternative is checked in an isolated scope with
its payload and captures; only continuing alternatives establish result types
and facts at the join. A stopped alternative has no continuation.
A checked Boolean conditional uses the same isolated-region contract. Its
condition is role-local logical `bool`; its `then` and `else` arms receive only
the explicit captures, transferred once at the boundary. Copy/drop permissions,
roles, continuing-arm results and common established facts are checked before
selecting an implementation. The condition itself is not a protocol branch.

An exhaustive match or conditional with no continuing arm and no results terminates its own
region. Its lowered block may contain an unreachable final halt solely to satisfy
the carrier's explicit-terminator invariant; it must never invent a returned value.
When component selection makes every arm of an already-checked join terminal,
the linker removes its unreachable results and continuation. A source-authored
all-stopping join must declare no results (`library-stop`). Callee-first
normalization preserves each selected stopping call and its effects, origin and
reason. A transitive stopping member
cannot fabricate the outputs promised by its interface. A mixed join retains
its continuing arm and stops when its terminal arm is selected.

A recoverable error is an ordinary alternative returned by a component. It is
different from a stopped execution. Matching an error cannot catch a rejection,
abort, refusal, incompleteness or resource exhaustion from the computation that
would have produced the value. The stopped computation retains its reached
state and observations, and creates no result value.

Bounded array traversal consumes each semantic element once and threads explicit
carried state. The generic body is checked before a symbolic count or private
element representation is selected. Invariant captures must be duplicable;
other state crosses the iteration through its carried ports. Zero elements
return the initial state without entering the body. Static expansion after
linking is bounded and preserves element order; it does not authorize dynamic
indexing of affine values, borrowing, or duplicating an element.

The checked result owns the exact body, imports, environment and derived
obligations that justify it. An immutable handle, rather than a mutable checked
flag, grants access to subsequent linking. Moving source locations alone changes
diagnostic provenance, not semantic identity. Changed assumptions require a new
check; a private implementation edit need not invalidate an otherwise identical
abstract client, but invalidates dependent linking results.

## Conformance and coherent linking

Linking supplies each imported component with an implementation of the exact
interface captured by the client. This condition also applies to imports used
inside selected component bodies. Conformance checks:

- The declared member set, associated sorts and equations.
- Source types and roles of inputs and results after complete substitution.
- Promised copy/drop permissions of private representations.
- Preconditions no stronger, postconditions no weaker, and allowed effects no
  broader than the interface contract, using the installed derivation rules.
- Required evidence facets and the captured environments on which checking rests.

Substitution covers static and ordinary type parameters, associated members,
dimensions, body values, call arguments, signatures and requirements. Unresolved
terms cannot cross the closed PIR boundary through an unchecked string spelling.
Component parameters, including `Self`, resolve through component bindings and
dependencies. The ordinary static-substitution map cannot rebind them: equality
checking and member dispatch must observe the same selected component.

A call may also supply a concrete component directly as a generic client's
component actual, as `Client::<BoolCell>(x)` does. The call is then a link at
its site: the component is checked for conformance as a declared link's is, its
selection takes part in the same coherence checks, and the linked
implementation becomes a dependency of the caller.

The linked dependency graph has one coherent implementation per selected key.
A diamond may share the same selection; different bodies for that key refuse,
with both dependency paths retained. Cyclic selection and exceeded construction
budgets refuse. Linked identities include implementation bodies, substitutions
and transitive dependencies, separately from abstract interface identity.
The client parameter-to-selection map participates in exact linked identity.
Combining independently linked clients preserves the same normalized-selection
and hidden-capture coherence checks as linking them in one dependency graph.

Evidence has an identified subject, owner/version, status and explanation.
Unavailable optional evidence remains unavailable. Unsupported required evidence
blocks linking. Matching an interface does not establish cryptographic soundness,
zero knowledge or behavioral equivalence of two implementations.

## Validated external preparation

An external adapter captures immutable material against an independently chosen
expected subject. An imported relation's canonical normalized descriptor, its
public/private layout, a setup's exact expected material, and a preparation's
encoding convention are distinct parts of that subject. A path, a candidate's
own claimed identity, or a digest alone cannot establish applicability. Static
association identity records the subject; it establishes no checked predicate.

Successful preparation retains the actual checked material and the particular
facts established by its validator. The consumer checks that these facts apply
to its exact selected subject, input ports and invocation. Reusing a checked
setup across relations is valid for relation-independent setup facts. An index
derived from a relation remains tied to that relation, its dimensions, encoding
and padding; changing the relation requires checking the new index.

Checked facts, explicitly accepted premises and unavailable evidence remain
separate. A key decoder may check canonical encodings and subgroup membership
without establishing honest setup generation or that every query encodes the
intended relation. Neither an interface declaration nor successful parsing can
upgrade those omissions into facts. Missing required premises refuse before
execution; malformed data, subject mismatch, unavailable checks and exhausted
resource budgets retain distinct diagnostics. Runtime satisfaction checks remain
part of the protocol when preparation has not established satisfaction.

The concrete native profile uses exact canonical R1CS descriptors. Groth16
checks relation dimensions and A/B query correspondence, expected verification
key material, key shape/domain and assignment layout/public prefix. It does not
establish C/IC/H derivation, query consistency, ceremony or native cryptographic
correctness. Decoder checks are not an independent proof of the decoder.

The PCS index profile injectively encodes BN254 coefficients as integers in the
larger BLS12-381 scalar field, in row-major A/B/C tables padded with zeroes to the
selected setup capacity. This is not a field homomorphism. A subset-sum transform
constructs evaluations of that coefficient polynomial on the Boolean cube;
commit/open/check use those evaluations. The exact encoding subject remains with
the checked index and committed result, including the relation's public partition
which the polynomial coefficients alone do not distinguish. A consuming protocol
must bind that subject in its authenticated statement. Raw commitments do not
prove that binding. PCS commitment requires explicit acceptance of basis
consistency, ceremony and native-crypto premises, without converting them into
checked facts.

An index larger than the independently selected setup is a subject/capacity
mismatch; exceeding a caller's checking budget is a resource failure. Cell limits
bound padded tables, not total transient allocator use. Expected configuration
must come from the application/compiler's authenticated configuration: these APIs
do not authenticate the caller's choice of expectation.

## Representation and execution

Representation planning follows abstract checking and coherent linking. It maps
typed values and semantic paths to concrete logical leaves. Distinct source types
may have the same layout; this does not authorize substituting one for another.
Member calls become statically resolved local calls. The resulting common PIR
still undergoes its own independent admission and participant projection.

An empty private representation of a nonduplicable value retains a nominal
[resource-unit port](../../domains/values.md#logical-resource-units) until its
usage has been represented. Empty physical storage does not erase ownership.
Creation, transfer and disposal remain explicit logical operations; they assert
no cryptographic predicate. Effectful calls with no result leaves remain calls,
including guards that may stop before resource creation. Lowering preserves call
order and stopped outcomes.

Fixed participant constraints require an execution representation that retains
them. A role-free local function carrier cannot silently erase a fixed role;
such lowering must retain the constraint through an appropriate owner or refuse.

Every common carrier this profile emits is admitted independently of the
frontend; its consumers need not receive frontend interfaces or generic terms
that have already been resolved. Requirement certificate replay establishes its
exact derivability proposition, not a protocol security theorem.

## Checked source helpers and lexical traversal

A source helper target carries its exact formed callable, static substitution,
public signature and checked body dependency. Its signature is available while
checking callers abstractly; executable linking additionally checks the exact
reachable bodies. The graph must be acyclic and work-bounded. An unimplemented
signature cannot discharge executable linking. A helper is never admitted as a
trusted primitive merely to make a source call convenient.

Lexical `map` and ordered `fold` use the same finite array-traversal judgment.
Map returns one collected element per input element; fold threads explicit state.
An empty map retains its result element type and returns the empty array. An empty
fold returns its initial state. Each step preserves ordered effects and terminal
stops, with no recovery or fabricated output after a stopped step. Free places
are captured in first-use order, deduplicated by resolved value/path. Repeated
captures must satisfy the existing copy rule; source inference does not infer
communication or replace explicit carried affine state.

Structured diagnostics may retain an exact declaration, imported interface,
selected component or unsatisfied obligation supplied by its checker. A missing
or resource-exhausted judgment remains unavailable. Unused-local warnings are
separate from acceptance dependence and cryptographic property judgments.

A closed link also captures the caller environment needed by its selected static
actuals. This supplies exact association/domain declarations absent from an
imported generic owner's context. It does not recheck that owner's body under
caller assumptions. Merging link environments checks repeated declarations for
exact content agreement; an equal locator alone is insufficient.

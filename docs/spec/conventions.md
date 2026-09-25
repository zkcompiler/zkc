# Conventions

This specification defines the mathematical model selected by
[docs](../README.md). A definition applies within its stated parameter
domain and assumptions. A profile specializes that model by fixing additional
operands or restrictions.

## Mathematical notation

`Type` denotes a mathematical type, `Prop` a proposition, and `Nat` the natural
numbers including zero. Types are not assumed finite or inhabited unless stated.
`Fin n` is the type of natural positions `i` with `i < n`.
Functions are total on their declared domains. A partial operation represents
failure explicitly in its result type.

`A → B` is the type of functions from `A` to `B`. In a dependent function type
`(x : A) → B x`, the result type depends on the argument. `A × B` is a product;
`A + B` is a disjoint sum whose injections are `inl` and `inr`. Records have
named fields; tuple notation can abbreviate a record when its field order is
specified. `Unit` has the single value `()`; `Bool` has `false` and `true`.

`List A` consists of finite ordered lists. `[]` is the empty list, `[a]` a
singleton, `a :: xs` prepends an element, and `xs ++ ys` concatenates lists.
`map f` applies `f` to each element. `flatMap f` applies a list-valued `f` and
concatenates its results in input order. `length xs` counts list elements.
Positions and repeated occurrences are retained unless a definition explicitly
uses a set or a quotient.

`Option A` has constructors `none` and `some(a : A)`. `Except D A` has
constructors `error(d : D)` and `ok(a : A)`. These are data types; an error value
stops an enclosing execution only if that execution's definition makes it do so.

For a decidable proposition `P`, `decide(P) : Bool` is `true` exactly when
`P` holds. A proposition without a stated decision procedure is not implicitly
an executable Boolean test.

Equations hold for all well-typed operands under the premises stated with
them. A displayed `:=` defines a term or predicate. `∀` and `∃` denote universal
and existential quantification. Equality is equality of the specified
mathematical objects; serialization, hashes and representation relations do not
replace it without a separate law.

## Definitions and requirements

Definitions, formation rules, semantic equations and stated requirements are
normative. A derived law is a consequence under its displayed premises, not an
extra assumption available without them. A paragraph marked *Note* or *Example*
is informative.

MUST and MUST NOT state requirements on their named subjects. MAY permits a
choice within the surrounding requirements. Ordinary declarative sentences also
define the model; they do not need a requirement keyword.

Legacy clause identifiers such as `CORE-03` are documentation references. They
are not operation tags, diagnostic codes, artifact revisions or content hashes.
The [correspondence maps](correspondence/core.md) give their
definition destinations. A semantic amendment records its rationale and the
affected correspondence; an identifier alone does not pin a theorem to source
bytes.

## Execution envelope

An admitted endpoint is specified at public parameters. Its body is
[well-founded](core/execution.md#bodies) and has a
[public interface-call bound](core/execution.md#uniform-call-bounds), uniform
over every declared reply. Actual replies may select shorter paths. Public
parameters, public invocation inputs and private inputs have distinct roles in
[source admission](language/interaction.md#public-families-and-semantic-subjects).

The model supports typed local computation and calls, stateful modules,
explicit failure, probabilistic providers and atomic session interleavings.
These features acquire meaning from their applicable contracts. A new operation
signature alone does not establish locality, independence, provider progress or
protocol security.

An [outer controller](core/iteration.md) may iterate finite bodies without a
finite global horizon. Its prefixes, termination claim and selected deployment
cap are distinct from bounded endpoint admission.

Unrestricted recursion inside stored source, general asynchronous delivery, mid-action reentrancy,
adaptive corruption and weak-memory concurrency have no implicit interpretation
in this envelope. An extension specifies the additional state, transitions,
observations and laws that its consumers require. The
[call boundary](core/execution.md#call-boundary) and public call bound establish
neither native termination nor asymptotic computational efficiency.

## Conformance claims

A conformance claim identifies its subject, interpretation, applicable
definitions, initial-state and input conditions, observation and supporting
correspondence. A subset claim states its bounds and omissions. Behavior outside
that subset does not silently become successful execution.

A compiler claim identifies its source vocabulary, target representation,
operation interpretations and covered input domain. Each claimed pass and
lowering supplies its applicable correspondence. Source typing or structural
IR verification alone establishes neither algebraic optimization nor phase
admission, domain adequacy or native correctness.

The [direct logical plan](profiles/compiler/direct-plan.md#typed-plans) is one
profile. Other representations, including a shared carrier, are permitted when
their semantic relation is established. MLIR, Rust and Lean module layouts do
not determine the specification's abstraction boundaries.

A realization claim MUST identify the actual implementation and build, its
relation, input domain, observer and trusted boundaries. It MUST distinguish
kernel proof replay, trusted executable checking, independent differential
evidence and declared assumptions. A mathematical simulation establishes its
mathematical adapters; a claim about native parsing, FFI or allocation supplies
the corresponding connection to those actual operations.

Differential controls used for a realization claim MUST exercise the actual
retained source and candidate data and compare complete related results,
including negative cases. Passing those controls does not establish a universal
native theorem or a protocol-security bound.

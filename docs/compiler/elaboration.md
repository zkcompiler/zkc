# Authoring syntax and elaboration

This page explains how source notation maps to explicit common PIR and why
certain distinctions remain written. The [source reference](../language/reference.md)
owns the accepted grammar; [source analysis](frontend.md) owns retained
types and queries, and [projects](../language/projects.md) owns imports and visibility.

## 1. Syntax choices

Use Rust's familiar function, binding, path and bound conventions where meanings
align. Keep zkc-specific participant and protocol constructs. Explicit returns and tail-expression returns are both supported. Nested calls,
products and arithmetic expressions retain their source types before lowering.
[Data forms](../language/data.md) explains operators.

The [source reference](../language/reference.md) contains the maintained
`Twice`/`Four` example. Use `snake_case` for new functions and values and
`PascalCase` for types and contracts. Renaming an existing declaration can affect
artifact identity and is not a spelling-only change. A quoted nominal root
followed by `::` is zkc notation; it does not imply a domain-import mechanism.

### Calls and result bindings

| Surface | Common result |
|---|---|
| `let y = Helper(x);` | One `AlgorithmCall` with one output. |
| `let (a, b) = Operation(x);` | One operation with two ordered outputs. |
| `control::require(ok);` | Zero-result operation; do not erase the guard. |
| `return x;` / `return (x, y);` / `return;` | One, two, or zero returned values. |
| `local P: let y = Helper(x);` | Same role-owned `LocalCall`, with explicit owner. |
| `local P: Check(x);` | Zero-result role-owned call. |
| `invoke child(a) -> (b);` | Existing explicit subprotocol call; unchanged. |

Resolve names against a complete declaration index, including forward references.
Do not select targets by trying a function and then silently falling back to an
operation after a type error. Reject duplicate declarations with both
locations; qualified primitive and exact helper names disambiguate call categories. Keep primitive and helper effects/call boundaries intact.
No frontend inlining is introduced.

Bare call statements are allowed only when the declared result arity is zero.
They do not discard nonzero results. No wildcard binding or automatic resource
cleanup is added. Affine resources remain subject to their existing contracts;
this design does not pretend that affine means every result must be used.

Source products are first-class values, including unit, singleton and nested
products. Destructuring and numbered projections retain source typing; common
PIR receives their ordered leaves. Ordinary `let` bindings are immutable.
Bounded local control additionally supports `let mut` through region elaboration.
See [products and placement](../language/values.md#products-local-blocks-and-distributed-outputs)
and [local control](../language/reference.md#collections-and-structured-local-control).
No implicit resource copies or reference semantics are introduced.

### Static arguments, attributes and paths

```text
let y = Twice::<F>(x);                       // explicit static argument
let first = vector::at::<F>(xs) attributes (0);
let one: F::Element = field::constant() attributes (1);
```

`::<...>` always supplies static parameters. `attributes (...)` always supplies
the operation's existing ordered attributes, including in an ordinary bound
function. Neither form is an ordinary runtime argument list. Attribute names and
named-call overloading are not supported. Runtime arithmetic
expressions and the bounded static evaluator are described in the
[source reference](../language/reference.md) and [named static constants](../language/families.md#named-static-constants).
Natural tokens in the example above elaborate to the existing attribute strings;
existing field literal checking/reduction rules remain authoritative.

Map registered operation paths such as `field::add` to the existing exact
contract key `field.add` through a checked frontend mapping. Do not replace dots
globally: `bls12-381.fr`, schema names, user symbols and implementation identities
are opaque identities. Installed operation paths and project imports have distinct resolution rules. Preserve
quoted exact names for low-level records. Qualified calls select installed operations; exact names prefer declared
helpers/configurations before an installed operation fallback in generic bodies.
Named-call resolution is independent of argument types. Operators select from
the [fixed operand-type table](../language/data.md#4-operators). Quoting a nominal term escapes its
lexical spelling; it does not create a new nominal-term grammar. See the
[source reference](../language/reference.md) for lookup and projection rules.

## 2. Logical types and bounds

The current `constructor:domain@representation` carrier remains unchanged. A
readable type elaborates to that logical constructor/domain pair; physical
representations are still selected later.

| Authoring type | Existing logical meaning |
|---|---|
| `F::Element` with field-sorted `F` | `field:F` |
| `G::Element` with group-sorted `G` | `group:G` |
| `G::Scalar::Element` | `field:G.Scalar` |
| `E::BaseField::Element` | `field:E.BaseField` |
| `Vector<F::Element>` | `vector:F` |
| `Vector<G::Element>` | `groups:G` |
| `Matrix<F::Element>` | `matrix:F` |
| `Polynomial<F>` | `polynomial:F`, the current univariate polynomial type |
| `Rng<F>` / `Nonce<F>` | Existing affine randomness/nonce types |

The finite constructor table covers ordinary logical constructors; element,
vector and matrix forms are resolved centrally by the elaborator and printer.
Unsupported nesting such as `Vector<Vector<F::Element>>` is refused. These are
not arbitrary Rust generic types or backend associated types. `F::Element`
preserves nominal `F`; sharing machine representation never makes fields equal.
Do not guess whether an unconstrained `D::Element` is field- or group-valued.

### Bounds must not strengthen a contract accidentally

The bound `<F: Field>` means the Field capability bound, with its parameter
sort determined from the existing vocabulary. It emits exactly the explicit
`Field(F)` assumption. `<F: TwoAdicField>` emits `TwoAdicField(F)` and relies on
the existing implication for `Field(F)`; it does not add another assumption.

```text
fn Transform<F: TwoAdicField>(xs: Vector<F::Element>) -> Vector<F::Element> {
  // Body obligations must follow from TwoAdicField(F).
}

fn Respond<G: ScalarAction>(x: G::Scalar::Element) -> G::Scalar::Element
where
  G::Scalar: Field
{
  return x;
}
```

`where` is for static capabilities over already declared terms. It is not a
runtime guard or an arbitrary theorem prover. Reuse the installed requirement
engine for entailment; do not synthesize laws from successful executions.
The frontend must not infer the public promise from the body.

The explicit kind-only escape is
`<F: domain Field>`: a field-sorted nominal parameter with **no Field(F)
assumption**. This is a kind annotation, not a domain definition or registry
extension. It is necessary for weaker contracts, unused static parameters and
faithful low-level printing. For example:

```text
fn Identity<F: domain Field>(x: F::Element) -> F::Element {
  return x;
}
```

Do not change this interface into `F: Field` merely for prettier output. The
existing sorted common model already expresses the distinction. The additional
surface escape makes it visible rather than requiring a new semantic concept.

Keep an explicit `requires (...)` clause for existing ordered multi-argument and
equality predicates that cannot be represented faithfully by unary bounds. It is
a lower-level contract form, not a second inference engine. Expand header bounds,
then `where` predicates, then explicit predicates in documented source order;
never reorder/deduplicate stored assumptions as an incidental formatting step.
The common printer can use kind-only parameters plus explicit requirements to
preserve the original ordered interface exactly.

No inferred missing domain declarations, new implication rules, or `impl` blocks
belong here. Using Rust-like bounds does not claim Rust's complete trait system.

## 3. Bounded inference

Use synthesis from operands and checking against an optional local result
annotation. Public signatures stay written. First resolve the callee and its
signature; then solve static argument holes. No overload search or exploration
of the installed catalog participates in choosing mathematical meaning.

For a resolved signature `forall d. (T1(d), ..., Tn(d)) -> U(d)`, match operand
types and any explicit result annotation to produce constraints for missing `d`.
Instantiate only if each missing parameter has a unique determined nominal term
under the caller's established equalities. Among constraint-provided equivalent
spellings choose fewest projections, then lexical order; explicit arguments retain
the selected term. This is not canonicalization of arbitrary programs. Submit the completed call to existing
sort, signature, requirement and affine-use checking. A syntactically inferred
substitution is not a proof of the operation's requirements.

Inference is deliberately bounded:

- Solve direct domain occurrences under known type constructors and explicit
  static arguments. Use expected types from `let x: T`, including a complete
  annotation on a flat result tuple.
- Preserve already known associated projections and check their equalities.
  **Do not invert associated members.** `G.Scalar = F` does not identify `G`.
- A body parameter or configuration residual parameter remains a symbolic term;
  do not specialize it merely because one installed domain currently fits.
- Do not invent domain-dependent conversions, embeddings, codecs, PCS choices,
  field sizes, proof parameters or physical implementations.
- Do not propagate guesses backwards through arbitrary later statements. A
  nullary producer with no annotation needs explicit static arguments.
- Preserve current resource/size limits and bound inference work. Reject
  unresolved and contradictory constraints with actionable diagnostics.

Examples:

```text
let y = field::add(x, x);                       // F follows from x
let z = Twice(y);                              // residual F follows from y
let one: F::Element = field::constant() attributes (1);
let other = field::constant::<F>() attributes (1);
```

In contrast, do not infer a group for a helper whose only input is an element of
`G::Scalar`; require `Helper::<G>(scalar)`. Do not convert a base-field vector to
an extension-field vector to make a call typecheck; preserve `vector::embed`.
Missing `PrimeField(F)` is a requirement failure, not permission to add it to the
caller or choose a prime-field backend.

Operation outputs and message receives have inferred types. Omitted static
arguments use the bounded reconstruction above; they are a separate inference
question from runtime result typing.

## 4. Boundaries retained

Keep `local ROLE`, `message`, `invoke`, explicit role mappings, public counted
loops and carried resource values. Local code can fail or draw randomness;
`local` does not assert purity. Named schemas remain part of communication and
transcript structure, not aliases for local variables. No inferred public input
agreement, secret declassification, commitment insertion or transcript absorption
is introduced.

Keep optional user sites and existing occurrence generation. Assign a site once
to each authored call/action before semantic elaboration; resolving a helper
must not add another site. Never derive a cryptographic label from pretty-printed
type syntax, a diagnostic offset or a renamed temporary.

Keep `configure` for protocol-local uses of generic functions. Removing it by
inventing a hidden configuration currently changes the common-source identity
surface. Helper applications can still call partial configurations and infer
their residual static arguments. No new configuration carrier is proposed.

Generic term scopes contain parameters and their projections, not closed catalog
identities. Concrete associated projections normalize at configuration/type
boundaries. Requirements keep their ordered symbolic terms and are validated at
their declaration. Keep ordinary and zero-parameter generic function categories.
Do not make the presence of an operation, or changing its spelling, silently
switch the declaration's category. Empty `<>` remains a documented current
limitation until that separate common-source seam is redesigned.

## 5. Engineering architecture

```text
captured source files and relation assets
    -> syntax tree and bounded diagnostics
    -> project resolution and typed source analysis
    -> static selection and checked common lowering
    -> common source admission
    -> construction, MLIR projection and physical lowering

JSON / programmatic common source -> common source admission
```

The source model retains declaration identity, nominal products, static terms
and body plans that common PIR deliberately erases. It is not a second protocol
execution semantics. The [frontend implementation map](frontend.md#engineering-boundaries-and-assurance)
owns the module responsibilities. [Projects](../language/projects.md) owns source
capture and visibility; [the common model](source-model.md) owns its independent
checking boundary.

Unresolved syntax must not be represented by sentinel common operations. The
syntax, checked source model and portable source each have their own validity
conditions. No formatter or inspection query replaces admission, and authoring
conveniences do not confer new logical-operation support.

### Tools and diagnostics

- Text formatting parses syntax and preserves comments without requiring name
  resolution, capability discharge or a backend. Unknown names remain editable.
- `protocol-source` emits only a fully elaborated, admitted common source.
  Failed inference cannot leak incomplete common records to MLIR/Rust/Lean.
- `protocol-parse` returns tagged syntax inspection, not common-source JSON or
  admissibility evidence. `protocol-source` is the checked interchange boundary.
- Preserve existing common-source JSON input and typed builders. They do not
  need to pass through the authoring syntax tree.
- Inspection shows resolved target kind, inferred static arguments,
  result types and the source of each requirement. Keep explicit common output
  available for debugging, including sites and exact ordered requirements.
- Errors identify the call, conflicting operand/annotation, candidate signature
  and a suggested explicit argument. Do not report a missing `<F>` only at the
  enclosing function's first token.

Formatting and common printing remain distinct: formatting preserves authored
tokens/comments; common printing renders an admitted representation and may
choose explicit rather than inferred forms. Both must have stated round-trip
properties. Supporting inference does not require an IDE/LSP project now.

## 6. Preservation and implementation acceptance

For spelling-only changes, require identical encoded common records, excluding
diagnostic spans. For inferred calls, compare with a separately authored explicit
source carrying the same substitution, assumptions, sites and declaration names.
Do not treat equal terminal results as sufficient evidence of equal transcripts.

Assumption strengthening, category conversion (`Function`/`GenericFunction`),
configuration insertion or symbol renaming is **not** spelling-only. Keep those
out or report the deliberate identity change separately. A normalized artifact
profile does not normalize arbitrary declaration/configuration/schema changes.

Required checks for the implementation:

1. Parser/formatter: comments, forward references, zero/single/multiple results,
   nested type/path delimiters, quoting, incomplete/malformed syntax and budgets.
2. Elaboration: explicit/inferred equivalence, partial configuration arity,
   nullary ambiguity, associated-member non-inversion, conflicting domains,
   weak kind-only contracts, stronger helper requirements and unused parameters.
3. Resources/control: nonce/RNG reuse still refused; zero-result guards retained;
   no hidden conversion, reordering, resource use or new occurrence.
4. Families: generic PCS openings; DLEQ/group scalars and nonces; AIR base/extension
   embeddings and oracle queries; confidential-transaction composition; three-role
   relay; nested/zero public loops; declaration-only interfaces.
5. Pipeline: common-source equality, MLIR import/projection, independent Lean
   checks, selected Rust differential executions and exact constructed-source or
   artifact-identity comparisons where claimed. Existing consumer proofs are not
   a proof of the native elaborator.
6. Source consumers: maintained examples, tests, documentation and generators
   use the accepted notation. The BLS convenience profiles are current syntax;
   their defaults resolve before common admission, with no profile interpreter
   in the executable carrier.

These controls cover the implemented elaboration boundaries. They do not prove
the compiler or establish unrestricted inference, dynamic dispatch or a general
package resolver. Exact source dependencies are covered by the project profile.

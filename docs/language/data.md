# Authoring data forms: bundles, structs, operators and checked structs

All four forms are authoring syntax of `.pir` text. Elaboration rewrites them
into the existing common-source records after retaining their nominal types and
resolved uses in [source analysis](../compiler/frontend.md). The portable JSON
form and every consumer of it are unchanged. The accepted
notation is summarized in the [source reference](reference.md).

## 1. Common rules

1. **No trace.** `protocol-source` emits only existing records. A source written
   with these forms and a separately authored source in the expanded notation
   produce identical encoded common records, spans excluded. This is the
   acceptance test for every rewriting rule below.
2. **Bottom-up, no search.** Every rule is decided from declarations and from
   operand types that are already known. No rule tries one interpretation and
   falls back to another after a failure.
3. **Order and effects.** Operands and field initializers are evaluated once,
   left to right in written order, exactly as nested calls already are. A
   rewriting never duplicates, reorders or drops an operation, and introduces
   no operation of its own.
4. **Declaration ownership.** A bundle or struct belongs to its declaring
   source module. Local declarations may be referenced before their position;
   cross-file lookup follows [project visibility](projects.md). Installed
   type notation resolves through imports from its installed owner.

## 2. Constraint bundles

```text
bundle PairingArithmetic(F) = (
  ScalarAction(F::PairingG1), ScalarAction(F::PairingG2),
  F::PairingG1::Scalar == F, F::PairingG2::Scalar == F
);
fn Verify<F: PairingField>(...) -> bool requires (PairingArithmetic(F)) { ... }
```

A bundle names an ordered list of requirements over its parameters. It is a
macro: it has no identity, cannot be asserted or implemented, and adds no
assumption. A use inside `requires (...)` is replaced, at that position, by the
bundle's requirements in declared order with arguments substituted for
parameters. A bundle body may use other bundles; expansion is recursive.
Duplicates are kept, as the existing requirement order rule already keeps them.
The stored requirements are therefore exactly what the author would have
written by hand, and the existing checker sees nothing new. An equality
requirement is written `A == B` in any requirement list, as in a `where` clause;
it stores the common `=` predicate over both terms.

| Refusal | Code |
|---|---|
| A bundle name equal to an installed predicate, to `=`, or to another declaration | `source-bundle-name` |
| A body term not rooted at a bundle parameter | `source-bundle-term`; an unknown root first fails resolution with `source-name-unresolved` |
| A use with the wrong number of arguments | `source-bundle-arity` |
| A bundle that reaches itself, or nesting deeper than 64 | `source-bundle-cycle` |
| An expansion beyond the requirement checker's budget of 1024 | `requirements-limit` |

A requirement produced by expansion carries the location of the use, and a
diagnostic about it names the bundle. A use is written like a predicate in
`requires (...)`, or as `where T: Bundle` for a bundle of one parameter. A
header bound names a capability, which also fixes the parameter's sort; a
bundle has no sort and is refused there (`source-bound`).

## 3. Structs

```text
use zkc::algebra::Vector;
struct VerifyingKey<F: domain Field> {
  input_query: Vector<F::PairingG1::Element>,
  alpha: F::PairingG1::Element,
  beta: F::PairingG2::Element
}

let vk = VerifyingKey{ input_query: q, alpha: a, beta: b };
let x = vk.alpha;
```

A declaration lists named, typed fields. A field type is a logical type or
another struct; the struct graph is acyclic, at most 64 deep, and a struct has
at most 4096 leaves. Static parameters use the kind-only form `F: domain Sort`.
A struct records no capability assumption, so a capability bound on a struct
parameter is refused (`source-struct-bound`) instead of being dropped silently.
Capabilities remain promises of the functions that use the struct.

Declarations use `struct Pair { left: T, right: T }`; construction uses
`Pair { left: x, right: y }` or field shorthand. Parenthesized declarations and
keyed parenthesized construction are rejected. Named runtime call arguments
use `:`, while static configuration bindings use `=`.

**Flattening.** Records keep nominal identity and field structure until checked.
Lowering then lays out fields in declaration order, recursively expanding nested
records. Internal leaf names such as `vk.alpha` are common-carrier data, not
legal ordinary binders or an alternative interpretation of source punctuation.
A source `vk.alpha` is a typed field projection and emits no operation merely
for selecting a structural leaf.

**Construction.** `Name { field: expr, ... }` names every field exactly once, in
any order. Initializers evaluate once in written order; leaves are then arranged
in declaration order. Static arguments are inferred under existing rules or
written as `Name::<F> { ... }`. Qualified heads such as `types::Name { ... }`
use the same constructor resolver and retain visibility, nominal compatibility
and restricted-constructor authority. Existing applied generic record checker
limits remain. Nullary structs are refused.

**Use.** A struct value may be passed where a parameter of the same struct and
equal static arguments is declared, returned, bound with `let`, and read by
field. Struct identity is nominal: two structs with equal fields are different
types. `let mut`, assignment and messages refuse struct values
(`source-struct-mutable`, `source-struct-message`); a message names a schema
that is part of transcript identity, so its payload stays explicit. Operators
take single values.

**Affine fields.** A leaf keeps its own type, so an affine leaf is checked by
the existing affine rule on its own name. Reading `s.coins` uses that leaf;
passing `s` uses every leaf. A second use of a consumed leaf, directly or
through the whole struct, is the existing reuse refusal.

**Protocol bodies.** Struct types are accepted for protocol inputs and outputs,
for the results of `local` calls, for `invoke` arguments and results, and for
`carry`, loop outputs, `yield` and `return`. A protocol input
`P key: ProvingKey<"bn254.fr">` is owned by `P` leaf by leaf. The frontend
tracks which protocol-level names are struct values and expands them at each
use; all other protocol typing stays with common admission. An entry protocol
with struct inputs receives host inputs under the leaf names, for example
`key.alpha`.

| Refusal | Code |
|---|---|
| Unknown struct, or wrong number of static arguments | `source-type`, `source-type-arity` |
| Duplicate, missing or unknown field in a declaration or construction | `source-struct-field` |
| Cyclic, too deep or too large struct | `source-struct-cycle`, `source-struct-limit` |
| Capability bound on a struct parameter | `source-struct-bound` |
| A struct value where a single value is required, or the converse | `source-struct-value` |
| A value of a different struct, or different static arguments | `source-struct-mismatch` |
| Mutable binding, assignment or message payload | `source-struct-mutable`, `source-struct-message` |

## 4. Operators

With the relevant operations imported, for example `use zkc::{algebra, curve};`:

```text
let a = alpha + linear_a + delta_g1 * r;
let blinded = c + -(delta_g1 * (r * s));
```

An operator selects either an installed operation binding or a checked ordinary
function. Installed bindings live beside the logical contract declarations in
[`Contracts/Declarations`](../../compiler/include/zkc/Contracts/Declarations).
Import the operation's source module or export to make its binding available.
The common carrier retains the selected contract and has no operator lookup.

A source library can define an operator for a record it owns:

```text
use zkc::algebra;
struct Number<F: domain Field> { value: F::Element }
#[operator(add)]
fn Add<F: algebra::Field>(left: Number<F>, right: Number<F>) -> Number<F> {
  return Number { value: algebra::add(left.value, right.value) };
}
fn Twice<F: algebra::Field>(x: Number<F>) -> Number<F> { x + x }
```

The supported hooks are `add`, `sub`, `mul` and `neg`. The function must have a
checked body, two operands (one for `neg`) and one source result. At least one
operand's nominal record constructor must belong to the function's defining
package. Imported aliases do not confer ownership of foreign records. A library
cannot override installed arithmetic solely by declaring a function on field
operands. Ordinary functions and component bodies share these rules.

The installed arithmetic bindings are:

| Symbol | Operands | Installed operation |
|---|---|---|
| `+`, `-`, `*`, unary `-` | field | `field.add`, `field.sub`, `field.mul`, `field.neg` |
| `+`, unary `-` | group | `curve.add`, `curve.neg` |
| `*` | group and field, in either order | `curve.scale` |
| `+`, `-` | vector | `vector.add`, `vector.sub` |
| `*` | vector and field, in either order | `vector.scale` |
| `+`, `-`, `*` | index | `index.add`, `index.sub`, `index.mul` |

`vector.mul` has no spelling: `*` between two vectors reads as a dot product as
easily as an elementwise product, so both stay named.

Precedence is fixed: unary minus, then `*`, then `+` and `-`; binary operators
associate to the left. Parentheses group. Names never contain `-`, so `a-b` and
`a - b` are the same subtraction.

**Resolution.** The key is the hook and ordered tuple of resolved nominal
constructor heads, such as `field`, `group`, `vector` or a particular source
record. Record identity is retained before layout erasure. Duplicate keys refuse;
requirements, expected results and wildcard operands cannot choose among
candidates. Opaque types without known heads use named calls. Static arguments
are inferred and requirements checked only after selecting the unique callable.
A failed call does not trigger another candidate search.

Operands evaluate once, left to right as written. The binding then arranges the
resulting values in signature order; scalar/group multiplication can permute
ports without permuting evaluation. Each installed port mapping is a bijection
checked against the operation signature. No spelling implies an algebraic law,
reassociation or simplification. Source record operators emit ordinary calls to
their checked bodies, including when used in a component.

With `use zkc::algebra;`, `let c = a * b;` on field values emits the same call as
`let c = algebra::mul(a, b);`. A module selecting implementations through explicit
`bind` declarations calls those binding names to retain that selection; intrinsic
operator sugar uses the installed operation's default binding.

| Refusal | Code |
|---|---|
| No binding for the hook and operand heads, including unavailable imports | `source-operator-unresolved` |
| Unsupported hook or misplaced/repeated attribute | `source-operator-attribute` |
| Wrong operand arity or source result shape | `source-operator-arity`, `source-operator-result` |
| Missing checked body or no operand record owned by the package | `source-operator-body`, `source-operator-ownership` |
| Unsupported operand head or duplicate tuple | `source-operator-head`, `source-operator-duplicate` |
| Installed binding disagrees with its signature | `source-operator-table` |

## 5. Checked structs

```text
use zkc::algebra::Vector;
checked struct BoundAssignment<F: domain Field> {
  assignment: Vector<F::Element>,
  statement: Vector<F::Element>,
  private_assignment: Vector<F::Element>
} constructors(BindAssignment);
```

The brace form can state the same restriction without the `checked` keyword:
`struct BoundAssignment<F: domain Field> constructors(BindAssignment) { ... }`.
The constructor list makes the type checked in either notation; omitting both
leaves an ordinary struct.

A checked struct is a struct whose construction is accepted only inside the
bodies of its named constructor functions. Each constructor is a declared
function with a body in the same module. Everywhere else the value can be
passed, returned and read by field, but not built. A consumer that declares a
parameter of the checked type therefore receives a value that a constructor
returned. Fields are readable because values are immutable: a read cannot
change what the constructor checked.

A checked value can carry runtime context in its fields. Current record static
parameters range over domain sorts, not relation declarations. Association with
a particular relation or setup is established by the actual constructor and
consumer contract; the type name alone does not establish that association.

The positions at which a value would arrive without its constructor are
refused: an input of a protocol selected by an `entry`, where the host supplies
values, and the result of a function or protocol declared `external`
(`source-checked-input`, `source-checked-external`). Messages already refuse
every struct.

The rule states that a constructor ran its checks on this value. It does not
state that the checks are the right ones; that is the constructor author's
obligation, and the formal reference does not see this rule. The restriction is
applied to `.pir` text and guards its author against an omitted or mismatched
check.

| Refusal | Code |
|---|---|
| Construction outside a named constructor | `source-checked-construction` |
| A constructor that is undeclared, has no body, or does not return the type | `source-checked-constructor` |
| Entry-protocol input, or `external` result | `source-checked-input`, `source-checked-external` |

## 6. Implementation homes and validation

The [frontend implementation map](../compiler/frontend.md#engineering-boundaries-and-assurance)
owns parsing, retained source checking and common emission responsibilities.
Data forms keep nominal information in source analysis and lower to existing
common records; they do not add an execution dialect.

Validation compares encoded common records with their expansions, exercises
author-facing refusals, reformats the maintained examples, and keeps the
existing Groth16 interoperability and rejection checks on the rewritten source.

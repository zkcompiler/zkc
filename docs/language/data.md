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
   type notation is shared and is not a declaration owned by an author.

## 2. Constraint bundles

```text
bundle PairingArithmetic(F) = (
  ScalarAction(F::PairingG1), ScalarAction(F::PairingG2),
  "="(F::PairingG1::Scalar, F), "="(F::PairingG2::Scalar, F)
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
written by hand, and the existing checker sees nothing new.

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
struct VerifyingKey<F: domain Field>(
  input_query: Vector<F::PairingG1::Element>,
  alpha: F::PairingG1::Element,
  beta: F::PairingG2::Element
);

let vk = VerifyingKey(input_query = q, alpha = a, beta = b);
let x = vk.alpha;
```

A declaration lists named, typed fields. A field type is a logical type or
another struct; the struct graph is acyclic, at most 64 deep, and a struct has
at most 4096 leaves. Static parameters use the kind-only form `F: domain Sort`.
A struct records no capability assumption, so a capability bound on a struct
parameter is refused (`source-struct-bound`) instead of being dropped silently.
Capabilities remain promises of the functions that use the struct.

The parenthesized forms remain accepted. Declarations also accept
`struct Pair { left: T, right: T }`, and construction accepts
`Pair { left: x, right: y }` or field shorthand. The
[source product guide](values.md#products-local-blocks-and-distributed-outputs)
explains brace syntax and named function arguments.

**Flattening.** A struct value is its leaves: the fields in declaration order,
nested structs expanded depth first. A binding `vk` of struct type is the
ordinary values `vk.input_query`, `vk.alpha`, `vk.beta`. These are legal value
names already, and the lexer reads `vk.alpha` as one name, so a field read is
an ordinary name reference and needs no operation. A parameter `vk: VerifyingKey<F>`
becomes the parameters `vk.input_query`, `vk.alpha`, `vk.beta`; a struct result
occupies as many result positions as it has leaves. Declaring a value whose
name collides with a leaf, or with the struct binding itself, is the existing
duplicate-binding error.

**Construction.** `Name(field = expr, ...)` names every field exactly once, in
any order. Initializers are evaluated in written order; the leaves are then
arranged in declaration order. Construction emits no operation. Static
arguments are inferred from the initializers by the rule already used for
calls, or written as `Name::<F>(...)`. Nullary structs are refused.

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

```text
let a = alpha + linear_a + delta_g1 * r;
let blinded = c + -(delta_g1 * (r * s));
```

An operator is a spelling of an installed operation. Both the operation and
its spelling belong to the definition of the domain: whoever defines `field`
says what `field.mul` computes and that `*` is written for it. Installed
domains are a closed catalog that this repository owns. Every installed
operation needs an interpretation in the formal reference and a native
implementation, so a domain is added in the tree, by the
[procedure for operations](../compiler/protocol-libraries.md#adding-an-operation-or-implementation),
and no source declares an operator for it. A declaration inside a protocol file
would let each file give `*` its own meaning for a type the file does not own,
and would repeat the same lines in every file.

Within a domain's definition the two stay apart. What `field.mul` computes is
its installed contract, with its signature and its value rule, and import,
admission and planning read that. The spelling is authoring notation, which
those stages do not read and another frontend need not share.

The catalog does not yet keep each domain's definition in one place: its
operations, capabilities and domain facts are installed in separate tables,
and none of them holds notation. Until the catalog is grouped by domain, the
spellings are one table in the frontend,
[`Operators.h`](../../compiler/lib/Frontend/Semantics/Operators.h), beside the type
names in [`Types.h`](../../compiler/lib/Frontend/Syntax/Types.h). This is a
temporary home. Both tables move into the per-domain definitions when that
grouping is made, which belongs with the language and type-system design
because capabilities, associated domains and notation are what that design
reshapes. The catalog, the JSON form and every later stage are unchanged.

A module may come to declare operators for a struct it declares, when operators
accept struct operands; that module owns the type.

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
associate to the left. Parentheses group. Names may contain `-`, so `a-b` is
one name; a binary minus is written with a space before it.

**Resolution.** The key of a spelling is its symbol and the logical constructor
of each operand, such as `field`, `group` or `vector`. The table has one entry
per key, so a use matches at most one. At a use, the operand types are already
known; the key selects the operation, and the resulting call is elaborated as
if written: static arguments are inferred, requirements are checked by the
existing checker, and a failure is reported for that call. Nothing else is
tried. Each selected entry is compared with the installed signature of the
operation it names, so the table cannot state what the contract does not
(`source-operator-table`). Operands are evaluated left to right in written
order, whatever order the operation takes them in.

A binding `let c = a * b;` over named operands is the flat call
`let c = field::mul(a, b);`, so both spellings number later temporaries alike.
`a + b + c` is exactly `add(add(a, b), c)`. No spelling implies a law, and no
expression is reassociated or simplified. Operators are accepted in function
bodies, where expressions already are. In a module that selects implementations
by explicit `bind`, an operator is the qualified call with its default binding;
such a module names its bindings to keep its selection.

| Refusal | Code |
|---|---|
| No spelling for the symbol and operand constructors at a use | `source-operator-unresolved` |
| A struct operand | `source-struct-value` |
| An internal table entry that disagrees with the installed signature; not author-triggerable with the installed table | `source-operator-table` |

## 5. Checked structs

```text
checked struct BoundAssignment<F: domain Field>(
  assignment: Vector<F::Element>,
  statement: Vector<F::Element>,
  private_assignment: Vector<F::Element>
) constructors (BindAssignment);
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

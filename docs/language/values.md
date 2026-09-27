# Products, local computation and outputs

Products group source values without changing their participant ownership. Local
blocks place computation at a role; returned products connect its results to the
surrounding protocol. [Data forms](data.md) covers nominal records and operators.

## Installed types and bulk values

Imports expose the installation's domain vocabulary. Its constructors declare
whether each static argument is a nominal domain, a type or a natural. For
example:

<!-- executable: module-body -->
```text
use zkc::algebra::{Field, Vector, FixedVector};
use zkc::algebra;

fn Dot<F: Field, N: nat>(left: Vector<F::Element>, right: Vector<F::Element>)
    -> F::Element {
  let x: FixedVector<F::Element, N> = algebra::fixed_vector_from_vector(left);
  let y: FixedVector<F::Element, N> = algebra::fixed_vector_from_vector(right);
  algebra::fixed_vector_dot(x, y)
}
configure DotFour = Dot(F = koala-bear, N = 4);
```

`F::Element` denotes the selected field's element type. `Vector<T>` uses the
installed element-family cases; `FixedVector<T, N>` retains both its element type
and length as one nominal bulk value. Conversion from a vector checks its actual
length. In contrast, `[T; N]` is a source aggregate that lowers to N leaf ports.
Neither annotation expands a fixed vector into source array elements.

Types do not select implementations. This example's KoalaBear operations have
Plonky3 implementations; other well-formed type applications can lack a backend
and refuse during physical selection. Copy/drop permissions propagate through
type arguments, while serialization requires separate installed support. See
[the complete protocol](../../examples/protocols/fixed-vector.pir) and
[extension installation](../development/extensions.md#add-a-logical-type-and-operations).

## Products, local blocks and distributed outputs

<!-- executable: module-body -->
```text
use zkc::{algebra, core};
struct Pair<F: domain Field> { left: F::Element, right: F::Element }

fn PairUp<F: Field>(left: F::Element, right: F::Element)
    -> (Pair<F>, ()) {
  (Pair { right, left }, ())
}

protocol Exchange<F: Field> {
  roles (Worker, Checker);
  inputs (Worker x: F::Element, Checker expected: F::Element);
  outputs (Worker result: F::Element, Checker accepted: bool);
  let result = local Worker {
    let (pair, done) = PairUp(right: x, left: x);
    pair.left + pair.right
  };
  message value: Worker(result) -> Checker(received);
  let accepted = local Checker {
    let same = algebra::equal(received, expected);
    core::require(same);
    same
  };
  finish { accepted, result };
}
entry main = Exchange::<F = "bls12-381.fr">;
```

These declarations go inside `module { ... }`. A product is an ordinary local
value: it can be stored, passed, returned, nested and projected with `.0`, `.1`,
and so on. `(x)` groups an expression; `(x,)` is a singleton; `()` is unit.
Source product types retain the same distinctions. Lowering concatenates leaf
layouts without allocating a new runtime tuple object. An aggregate remains
immutable; individual scalar bindings can use the existing mutable local control.
Annotations on aggregate expressions check their source types before erasure.

`local Worker { ... }` admits only Worker's available values and returns a value
owned by Worker. Its ordinary function calls do not communicate. The compiler
creates a private helper and supplies only used free leaves, preserving affine
resource checks. Scratch bindings stay inside the block. The shared local checker
also handles explicit `return value;`, existing bounded `for` and local `if`.
An explicit return must be final in the enclosing function/block; early returns
inside control regions are refused. Same-scope and inherited-name shadowing are
currently refused; this is not a claim to implement Rust's complete block language.

Retained lexical queries distinguish each branch's explicit captures and each
loop's induction/carried parameters from the enclosing scope. Unit captures retain
a source binding even though they contribute no target leaves. These scope records
support diagnostics and tooling; they do not add runtime storage or communication.

`finish` names the protocol's distributed output ports. Written order may differ
from declaration order. Its values must have the declared type and owner; there
is no implicit communication or acceptance check. Child invocations can bind
those names explicitly:

```text
dependencies(child: Exchange::<F=F>());
invoke child(x, expected) -> {accepted: ok, result: value};
finish {result: value, accepted: ok};
```

The enclosing protocol must declare corresponding inputs, outputs and roles.
The existing positional invocation form remains useful for explicit common-PIR
notation. A direct entry into a closed protocol or concrete family selection
creates the finite child-instance tree with identity role mappings. A protocol
with unresolved natural parameters requires explicit instance wiring. This
shorthand requires the declared static arguments and supplies no domain defaults.

Named function arguments use `name: expression`. All inputs must be named exactly
once when using that form. Operands execute left to right as written, then map to
signature order. Imported intrinsic calls also accept named operands using their
generated public labels. For example, after `use zkc::algebra;`,
`algebra::add(field1: right, field0: left)` evaluates `right` before `left`, then
supplies the values to the installed `field.add` ports. These labels are part of
the export; they are not guessed from local variable names.

Predicate/equality requirements can use a single `where` clause:

```text
fn Identity<G: domain Group, F: domain Field>(x: F::Element) -> F::Element
  where ScalarAction(G), Field(F), G::Scalar == F { x }
```

This uses the existing capability/entailment engine. Constructor authority can be
written `struct Prepared<F: domain Field> constructors(Make) { ... }`; the
restriction is not a proof that `Make` establishes an arbitrary mathematical
predicate. The explicit `requires (...)` and common-source record spelling are
still accepted by the same parser, without a migration adapter.

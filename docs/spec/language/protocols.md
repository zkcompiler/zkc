# Protocol bodies and relations

This native contract defines participant-local bodies, communication and control.

## Ordered control

```text
fn accumulate(x: Fr, n: index, go: bool) -> Fr {
  let zero: Fr = 0;
  let sum = for i in 0..n carry(s = zero) capture(x) {
    yield s + x;
  };
  return if go capture(sum) {
    yield sum;
  } else {
    stop "reject";
  };
}
```

`if`, exhaustive `match`, and `for` are expressions in local functions. Regions
are isolated: they see explicit `capture(...)` values, loop carries and indices,
or a selected variant's payload. All arms are checked. Continuing arms must yield
the same logical type. `match v capture(...) { Some(x) => {...}, None() => {...} }`
covers each declared alternative exactly once. A stopped arm needs no result.

A `for i in lower..upper carry(name = initial, ...) capture(...)` loop preserves
carry types. Zero iterations return the initial carries. One carry returns that
value; multiple carries return a tuple; no carries return unit. Captures require
`Copy`; affine resources travel through carries. Each continuing iteration retains
the exact captures at the backedge. `require condition;` stops on false. `stop`
uses a native reason: `reject`, `abort`, `exhausted`, `incomplete` or `refused`.
Target execution limits remain independent of source effects and typing.

## Participant meaning

```text
protocol Transfer roles(P, V)(x: Fr @P, n: index @P, go: bool @P) -> (result: Fr @V) {
  local P let payload = accumulate(x, n, go);
  let received = send P -> V(payload);
  return (result = received);
}
entry Demo = Transfer;
```

A protocol has an ordered, nonempty role roster and named, typed input/output ports
with nonempty role sets. `@P` and `@(P, V)` name components. Entries select a protocol
and closed static arguments; selection uses an exact qualified Entry name.

A protocol value denotes one component per available role. Shared input components
need not be equal. Total mathematical expressions require `Copy + Drop`; ordinary
arithmetic intersects operand availability. A helper result follows its body's
actual input dependencies, while formation checks retain every intermediate's
dependencies, including unused computations. A helper returning only its first
input may accept disjoint roles, but an unused sum of both inputs still requires
a common participant. Abstract mathematical members conservatively depend on all
inputs for both result availability and formation, including unused calls.

`local P let value = helper(args);` explicitly owns an ordered call at P. It creates
no communication. Multi-role values require `Copy + Drop + Share`; affine values
stay at one role. Narrowing availability requires `Drop`. Protocol returns use
`(port = expression, ...)`: expressions evaluate in written order and operands are
then placed in declared port order. Missing, repeated and unknown outputs refuse.

Send occupies a whole binding RHS. It requires distinct declared roles, sender
availability, and `Copy + Drop + Share + Wire`. Its result denotes the actual
received value and is available only at the receiver. The original payload retains
its roles. Each native payload leaf emits `protocol.exchange` followed immediately
by receiver-only `protocol.restrict_roles`. Zero-leaf messages refuse because erasing
a message would erase an interaction. These operations assume neither honest
delivery nor equality of participant components.

## Managed services and guards

```text
protocol Draw<F: Field> roles(V)() using(coins: Random<F> @V) -> (r: F @V) {
  using alias = coins;
  let r = alias.draw();
  return (r = r);
}
protocol Run roles(V)(go: bool @V) using(coins: Random<Fr> @V) -> (r: Fr @V) {
  guard @V go;
  let r = apply Draw<Fr>() using(coins);
  return (r = r);
}
```

Managed service ports are separate from data ports and static type arguments.
`Random<F>` requires a field and exactly one owner. Closure selects an installed
random-service contract for that field; analysis can retain a generic declaration
before that selection. The installed catalog includes service contracts in its
identity.

`using alias = coins;` borrows the same root. Aliases introduce no query, reset or
independence assumption. `coins.draw()` is ordered protocol work: its result is
available only at the service owner, and an unused result does not remove the
query.

```text
protocol Query<N: nat> roles(P, V)() using(coins: Random<E> @V) -> (p: index @P) {
  let position = coins.index<N>();
  let p = send V -> P(position);
  return (p = p);
}
```

`coins.index<N>()` samples UniformIndex(N): an `index` uniform on `[0, N)` under
the [installed sampler's premise](../runtime/services.md#uniformindex-realization).
`N` is a static natural, such as `pow2(K)`, and is fixed before sampling. A closed
`N` must be a power of two from 1 through 2^63; a generic `N` is checked when its
body closes. The service field must satisfy `zkc::random::IndexRandomness`, either
as a closed fact or through an explicit assumption. The result is available only
at the service owner and the query is ordered like `draw()`. It emits a
`data.index` constant immediately followed by a `protocol.query` with method
`index`; source correspondence compares both. Other distributions, runtime
bounds and rejection sampling are not source methods. Services cannot enter ordinary types, aggregate fields, messages, local
functions or return values. An application supplies its managed bindings after
its data arguments, in declared service order. Each field and mapped owner must
match. Repeating a binding passes the same reference to both ports.

`guard @V condition;` requires a Boolean available at V. False stops V at that
ordered occurrence; it does not produce a Boolean result or establish knowledge
at another role. The guard contributes the `stop` effect. Queries and guards
remain distinct native operations checked by source correspondence.

In the original MLIR, managed ports follow flattened data inputs. Each has a
`protocol.service_ref` type and a singleton role set. The source interface lists
managed ports under `services`, with name, installed contract, owner and native
input index; data schemas contain no service references.

## Protocol composition

```text
protocol Pair roles(A, B)(x: Fr @(A,B), y: Fr @(A,B))
    -> (sum: Fr @A, product: Fr @B) {
  return (sum = x + y, product = x * y);
}
protocol Use roles(P, V)(x: Fr @(P,V), y: Fr @(P,V))
    -> (p: Fr @P, v: Fr @V) {
  let (atV, atP) = apply Pair roles(V,P)(x, y);
  return (p = atP, v = atV);
}
```

`apply` occupies a whole protocol `let` RHS. Bindings follow the callee's declared
output order. Each result retains its own type and participant set; the binding
list does not construct a tuple with shared availability. A sole result can use
`let value = apply ...`; a resultless application uses `let () = apply ...`.
Applications remain ordered even when their results are unused.

`roles(...)` maps the callee's ordered roster to distinct caller roles. Omitting
it selects identically named roles, which must all exist in the caller. An explicit
empty, incomplete or noninjective map refuses. Inputs must supply every mapped
component. Results expose exactly the callee's mapped declared output sets.
Shared availability does not assert equality of participant inputs or results.
Static arguments follow the same inference and bound checks as helper calls.

Applications lower directly to `protocol.apply`. Its native static expansion
preserves nested sites and explicit participant boundaries before projection.
The combined helper/application graph must be acyclic and obey source and native
expansion limits. No additional runtime call stack is introduced. `apply` is
contextual here; library members can still be named `apply`.

## Distributed repetition

```text
let (af, bf) = repeat roles(P,V)(i < n, max N)
    carry(a = initialP @P, b = initialV @V) capture(go) using(coins) {
  guard @V go;
  let (x, y) = apply Round(a, b) using(coins);
  yield (a = x, b = y);
};
```

A protocol `repeat` is an ordered, isolated region. Its runtime `index` count must
be available at every listed participant. Its static natural maximum closes to
at most 1,048,576. Each participant checks its local count before body work. A
joint host additionally checks count agreement among live participants; source
availability alone does not prove equal counts.

Carries have separate types and role sets. An optional carry annotation selects
a nonempty subset of both the initial availability and loop roles; otherwise it
uses their intersection. Narrowing requires `Drop`; shared carries require
`Copy + Drop + Share`. The named yield supplies every carry exactly once, with
matching type and availability. Result bindings follow carry declaration order.
Zero iterations return the initial values. Affine carries must preserve each
input's exact native root at the backedge, including through helper applications.

Data captures require `Copy`. Managed captures borrow the same roots and require
their owners inside the loop. Nested actions may use only loop participants;
nested regions need their own explicit captures. Total mathematics retains its
ordinary component semantics. Results cannot hide per-role values in a tuple.
The native repeat carries flattened data while keeping managed captures separate
from source data layouts. Source correspondence checks the maximum, roles,
operands, region signature, nested operations and named yield.

A conditional service query can use a one-role repeat with maximum one. An owned
local helper computes its zero-or-one count. The query executes only in the
reached iteration; it is never hoisted or evaluated speculatively.

## Conditional participant completion

```text
protocol Run roles(V)(go: bool @V, x: Fr @V) -> (result: Fr @V) completes {
  let () = finish_if @V(go) (result = x);
  return (result = x + x);
}
```

`completes` declares an Entry-only protocol: applying it as a reusable component
refuses, including when its body has no current completion action. `finish_if`
requires that marker and occupies a complete unannotated `let` RHS. Its Boolean
condition and named outputs must be available at its owner. The named list
supplies exactly that owner's declared protocol outputs. Expressions evaluate in
written order; native operands follow output declaration order.

True completes only that participant, unwinds its enclosing repeats and skips
its remaining actions. False continues. Neither path informs peers or equates
shared output components. Every suffix remains statically checked. This action
is normal completion, distinct from a guard failure or host retry decision.

The binding list names the outputs without `Copy`, in declaration order. Those
values move on both paths; false returns fresh continuations. Copyable outputs
remain usable through their original bindings. A product continuation preserves
its copyable data leaves and replaces each native affine leaf with the action's
successor. Generic definitions retain their declared move discipline even when
an instantiation selects a copyable type. Normal cleanup follows the existing
[entry completion contract](../ir/completion.md).

## Relations and specification clauses

```text
relation DLog<H: Group>(parameter base: H, statement point: H,
                        witness scalar: H::Scalar) {
  return point == base * scalar;
}
protocol Check<H: Group> roles(P, V)
    (g: H @V, h: H @V, x: H::Scalar @P) -> (accepted: bool @V)
    spec {
      target knowledge = DLog<H>(in.g, in.h, in.x) accept out.accepted;
    }
{
  // The authored protocol must compute its own decision.
  let accepted @V = true;
  return (accepted = accepted);
}
```

A relation owns ordered formals with explicit `parameter`, `statement` or
`witness` purposes. These labels describe the proposition; they do not introduce
runtime ports, decide input authority or assert secrecy. Formula relations reuse
the total mathematical body language and return one Boolean. They are not callable
execution helpers. Formal polynomials may be reconstructed inside the predicate
from immutable executable data. Generic arguments are explicit at relation
applications. Selected formal layouts must be nonempty immutable logical data;
zero-argument relations are allowed.

A protocol's optional `spec { ... }` precedes its body, after bounds and effects.
`spec` is reserved. Clause names are unique within that block:

| Clause | Binding requirement |
|---|---|
| `target name = R(...) accept out.decision;` | Relation application and a required Boolean decision output |
| `input name = R(...);` | Input selectors only; no decision |
| `output name = R(...) [accept out.decision];` | At least one output selector; optional decision |
| `continuation name = R(...) residual S(...) [accept out.decision];` | Input-only subject and a residual containing an actual output |

Square brackets in the table denote optional syntax. A selector is `in.port` or
`out.port`, followed by logical record/tuple/fixed-array projections and an optional
`@Role`. An omitted role is inferred only from a singleton declared port role set.
Shared roles may hold different values. Selectors preserve the chosen component,
field privacy and static bounds. They cannot select internal SSA values, index
inside a native container, or project an unchecked variant payload.

An inline relation uses explicitly bound formals:

```text
target equality = relation(statement expected = in.expected,
                           witness actual = out.actual) {
  return expected == actual;
} accept out.accepted;
```

Its types come from those bindings. It inherits the protocol's static parameters
and bounds, and captures no other runtime values. The anonymous declaration is
bound by ID and cannot be named through a generated source path.

Clauses state authored intent. They neither assume satisfaction nor insert a guard,
execute a predicate, prove soundness, or establish a reduction. Output conditions
and residuals refer to the actual completed results; a non-completing path supplies
no result proposition. A target decision is not a proof that its relation holds.

Opaque and captured definitions have no mathematical body:

```text
relation External(statement x: bool, witness w: bool)
  = opaque("vendor.predicate/0", "key", "revision");
relation Circuit(statement public: builtin("field_array", Fr, 1),
                 witness assignment: builtin("field_array", Fr, 3))
  = r1cs(asset library::circuit);
relation Trace(statement public: builtin("field_array", Fr, 1),
               witness trace: builtin("matrix", Fr))
  = air(asset trace_constraints);
relation Machine(statement x0: Base, statement final: Base,
                 parameter rom_height: index, parameter rom: Vector<Base>,
                 witness multiplicity: Vector<Base>,
                 statement cpu_height: index, witness trace: Vector<Base>,
                 statement log_present: bool, statement log_height: index,
                 witness log: Vector<Ext>)
  = bundle(asset machine);
```

Opaque identities must be nonempty and cannot use the `zkc.` namespace. They have
fixed signatures without static parameters. Declarations sharing one
(kind, key, revision) must have identical logical formal types and purposes;
flattened native equality is insufficient. Formal names may differ.

Captured definitions also have fixed signatures. R1CS uses the asset's exact field,
public count and full assignment length, including ONE and the public prefix. The
witness purpose does not make that entire assignment secret. AIR uses the exact
public-input array and trace matrix field, retaining columns and row scopes in
the immutable asset. Dynamic trace shape and work admission are separate from
predicate truth. Asset paths refer only to explicitly captured bytes. Runtime
matrix parameters remain ordinary protocol inputs when the author instead defines
a formula over them.

### Bundle declarations

A bundle declaration binds a captured
[relation bundle](../domains/relation-bundles.md) and has the signature the
bundle derives. The derived formals are, in this order: one `statement` formal
of the slot's exact field per public slot, in slot order; then for each table in
table order, a `statement bool` presence formal when the table is optional, a
height `index` formal when the height authority is `config` (`parameter`) or
`instance` (`statement`) and none for a fixed height, then one
`builtin("vector", field)` formal per group in group order, over the group's exact
field, with `witness` for a witness group, `parameter` for a configuration group
and `statement` for a public group. Channels contribute nothing. The example
above binds a bundle with public slots `x0` and `final` over `Base`; a required
table with configuration height, a configuration group and a witness group; a
required table with instance height and a witness group; and an optional table
with instance height and one witness group over `Ext`. A declaration must spell
exactly the derived count, logical types and purposes; formal names are free.
Field membership is retained per formal, so a bundle over several fields has
formals over several fields; no field is joined or embedded into another.

An assignment of these formals denotes the bundle's configuration, instance and
witness carriers: the public formals are the instance's public values in slot
order; a configuration height formal and the `parameter` vectors of a table
are its configuration height and groups; a presence formal is the instance's
presence choice, and a required table is present; an instance height formal and
the `statement` vectors are its instance height and groups; the `witness`
vectors are its witness groups. A vector of a present table of height `h` and
a group of width `w` has exactly `h * w` elements, element `k` being row
`k / w`, column `k % w`. Configuration data is admitted against its declared
height whether or not the table is present, as in the bundle chapter. An
absent optional table has empty `statement` and `witness` vectors and, when its
height authority is `instance`, a height formal equal to `0`; admitted heights
are at least `1`, so `0` is the one spelling of an absent height. The relation
holds for an assignment exactly when the bundle holds for the carriers it
denotes, including their admission: a vector of another length, an element
outside its field encoding, a height outside its declared range or power-of-two
requirement, or a nonempty vector of an absent table makes the relation false.
As for every relation declaration, the declaration asserts intent; it does not
evaluate the bundle, add a guard or establish that an Entry proves it.

# Protocol bodies and relations

This native contract defines participant-local bodies, communication and control.

## Bindings and local control

```text
fn accumulate(x: Fr, n: index, go: bool) -> Fr {
  let mut sum: Fr = 0;
  for _ in 0..n {
    sum = sum + x;
  }
  return if go {
    sum
  } else {
    stop "reject";
  };
}
```

`let pattern = expression;` introduces immutable bindings. `let mut name =
expression;` introduces an assignable binding; `name = expression;` replaces its
whole value after evaluating the RHS. Type and protocol role set remain fixed.
There is no assignment to individual fields. Each authored binding and assigned
successor retains its own resource obligations, including empty values.
Overwriting an unused value without `Drop` refuses.

Blocks have lexical scope. A new binding's initializer sees the previous binding;
same-scope rebinding and inner immutable shadowing are allowed. Nested bindings
cannot shadow an outer mutable binding or a managed service. Declaration names
remain reserved against local shadowing. A plain block adds no runtime control
operation. A final expression is its result; no tail means unit. `return` ends a
declaration body and cannot occur in a nested block. A continuing declaration
requires `return`; a declaration whose final statement always stops needs none.
Statements or terminators after a guaranteed stop are rejected, including code
after an all-stopped control. An operand that always stops must be expressed as
a whole block/control result, not embedded in an unreachable enclosing operation.

Patterns include names, `_`, `()`, tuples and complete named records, such as
`let (x, _) = pair;` or `let Point{x, y: ordinate} = point;`. Wildcards and discarded
expression statements require `Drop`. Record patterns preserve field privacy;
opening a restricted record requires local mode and constructor authority.
Record construction supports same-name fields, such as `Point{x, y}`.

`if` and exhaustive `match` are local expressions. All arms are checked, including
statically unselected arms, and continuing arms have one common result type.
`match choice { Some(x) => { x }, None() => { stop "reject"; } }` covers every
alternative once. A missing `else` supplies an empty block. A block-like statement
without a semicolon must produce unit. Header conditions, scrutinees and bounds
containing record literals require parentheses. A value expression whose every
arm stops needs an expected type or a discarded statement context. Nested stopped
arms do not constrain the result inferred from continuing arms. A stopped path has
no resource obligations. Result inference uses the expected type or the first
continuing arm; annotate numeric literals when that context is insufficient.

Free places are reads before assignment on some continuing path, preserving
projection privacy and partial moves. Capturing one field does not move its affine siblings.
A noncopyable immutable branch capture transfers custody; return it explicitly to
retain access. Mutable state is joined only when wholly available on every
continuing arm. Otherwise it becomes unavailable; each residual must be consumed
or permit `Drop`. Assignment can restore an unavailable binding. A partially moved
root may supply its remaining fields, but cannot supply a whole value. Inferred
`Copy` inputs do not create authored obligations: for values without `Drop`, only
uses guaranteed on every continuing arm discharge the corresponding outer places.
A later outer use remains valid; explicit aliases still require their own use.

Local `for i in lower..upper { ... }` evaluates both `index` bounds once, in written
order, and produces unit. Outer assignments and referenced, wholly available
noncopyable mutable roots become loop state. Every state slot needs a whole initial
value and a whole successor on every continuing iteration; zero iterations retain
the initial value. Local state may replace a resource with a newly constructed one.
Invariant places require `Copy`. A possibly empty loop does not discharge an outer
invariant's no-`Drop` obligation: it still needs a use outside the loop. Managed
services are unavailable inside local functions.

`require condition;` stops with native reason `reject` on false and retains
effects already performed. A raw `kernel("control.require", condition)` instead
retains its installed backend-failure contract. `stop` uses a native reason:
`reject`, `abort`, `exhausted`, `incomplete` or `refused`. Target execution limits
remain independent of source effects and typing.

## Participant meaning

```text
protocol Transfer roles(P, V)(x: Fr @P, n: index @P, go: bool @P) -> (result: Fr @V) {
  let payload @P = accumulate(x, n, go);
  let received = send P -> V(payload);
  return received;
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

An ordinary `fn` runs once at exactly one participant; its result is available
only there. The compiler infers that owner within the current authored statement.
Inputs, explicit `@` annotations, a mutable target's fixed roles, a send's sender,
return ports and enclosing ordinary calls constrain the choice. Every ordinary
call requires all its arguments at its owner, including unused arguments.
There must be exactly one solution for every call; conflicts use `source.roles`
and ambiguities use `source.owner`. Neither permissions nor the cost of execution
chooses an owner. Explicit annotations are checked constraints.

```text
// shared: Fr @(P,V), p: Fr @P; f is an ordinary fn.
let a = f(p);                 // P
let b = f(shared) + p;        // P
let c @V = f(shared);         // V
let received = send P -> V(f(shared)); // call at P, received value at V
// let ambiguous = f(shared); // error: P or V
```

Each let, assignment, discarded expression, require, send, application,
completion and return settles before the next statement. Later uses cannot
choose an earlier owner. A multi-port return supplies separate demands in one
statement. A loop header settles before its body, whose statements and final
unit expression settle in order. Inner block statements settle independently;
the outer demand reaches only the block's final expression. Compiler-generated
temporaries do not create new boundaries. Callee contracts are fixed before checking the caller;
specialization does not infer owners again.

Nested calls evaluate strictly left to right and remain ordered even when their
results are unused. Different calls in one statement may have different owners.
Pure mathematics propagates demand through its actual result dependencies.
Every original mathematical intermediate must still form at the chosen owners,
but an ignored intermediate cannot select them. For example, if `zero(x)` returns
constant zero, `let r @P = zero(f(shared));` remains ambiguous. Likewise,
`zero(f(shared) * p)` remains ambiguous even though the ignored product would
need P. Once other demands uniquely select owners, every such product must
still form; the compiler never retries another owner after a formation failure.

One logical tuple, record or array requires common availability for all fields.
Projection and destructuring preserve that set, including through mathematical
helpers and native flattening. Separate protocol result ports keep separate sets.
Dependencies are determined before optimization: `x-x` and `x*0` retain x's source
dependency.

Narrowing availability requires `Drop`; multi-role values require `Share` in
addition to each operation's own permissions. `let mut x = shared;` fixes both
components; assigning a P-only value cannot narrow x. Use separate bindings such
as `let mut xp @P = shared;` and `let mut xv @V = shared;` for independent state.
No rule inserts communication or replicates an ordinary call. Inside a restricted
roster, reads use its available components; actions stay inside that roster and
mutable state retains its entire original role set.

A sole protocol output accepts `return expression;`. Multiple outputs use
`return (port = expression, ...);`, with same-name shorthand `return (port, ...);`.
Expressions evaluate in written order, then operands are placed in declared port
order. Missing, repeated and unknown outputs refuse.

Send occupies a whole binding RHS. It requires distinct declared roles, sender
availability, and `Copy + Drop + Share + Wire`. Its result denotes the actual
received value and is available only at the receiver. The original payload retains
its roles. Each native payload leaf emits `protocol.exchange` followed immediately
by receiver-only `protocol.restrict_roles`. Zero-leaf messages refuse because erasing
a message would erase an interaction. These operations assume neither honest
delivery nor equality of participant components.

## Managed services and rejection

```text
protocol Draw<F: Field> roles(V)(coins: Random<F> @V) -> (r: F @V) {
  let alias = coins;
  let r = alias.draw();
  return (r = r);
}
protocol Run roles(V)(go: bool @V, coins: Random<Fr> @V) -> (r: Fr @V) {
  require @V go;
  let r = Draw<Fr>(coins);
  return (r = r);
}
```

Protocol declarations and applications use one ordered list for data and managed
arguments; either kind may appear in any position. The checked representation
retains distinct data ports, service ports and their source argument order.
Static type arguments remain separate.
`Random<F>` requires a field and exactly one owner. Closure selects an installed
random-service contract for that field; analysis can retain a generic declaration
before that selection. The installed catalog includes service contracts in its
identity.

`let alias = coins;` names the same root. The alias is immutable and unannotated. Aliases introduce no query, reset or
independence assumption. `coins.draw()` is ordered protocol work: its result is
available only at the service owner, and an unused result does not remove the
query. Services cannot enter ordinary types, aggregate fields, messages, local
functions or return values. An application supplies each managed binding in its
declared argument position. Each field and mapped owner must
match. Repeating a binding passes the same reference to both ports.

`require @V condition;` requires a Boolean available at V. False stops V at that
ordered occurrence; it does not produce a Boolean result or establish knowledge
at another role. Omit `@V` when the statement determines one owner, as in
`require actual == expected;` with V-only `actual`. A shared condition alone is
ambiguous. Local functions inherit their caller's owner. False is a native
rejection, distinct from returning `false`, backend failure or normal completion.
It does not broadcast, roll back effects or request a retry. A stopped prover
publishes no completed proof; a stopped verifier cannot accept. The action
contributes `stop` and lowers to `protocol.guard` or local conditional rejection.
Source correspondence checks those exact outcomes.

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
  let (atV, atP) = Pair roles(V,P)(x, y);
  return (p = atP, v = atV);
}
```

Calls resolve by declaration kind. A protocol call occupies a whole `let` RHS,
assignment RHS or expression statement. Results follow the callee's declared port
order and retain independent types and role sets; a multi-result tuple pattern
does not construct a tuple value. One result accepts an ordinary pattern. Multiple
results require one pattern per port, without a combined type or role annotation.
A zero-result call can be written `Observe();` or `let () = Observe();`.
Discarded outputs require `Drop`; calls remain ordered when their results are unused.

`roles(...)` maps the callee's ordered roster to distinct caller roles. Omitting
it selects identically named roles, which must all exist in the caller. An explicit
empty, incomplete or noninjective map refuses. Inputs must supply every mapped
component. Results expose exactly the callee's mapped declared output sets.
Shared availability does not assert equality of participant inputs or results.
Static arguments follow the same inference and bound checks as helper calls.

Applications lower directly to `protocol.apply`. Its native static expansion
preserves nested sites and explicit participant boundaries before projection.
The combined helper/application graph must be acyclic and obey source and native
expansion limits. No additional runtime call stack is introduced.

## Distributed repetition

```text
let mut a = initialP;
let mut b = initialV;
for i in 0..n roles(P, V) max N {
  require @V go;
  let (x, y) = Round(a, b, coins);
  a = x;
  b = y;
}
```

A protocol `for` requires literal lower bound `0`, explicit `roles(...)` and a
static natural `max`. Its runtime `index` count is evaluated once and must be
available at every listed participant. The maximum closes to at most 1,048,576.
Each participant checks its local count before body work. A joint Host also checks
count agreement among live participants; availability alone does not prove equality.

The compiler infers mutable state, invariant data and managed service references
from the body, including nested regions. State slots retain their types and full
role sets: every state participant must be in the loop roster. Narrow a binding
before the loop when necessary. Zero iterations return initial values. Each
continuing iteration supplies a whole successor. Affine protocol state must
preserve each input's exact native root, including through helper calls; equal
types or swapping same-typed resources do not suffice.

Invariant data places require `Copy`; their selected availability is the nonempty
intersection with loop roles, with narrowing allowed only under `Drop`. A
copyable mutable binding with no assignment can be an invariant. Managed aliases
capture their common root once and require its owner inside the loop. Nested
actions use only active loop participants. Mathematical component semantics remain
unchanged; separate participant states are never bundled into a common-role tuple.

The checked graph and native `protocol.repeat` retain explicit state, data
captures, managed references, region inputs and successors. Source comparison
checks those operands, the maximum, roles, signature and nested operations.
A conditional query can use a one-role loop with maximum one. An owned local
helper computes its zero-or-one count; the draw executes only in the reached
iteration and is never hoisted or evaluated speculatively.

## Conditional participant completion

```text
protocol Run roles(V)(go: bool @V, x: Fr @V) -> (result: Fr @V) completes {
  let () = finish_if @V(go) (result = x);
  return (result = x + x);
}
```

`completes` declares an Entry-only protocol: applying it as a reusable component
refuses, including when its body has no current completion action. `finish_if`
requires that marker and occupies a complete unannotated immutable `let` RHS. Its Boolean
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

# Mathematical source language

This profile defines the `.zkc` source language and its translation to
[mathematical protocol MLIR](../compiler/mathematical-protocols.md). It separates
total mathematics, ordered local computation and participant interaction. The
`.pir` profile has a separate parser and checking path; format selection is explicit.

## Capture and names

A capture is a nonempty map from logical module paths to exact UTF-8 bytes.
Each file starts with `module path;` matching its captured name. Module paths
use `::`; identifiers match `[A-Za-z_][A-Za-z0-9_]*`. Keywords are reserved.
Comments start with `//`. Tokens retain trivia and byte spans.

Module declarations are private unless prefixed with `pub`. Interface/component
members are exposed through their owner; associated representations retain their
constructor privacy. A declaration can be named
through `use module::{Name, Other};` or by its qualified path when its module
is captured. Imports never discover files. Imports, declarations, static parameters
and local bindings cannot shadow visible names. Imports, types and call graphs
must be acyclic. Every declaration is checked, including unused generic bodies.

Capture accepts named assets as explicit bytes alongside modules. Formats are
`r1cs-json`, `r1cs-binary` and `air-json`; checking never opens a diagnostic path.
The CLI accepts `--asset=NAME=FORMAT=FILE`. Analysis admits every supplied asset,
including unused ones, through the existing bounded R1CS or AIR reader. Canonical
relation identity retains constraint content, field, statement layout and AIR row
scopes. It does not prove a source-circuit interpretation or key/setup correctness.

Capture identity is SHA-256 over the `zkc.capture/2` marker, explicit source format,
module count, modules sorted by logical path, asset count, and assets sorted by
name. Module names/text and asset names/formats/exact bytes are included. Every
component, including the decimal counts, has an unsigned 64-bit little-endian
length prefix. Diagnostic paths do not enter identity. Canonical relation identity
is separate: transport whitespace can change capture identity while retaining the
same admitted relation definition.

Modules and assets share the file-count limit. Source text retains its own total
capture-byte limit. Assets have separate per-item and aggregate bounds of 64 MiB;
each reader retains its own structural and byte limits, including AIR's 8 MiB
bound. Caller limits may only lower these ceilings. Analysis rechecks the capture
against its requested limits before parsing assets. Capture alone supplies no
protocol ports, runtime matrices or specification binding.

## Definition checking and Entry closure

Analysis checks every definition and Entry reference against declared static
bounds. The resulting `CheckedProject` is immutable. Selecting an Entry creates
an independent `ClosedEntry` containing the reachable specialized bodies and
retained type declarations. Only those bodies enter its original MLIR. An
unselected Entry's target-admission failure does not invalidate another Entry;
source errors in any definition still reject analysis.

An instance key contains the qualified declaration name, checked body mode and
canonical static arguments, with each component length framed. Concrete
instances in their declared body mode retain the encoded declaration symbol. Specializations use `zkl_`
followed by the complete SHA-256 key digest; distinct keys that produce the same
symbol are refused. No declaration-table index enters the symbol. Local logical
origins name the source definition, allowing a selector to denote its instances;
the exact generated symbol and retained closure identify one specialization.
Adding an unreachable definition changes capture identity but does not rename
reachable instances. Template bodies are shared immutably. Specialization has its own work and instance budgets; retained templates do not consume the emitted-declaration allowance. Only reachable body copies are specialized before original emission.

## Types and static terms

```text
domain Fr = field("bls12-381.fr");
domain G = group("bls12-381.g1");
type Vector<F: Field, N: nat> = [F; N];
struct Pair<T: Type> { pub left: T, pub right: T }
enum Choice<T: Type> { Some(T), None() }
```

Runtime types comprise `bool`, `index`, unit `()`, tuples, fixed arrays, installed
fields/groups, native data containers, nominal records/variants and associated component types. `(T,)`
is a singleton tuple; `(T)` is grouping. A record's identity includes its declaration
and every static argument, including phantom arguments. Variant identity includes
its declaration and static arguments, not only its payload layout. Aliases expand
without creating a nominal identity. Variant payloads are positional; a variant
has one to 32 distinct alternatives. Formal mathematical types have a separate
[authoring contract](#formal-mathematics).

Domain declarations require an installed identity of the declared sort. A group's
`Scalar` association gives its scalar field. Static parameters use `Type`, `Field`,
`Group`, `nat`, or a selected interface. Naturals are compile-time values, distinct
from runtime `index`. Constants, parameters, addition and multiplication normalize
to polynomials with checked unsigned 64-bit coefficients. Equality compares those
normal forms. Arithmetic overflow refuses rather than wrapping.

`pow2(E)` denotes two to a static natural exponent. Its symbolic exponent must
normalize to a linear sum of natural parameters and a constant. For example,
`pow2(N + M)` equals `pow2(N) * pow2(M)`, and `pow2(2 * N + 3)` equals
`8 * pow2(N) * pow2(N)`. Powers are distinct typed factors, not encoded parameter
names. Substitution into signatures and explicit bounds checks the same
restriction during generic definition checking. Body-only static expressions are
substituted when the selected body closes; a call can therefore pass generic
checking and fail closing. Symbolic nonlinear exponents and nested symbolic powers
are unsupported. Closed exponents must be below 64; term, factor and work limits
bound symbolic expansion.
This is a sound set of normalization rules, not a complete procedure for
exponential arithmetic. Static argument inference does not invert `pow2`.

`where 1 <= N` requires a natural bound. `where Copy(T), Drop(T)` adds permission
requirements; `T: Type + Copy + Drop` expresses the same parameter permissions.
`where Share(G::Scalar), Wire(G::Scalar)` constrains an associated projection.
Calls must prove these bounds from the caller's explicit assumptions or the selected
concrete type. Closed permission requirements are evaluated immediately; a true
requirement adds no generic assumption. Group permissions do not imply scalar permissions.
Requirements follow a callable's result type or a nominal declaration's parameter
list; an alias places them before `=`. Symbolic inequalities must match an explicit
normalized assumption, or be reflexive. Closed inequalities are evaluated. There
is no inequality solver or inference by solving equations such as `N + M = 8`.

Fixed arrays have bounded closed lengths after selection. `[a, b]` constructs an
array; `a[0]` uses a numeric static index. A symbolic length needs a corresponding
explicit bound for that index. Dynamic array indexing is outside this profile.
Runtime loops and `index<N>()` in local code can use a closed natural as an index
value. Indices are not field elements.

## Native data and library kernels

Libraries can name installed data representations and wrap their operations:

```text
type Vector<F: Field> = builtin("vector", F);
type Matrix<F: Field> = builtin("matrix", F);
fn get<F: Field>(values: Vector<F>, i: index) -> F {
  return kernel<F>("vector.get", values, i);
}
fn columns<F: Field>(matrix: Matrix<F>) -> index {
  return kernel<F>("matrix.dimension", matrix; "1");
}
```

`builtin` selects a logical constructor from the installed catalog. Its argument
count and kinds are checked. This profile admits `vector`, `matrix`, `groups`,
`indices`, `polynomial`, `table`, `point`, `round`, `sequence` and `field_array`,
as well as scalar `field`, `group`, `bool` and `index`. Runtime collections remain
one native value; fixed source arrays retain their structural layout. Runtime
polynomial data does not denote a formal polynomial expression. The native type
policy owns mathematical and shared-data eligibility. Copy and Drop alone do not
admit runtime polynomial data into `math fn`, including through an aggregate or
a generic helper instantiated for ordered execution.

A `sequence` element is a scalar or another admitted native data type. Source
records, variants, products and private representations require their own
layout-preserving packing contract; they cannot be passed as native Type roots.
Managed services are separate from these data types. Container permissions retain
element permissions, and concrete external boundaries require native message
admission. A symbolic message shape still needs an admitted codec at closure.

`kernel<...>("contract", operands...; "parameter", ...)` calls an installed
source/construction contract from an ordinary local function. The semicolon and
parameters are optional. Static arguments explicitly select the contract's root
terms in declaration order; their kinds come from the catalog. Projections and
input/output types follow that signature. Multiple native results form a source
tuple, and no results form unit. Constant parameters use the contract's own
validation, including field-literal bounds. A generic field admits only `0` and
`1` as literals; concrete field parameters are checked against that field.

Generic checking may use the declared Field/Group facts and installed capability
implications. Stronger capabilities must be established by a concrete selection;
the compiler does not assume them from a field or group sort. Native Type roots
must be admitted data with Copy and Drop. Unknown contracts,
compiler-generated contracts, wrong statics, and source representation erasure
refuse before emission. Selected closure checks concrete native admission and
exact port agreement with the installed binding. Independent source comparison
resolves the actual binding again and checks its ports and parameters.

Kernels retain ordered execution and conservatively infer `stop`: the installed
local contract does not certify totality. Sampling and history transitions require
their managed interfaces. Type-root data operations refine the catalog's generic
custody uncertainty only after proving Copy and Drop for their roots and ports.
The catalog's construction stage includes runtime sequence operations; it does
not move those calls into Entry setup. Kernels cannot occur in `math fn` or directly
in protocol expressions. Protocols call library wrappers with an explicit local
owner. These bindings install no new backend, mathematical identity or provider.

## Boolean formulas

Total Boolean operations use the same mathematical helper path as field and
group expressions. `intrinsic("bool.and", a, b)`, `"bool.or"` and `"bool.xor"`
take two Boolean operands and return one Boolean. They have no static arguments
or literal parameters. Both operands are evaluated; these are mathematical
operations, not conditional execution. Libraries can expose ordinary functions:

```text
math fn both(a: bool, b: bool) -> bool {
  return intrinsic("bool.and", a, b);
}
math fn negate(a: bool) -> bool { return a == false; }
```

These helpers can be called in protocols or realized within local code. Their
input dependencies retain every actual participant component. Intrinsic syntax
itself stays inside mathematical functions.

## Formal mathematics

```text
type Array<F: Field, N: nat> = builtin("field_array", F, N);
type Poly<F: Field, N: nat> = formal("polynomial", F, N);
math fn multilinear<F: Field, N: nat>(table: Array<F, pow2(N)>) -> Poly<F, N> {
  return intrinsic<F, N>("poly.mle", table);
}
math fn evaluate<F: Field, N: nat>(p: Poly<F, N>, point: [F; N]) -> F {
  return intrinsic<F, N>("poly.evaluate", p, point);
}
```

A formal polynomial denotes an expression over a field and an ordered list of
variables. It is an SSA value in mathematical MLIR and has no executable value
encoding. Its type carries the field and natural arity. It has Copy and Drop,
but no Share or Wire. Mathematical helper ports, products, fixed arrays and
ordinary record fields can contain formal values. A zero-length array retains
its formal element meaning even though it has no SSA leaves.

Formal values are confined to mathematical helpers. Protocol and local-function
ports and body values require executable types, including messages, explicit role
restriction operations and distributed loop carriers/captures. The same restriction applies to `Type` static arguments, variants,
associated representations and native container arguments. These checks inspect
representation recursively, including private fields; permission annotations
cannot make a formal type executable. Arrays of length zero still require a
closed element layout and retain the element permissions. This also applies to
executable elements and is reflected in the source interface schema. A mathematical helper with executable ports may use formal values
internally and be realized inside local code through the common compiler path.

`intrinsic<...>("name", operands...; "point", ...)` is a library hook admitted
inside `math fn`. It emits a typed mathematical operation directly. Libraries
can wrap it with ordinary named functions. Static roots are explicit: one field
followed by the naturals listed below. Here `A(L)` means `Array<F,L>` and `P(N)`
means `Poly<F,N>`; `[F;K]` is a structural source array, flattened in order.

| Intrinsic | Natural roots | Input → output |
|---|---|---|
| `array.pack` | `L` | `[F;L] → A(L)` |
| `array.at` | `L,I` | `A(L) → F`, requiring `I + 1 <= L` |
| `poly.constant` | `N` | `F → P(N)` |
| `poly.from_coefficients` | `L` | `A(L) → P(1)`, requiring `1 <= L` |
| `poly.mle` | `N` | `A(pow2(N)) → P(N)` |
| `poly.add`, `poly.multiply` | `N` | `(P(N),P(N)) → P(N)` |
| `poly.fix` | `N,K` | `(P(N+K),[F;K]) → P(N)` |
| `poly.sum_suffix` | `N,C` | `P(N+C) → P(N)` |
| `poly.evaluate` | `N` | `(P(N),[F;N]) → F` |
| `poly.coefficients` | `L` | `P(1) → A(L)`, requiring `1 <= L` |
| `poly.evaluate_domain` | none | `P(1) → A(L)` for `L` supplied points |
| `poly.interpolate` | none | `A(L) → P(1)` for `L` supplied points |
| `poly.fix_table` | `N,K` | `(A(pow2(N+K)),[F;K]) → A(pow2(N))` |

Only the two domain intrinsics accept string parameters: one to 64 distinct,
canonical field literals in declared order. A symbolic field supports only
`0` and `1`; other literals need a concrete installed field. Explicit generic
natural bounds use the same entailment rules as ordinary calls. Definition
checking establishes logical shapes; closing rechecks the selected statics.

Native mathematical admission and preparation enforce the selected representation
and expansion limits, including arity at most 32. Coefficient extraction also
requires a derived degree bound that fits the result array. The polynomial
compiler checks every observation before eliminating unused expressions, including
observations exposed by helper expansion. Source typing does not supply a degree
certificate. The mathematical IR retains these expressions for analysis before
polynomial elimination produces ordinary executable calculations.

## Permissions and abstraction

| Permission | Source meaning |
|---|---|
| `Copy` | Reading a value may preserve the original place. Otherwise the read moves it. |
| `Drop` | A continuing path may leave a value unused. |
| `Share` | Participant placement may admit multiple components. |
| `Wire` | A source decoder may construct this value at an external boundary, subject to target codec and layout admission. |

Permissions are independent: `Copy` does not imply `Drop`. Products, arrays and
variants derive permissions from all their element/payload types. Explicit
permissions on a record or variant restrict those derived permissions; they cannot
add permissions that its fields lack. Restricted nominal constructors and private
record fields do not derive `Wire`; writing `Wire` on a restricted record or
variant is refused without an admitted validator. A private associated
implementation cannot promise `Wire` from its representation alone. `Field` and
`Group` parameters promise `Copy`
and `Drop`. Ground domain availability, sharing and transport still pass the
installed native type policy and codecs.

Fields are private unless marked `pub`. A restricted nominal constructor and its
representation are available only in its defining module. Private associated
representations are sealed behind component members. `unpack(value)` requires
that module's authority; it consumes the wrapper and returns its fields (a tuple
for a record, the representation for an associated type). Restricted values do
not expose ordinary field projection. `consume value;` requires constructor
authority and cannot discard fields that lack `Drop`. Such fields must be
unpacked and transferred separately. Variants require exhaustive `match` to transfer
or dispose of their payloads; `consume` and `unpack` operate on products and associated
representations. `drop value;` requires `Drop`.

Whole and partial moves are tracked before flattening. Overlapping uses after a
move refuse. Every place without `Drop` needs a use/transfer on each continuing
path, including empty values and copies made by a new binding. A stopped path
uses the target's cleanup semantics. This source obligation is distinct from
native affine custody; an affine runtime value can be cleaned up on a stop.

Entry inputs and message receives refuse private associated representations, restricted
records/variants, and recursively private record fields without an admitted validator.
Generic `Wire` bounds therefore discharge source constructor authority before
selection; native codec, layout and size support are separate target obligations.
Entry ingress is checked after generic selection. Internal protocol applications transfer
existing values and do not introduce an ingress boundary. A public native
representation does not grant authority to construct a private source value.

## Callables and static components

```text
math fn square<F: Field>(x: F) -> F { return x * x; }
interface Increment<F: Field> {
  math fn apply(x: F) -> F;
}
component PlusOne<F: Field>: Increment<F> {
  math fn apply(x: F) -> F { return x + 1; }
}
math fn applyIncrement<C: Increment<Fr>>(x: Fr) -> Fr {
  return C::apply(x);
}
```

`math fn` is total, unordered mathematics over `Copy + Drop` values. An ordinary
`fn` is ordered local computation. Both have typed inputs and one logical result,
which may be a tuple or unit. Calls infer direct generic parameters from argument
types where unambiguous; explicit arguments must check. There is no global instance
search, runtime component dispatch or inference through noninjective associations.

An interface declares associated types/domains and math/local member signatures.
A component selects one interface and defines every member exactly once. Associated
runtime types default to no permissions; their promised permissions must be supported
by their representation. Associated `Field` and `Group` declarations expose their
selected domain. Conformance checks callable modes, types, permissions, natural
preconditions and effect allowances. An implementation cannot require more than
its interface allows. Interfaces and components may have static parameters;
member-specific generic parameters require a further conformance contract and refuse.
Records and variants are module declarations. An abstract call or type projection
requires a bound component; a free interface name cannot select an implementation.

Defined local functions infer `stop` and `opaque` effects from their bodies.
An optional `!{stop, opaque}` is an upper bound, and `!{}` forbids both. Abstract
local signatures default to allowing both; math signatures allow neither. An empty
effect allowance never turns ordered code into a total mathematical function.
Opaque runtime intrinsics are not exposed by this profile.

Bodies contain immutable `let` bindings and one final `return`. Arithmetic uses
`*`, `+`, `-`, `==`, parentheses and field/group contracts; operator precedence is
multiplication, addition/subtraction, then equality. Chained equality needs
parentheses. No implicit field conversion occurs. Field literals need a unique
expected field from an annotation, operand, call or result. Installed contracts
check canonical spelling and characteristic bounds without modular reduction.
For an abstract field, only the universally valid literals `0` and `1` are admitted.
Boolean literals need no domain. Record construction supplies every field exactly
once. Variant construction uses `Choice::Some<Fr>(x)` in local code.

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
query. Services cannot enter ordinary types, aggregate fields, messages, local
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
[entry completion contract](../compiler/entry-completion.md).

## Translation and retained interface

The source model has Math, Local and Protocol body modes, checked types, explicit
regions and static arguments. Closing an Entry substitutes already checked bodies;
it never reparses templates. Closed instances are memoized by declaration, mode
and exact static type identity. Only closed definitions enter original MLIR.

Math helpers become private `func.func` definitions. Ordered helpers become
`local.func`. A math helper called inside ordered code retains its mathematical
body and receives a data-only `local.realize` declaration. The local call is an
ordered `local.apply` occurrence; native preparation realizes the helper through
the common polynomial and calculation lowerers before expanding that call.
Formal intermediates never become local runtime values. Inline arithmetic
written directly inside `fn` remains an ordered primitive.
Protocols become `protocol.func`, with explicit `protocol.local_call` for owned calls.
Total operations use their admitted dialect identities; ordered operations use
existing executable bindings. No additional protocol interpreter is introduced.

Products flatten in declaration order. Variants retain a native tagged descriptor
with exact nominal identity and payload layouts. A noncopyable restricted nominal
or associated value has a leading `resource_unit` custody leaf even when its data
is empty. Custody slot identities use the complete SHA-256 digest of canonical source type identity, with collision refusal; traversal order does not affect them. Empty unrestricted products have no leaves, but remain logical values.

Qualified symbol components encode as `s` followed by each component's decimal
byte length, `_`, and spelling. `example::Transfer` becomes `s7_example8_Transfer`.
Specialized symbols use the framed semantic key described above. Ordered site identities
use a per-function preorder occurrence counter, with bounded leaf suffixes where
one logical operation expands. Whitespace and comments do not affect these sites.

Before simplification, the compiler reparses exact emitted bytes, verifies the
whole native module and independently compares actual SSA with checked source.
It consumes every definition and operation, including unused work, and checks
layouts, operands, bindings, modes, helper targets, roles, sites, captures, carry,
variant arms, custody and returns. The comparison never calls emission. An equivalent
but differently structured rewrite can refuse. Inputs, receives, restrictions,
queries, owned calls and protocol results retain exact role sets. Derived math
and aggregate leaves may have wider native availability than the conservative
source value; comparison requires containment and still matches their complete
operation and operand graph.

`CheckedOriginal` owns immutable source, original bytes, comparison counts,
interface, toolchain identity and a bound diagnostic location map. It exposes no
mutable original IR. The existing compiler receives those bytes and the selected
protocol symbol, then emits ordinary `zkc.run/1` and `zkc.program/1` artifacts.
Every protocol in the selected closure passes target preparation.

`zkc.language-interface/2` has exactly these JSON members: `format`, `capture`,
`original`, `toolchain`, `entry`, `protocol`, `roles`, `inputs`, `outputs`, `services`.
Each port has `name`, `type`, `roles`, logical `index`, ordered native leaf indices
in `native`, and a recursive `schema`. The schema records `type`, `custody`,
`permissions`, `leaves`, `fields` and `alternatives`. Fields record `name`, leaf
`offset` and child `schema`; alternatives record `name` and their payload `fields`.
Zero-leaf ports retain empty native indices. Offsets are relative to their product
or alternative payload. Version 1 and unknown versions refuse. No relation or
clause placeholder is present.

Checking compares decoded JSON against the retained original's exact interface,
rejecting duplicate/unknown keys, wrong versions, identities, selections and layouts.
Object member order is immaterial. The original identity hashes exact MLIR bytes
without debug locations under a fixed printing policy. The toolchain identity binds
the installed catalog, compiler source build identity and actual LLVM/MLIR release.
These identify the checked environment; they are not an authenticity signature or
security claim. The independent comparison binds generated coordinates to source
spans; diagnostic paths do not affect capture or original identity.

## Bounds and scope

Requests can lower these ceilings, never raise them. Checks refuse before charged
work or recursive-depth budgets are exceeded; no truncated result is returned.
Definition checking, specialization, layouts, emission, comparison and interface serialization each have a
work budget. The interface writer bounds traversal even when repeated empty types
have no native leaves; its result must also pass the bounded interface reader.

| Quantity | Ceiling |
|---|---:|
| Files; bytes per file; total captured bytes | 256; 1 MiB; 8 MiB |
| Tokens, including trivia and file-end tokens | 1,000,000 |
| Nontrivia token; identifier; module path bytes | 4096; 128; 2048 |
| Parse, expression, import and call depth | 64 each |
| Expanded type depth; type nodes | 32; 100,000 |
| Declarations; source or emitted operations | 10,000; 100,000 |
| Static instances; aggregate leaves/array length | 4096; 1024 |
| Natural monomials; factors per monomial | 1024; 64 |
| Charged work per phase | 1,000,000 |
| Emitted MLIR; interface JSON | 16 MiB; 4 MiB |
| Encoded symbol; diagnostic path bytes | 4096 each |
| Location records, five 64-bit coordinates each | 16 MiB |

The comparator performs whole-module admission once before comparing SSA. Target
admission, expansion and execution retain their own limits. A checked source may
fail target preparation or realization with the failure phase identified.

Relation predicates and attachments, proof construction, source-facing Host inputs, dynamic arrays and
member-generic conformance remain outside this profile. Reserved future syntax
refuses explicitly. Existing IR support remains independent. Structural source
comparison and runtime controls establish neither native Lean correspondence nor
protocol security.

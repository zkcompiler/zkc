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

Capture identity is SHA-256 over a version marker, explicit format, and modules
sorted by logical path. Every name and byte string has an unsigned 64-bit
little-endian length prefix. Diagnostic file paths do not enter identity.

## Types and static terms

```text
domain Fr = field("bls12-381.fr");
domain G = group("bls12-381.g1");
type Vector<F: Field, N: nat> = [F; N];
struct Pair<T: Type> { pub left: T, pub right: T }
enum Choice<T: Type> { Some(T), None() }
```

Runtime types comprise `bool`, `index`, unit `()`, tuples, fixed arrays, installed
fields/groups, nominal records/variants and associated component types. `(T,)`
is a singleton tuple; `(T)` is grouping. A record's identity includes its declaration
and every static argument, including phantom arguments. Variant identity includes
its declaration and static arguments, not only its payload layout. Aliases expand
without creating a nominal identity. Variant payloads are positional; a variant
has one to 32 distinct alternatives.

Domain declarations require an installed identity of the declared sort. A group's
`Scalar` association gives its scalar field. Static parameters use `Type`, `Field`,
`Group`, `nat`, or a selected interface. Naturals are compile-time values, distinct
from runtime `index`. Constants, parameters, addition and multiplication normalize
to polynomials with checked unsigned 64-bit coefficients. Equality compares those
normal forms. Arithmetic overflow refuses rather than wrapping.

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

## Permissions and abstraction

| Permission | Source meaning |
|---|---|
| `Copy` | Reading a value may preserve the original place. Otherwise the read moves it. |
| `Drop` | A continuing path may leave a value unused. |
| `Share` | Participant placement may admit multiple components. |
| `Wire` | The type may be considered for message transport, subject to target codec admission. |

Permissions are independent: `Copy` does not imply `Drop`. Products, arrays and
variants derive permissions from all their element/payload types. Explicit
permissions on a record or variant restrict those derived permissions; they cannot
add permissions that its fields lack. `Field` and `Group` parameters promise `Copy`
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

Protocol ingress and sends refuse private associated representations, restricted
records/variants, and recursively private record fields without an admitted validator.
This remains checked after generic selection. A public native representation does
not grant authority to construct a private source value.

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

## Translation and retained interface

The source model has Math, Local and Protocol body modes, checked types, explicit
regions and static arguments. Closing an Entry substitutes already checked bodies;
it never reparses templates. Closed instances are memoized by declaration, mode
and exact static type identity. Only closed definitions enter original MLIR.

Math helpers become private `func.func` definitions. Ordered helpers become
`local.func`; math helpers used in ordered code receive a local-mode instance.
Protocols become `protocol.func`, with explicit `protocol.local_call` for owned calls.
Total operations use their admitted dialect identities; ordered operations use
existing executable bindings. No additional protocol interpreter is introduced.

Products flatten in declaration order. Variants retain a native tagged descriptor
with exact nominal identity and payload layouts. A noncopyable restricted nominal
or associated value has a leading `resource_unit` custody leaf even when its data
is empty. Slot identities come from a deterministic table scoped to the retained
project. Empty unrestricted products have no leaves, but remain logical values.

Qualified symbol components encode as `s` followed by each component's decimal
byte length, `_`, and spelling. `example::Transfer` becomes `s7_example8_Transfer`.
Specialized symbols use deterministic declaration ordinals. Ordered site identities
use a per-function preorder occurrence counter, with bounded leaf suffixes where
one logical operation expands. Whitespace and comments do not affect these sites.

Before simplification, the compiler reparses exact emitted bytes, verifies the
whole native module and independently compares actual SSA with checked source.
It consumes every definition and operation, including unused work, and checks
layouts, operands, bindings, modes, helper targets, roles, sites, captures, carry,
variant arms, custody and returns. The comparison never calls emission. An equivalent
but differently structured rewrite can refuse.

`CheckedOriginal` owns immutable source, original bytes, comparison counts,
interface, toolchain identity and a bound diagnostic location map. It exposes no
mutable original IR. The existing compiler receives those bytes and the selected
protocol symbol, then emits ordinary `zkc.run/1` and `zkc.program/1` artifacts.
All emitted protocols pass target preparation, even if not selected.

`zkc.language-interface/2` has exactly these JSON members: `format`, `capture`,
`original`, `toolchain`, `entry`, `protocol`, `roles`, `inputs`, `outputs`.
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
Checking, layouts, emission, comparison and interface serialization each have a
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

Services, distributed protocol control/composition, relation predicates and
attachments, proof construction, source-facing Host inputs, dynamic arrays and
member-generic conformance remain outside this profile. Reserved future syntax
refuses explicitly. Existing IR support remains independent. Structural source
comparison and runtime controls establish neither native Lean correspondence nor
protocol security.

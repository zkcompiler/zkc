# Mathematical source language

This profile defines the `.zkc` source language and its translation to
[mathematical protocol MLIR](../compiler/mathematical-protocols.md). It separates
total mathematics, ordered local computation and participant interaction within
the supported source-language path.

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

Capture identity is SHA-256 over the `zkc.capture` marker, explicit source format,
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

Qualified references first resolve their root in the enclosing component and
then the module's visible declarations, including imports. A resolved lexical
root owns the rest of the path: a missing or private member does not fall back
to an unrelated captured module. If no lexical root exists, a qualified module
path is considered. A leading `::` explicitly selects an absolute module path,
for example `::algebra::Fr`. It is reference syntax, not part of module or
canonical declaration names. Optional prefix lookup preserves privacy and
resource-limit diagnostics.

## Definition checking and Entry closure

Analysis checks every definition and Entry reference against declared static
bounds. The resulting `CheckedProject` is immutable. Selecting an Entry creates
an independent `ClosedEntry` containing the reachable specialized bodies and
retained type declarations. Only those bodies and selected relation declarations enter its original MLIR.
Specification clauses make their relations and mathematical dependencies explicit
closure roots, even when execution never calls them. An
unselected Entry's target-admission failure does not invalidate another Entry;
source errors in any definition still reject analysis.

An instance key contains the qualified declaration name and canonical static
arguments, with each component length framed. A declaration fixes its body mode.
Concrete instances retain the encoded declaration symbol when
it fits the native 128-byte identifier limit. Longer paths and specializations use `zkl_`
followed by the complete SHA-256 key digest; distinct keys that produce the same
symbol are refused. No declaration-table index enters the symbol. Local logical
origins name the source definition, allowing a selector to denote its instances.
An origin exceeding 128 bytes uses `zkl_origin_` followed by the SHA-256 digest
of that encoded definition symbol. This origin is shared across specializations;
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

Domain declarations require an installed identity of the declared catalog sort:
`field`, `group`, `commitment`, `transcript`, or `codec`. Static parameters use
`Type`, `Field`, `Group`, `Commitment`, `Transcript`, `Codec`, `nat`, or a selected
interface. Sort names take precedence in static parameter bounds; elsewhere names
retain ordinary module resolution. Field and group domains also denote their runtime
value types. Commitment, transcript and codec domains are static only: they cannot
be runtime ports, tuple/array elements or arguments to a `Type` parameter.

Catalog associations project domains, such as `G::Scalar`, `C::ValueField`,
`C::PointField`, `C::EvaluationField`, `T::ChallengeField`, and
`F::PairingG1::Scalar`. Generic checking uses the catalog's owner/result sorts;
selection requires each association to exist for the installed identity. Closed
associated fields/groups are identical to their directly declared types. A component
may expose an associated domain (`type C: Commitment`); this adds no runtime value
or constructor. Static-only domains have no Copy, Drop, Share or Wire permission.
Naming a transcript domain does not expose managed transcript operations as local
kernels. Runtime constructors retain their separate admitted vocabulary below.

Naturals are compile-time values, distinct from runtime `index`. Constants,
parameters, addition and multiplication normalize
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
normalized assumption, or be reflexive. A stronger closed lower bound with the
same right-hand side suffices: `2 <= N` establishes `1 <= N`. Closed inequalities
are evaluated. There
is no inequality solver or inference by solving equations such as `N + M = 8`.

Catalog capabilities use qualified exported names in the same clause, for example
`where zkc::algebra::TwoAdicField(F), zkc::pcs::MultilinearOpening(C)`.
The catalog defines each predicate's argument count and sorts; arguments may be
associated projections. Names are exact qualified exports, including
`zkc::algebra::Field` and `zkc::curve::Group`. There are no ambient short names or
user-declared facts. Field/Group sorts imply their corresponding facts. Other
symbolic requirements must follow from explicit caller bounds and installed
unary implications; arguments match by normalized source identity. A closed
requirement is checked against installed facts, even in an unused declaration,
and never established by an assumption. These are operation availability
requirements, not cryptographic guarantees. Before source checking, the installed
catalog must sustain inherent sort facts and every installed unary implication.
This preserves generic assumptions when type aliases normalize away their bounds.

Bounds apply to generic type and component applications as well as calls. Parent
bounds are inherited. Associated type declarations cannot introduce their own
capability requirements; inherited component bounds still apply. A component member
cannot add requirements beyond those
provided by its component and interface member; interface bounds are substituted
through the implementation's parameters and associated types. Type applications
inside a clause use its complete set of bounds, independent of written order.
Specialization discharges and removes bounds. They introduce no runtime values,
instance-key fields or equality assumptions. Checking is bounded by the source
work budget and the finite requirement checker's term and assumption limits.

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
`indices`, `polynomial`, `table`, `point`, `round`, `sequence`, `field_array`,
`commitment`, `commitments`, `proof`, `prover_key`, `verifier_key`, `opening_state`
and `opening_states`, as well as scalar `field`, `group`, `bool` and `index`. Runtime collections remain
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
Commitments and proofs may be messages when concrete native admission permits.
Keys and opening state remain local, copyable private data; they do not gain
Share or Wire. Commitment collections retain the native collection policy, which
does not currently admit them as protocol messages. Admitting a constructor does
not admit every domain instance. External key/state inputs still require an
explicit ingress contract; this constructor support supplies none.

`kernel<...>("contract", operands...; "parameter", ...)` calls an installed
source/construction contract from an ordinary local function. The semicolon and
parameters are optional. Static arguments explicitly select the contract's root
terms in declaration order; their kinds come from the catalog. Projections and
input/output types follow that signature. Multiple native results form a source
tuple, and no results form unit. Constant parameters use the contract's own
validation, including field-literal bounds. A generic field admits only `0` and
`1` as literals; concrete field parameters are checked against that field.

Generic checking uses declared capability bounds, inherent Field/Group facts and
installed implications. For example, `where zkc::algebra::TwoAdicField(F)` permits
a generic wrapper for `poly.domain_root`; `where zkc::pcs::MultilinearOpening(C)`
permits generic PCS wrappers rooted at `C` and its associated fields. Every
concrete selection still needs the corresponding installed fact. Native Type roots
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

## Entry jobs

The short form `entry Session = Protocol<Args>;` selects a joint run. A proof Entry
uses an explicit block:

```text
entry Proof = Schnorr<G> {
  prover P;
  verifier V;
  public { base, point };
  accept accepted;
  target knowledge;
  construction fiat_shamir("merlin3.bls12-381.fr64be/0") {
    derive challenges;
  }
}
entry Release = Proof;
```

`prover`, `verifier`, `public`, `accept` and `construction` are required exactly
once, in any order. Proof jobs require two distinct protocol participants. Public
ports are named whole logical inputs and must cover exactly the data ports
available at the verifier, including empty logical ports. Their order is
canonicalized to declaration order. Relation purposes do not authorize inputs.
`accept` names a Boolean output or product field available at the verifier;
its native result index follows the complete flattened output signature.

Optional `complete port.field;` selects a producer Boolean output or product
field, for example `complete result.ready;`. True permits completion; false
withholds that attempt's proof. This does not change the protocol body or add a
guard. Ordinary `prove` uses one attempt and refuses an incomplete result; the
application must call `prove_attempts` with a larger count to authorize retries. Run Entries cannot carry a completion selection.

`construction authored;` selects the existing no-derived-transcript profile.
A `fiat_shamir` construction names an installed suite and exactly one verifier
random service with the corresponding field. Other verifier services refuse.
The native compiler resolves the service's actual ordered query/delivery pairs,
including static applications and repeated occurrences. It checks exact delivered
values and order through the same admission as an explicit native policy. An
unused selected service, omitted delivery or transformed challenge refuses; source
authors do not supply generated site names. These checks establish supported
construction, not a security theorem. Native proof admission and its limits still
apply to the resulting program.

`target` is optional. It names an existing target clause with the same acceptance
selector. Export requires entry-input operands, with witness ports unavailable at
the verifier and other purposes available there. The original gains one
`protocol.statement` at the selected protocol's start, retaining exact argument
components, participant selectors, relation and Boolean result index. Ordinary
clauses remain metadata; selecting no target emits no statement. Output-bound or
more general clauses remain valid attachments but cannot be selected for this
native statement ABI.

An Entry may name another complete Entry, including one declared later. Aliases
inherit the protocol, closed arguments, setup associations and every job choice. Cycles, partial
overrides and static re-specialization of an Entry refuse. Alias resolution uses
the source call-depth and work bounds.

### Setup associations

Run and proof Entries may associate inputs with named setup slots:

```text
entry Proof = Opening<Kzg> {
  setup pcs { vk, pk, statement.commitment };
  prover P;
  verifier V;
  public { vk, statement, point };
  accept accepted;
  construction authored;
}
entry Session = Opening<Kzg> { setup pcs { vk, pk, statement.commitment }; }
```

A selector names an input or a visible product subtree. It retains logical port
and field indices; closure derives its native leaves. The selected subtree must
contain at least one setup-bearing leaf. Ordinary siblings are ignored. Native
collections remain one operand, including setup-bearing variant alternatives.
Paths cannot project through associated representations or variants.

Every setup-bearing input leaf must occur in exactly one slot. Selectors cannot
overlap, including within one slot. Names are unique identifiers, slots are
nonempty, and at most 64 slots are admitted. Association applies to every role
component of the logical input. The installed setup-bearing profile is
multilinear KZG, including keys and nested commitment/proof data. Merkle commitments
do not require a setup key. Slots do not introduce runtime operations or authorize
setup material.

A proof slot must include at least one whole public verifier-key input available
at the verifier. Every verifier-key input must satisfy that rule; at most 64
verifier-key ports are admitted in a proof Entry, independently of the slot count.
Prover-key inputs must remain at the prover. The Host pins
all keys in one slot to the same application-selected identity. Multiple slots
may select different identities. A run slot does not require a verifier-key input.
A block with only setup choices selects a run; adding any proof choice requires
the complete proof block. Empty blocks refuse.

Explicit setup association admits whole builtin `prover_key` and `verifier_key`
input ports through checked Host initialization. It does not grant `Wire`,
message transmission, nested/private key construction or opening-state ingress.
Other input constructors keep their existing permission requirements. Current
source slots require an input association; they do not express receive-only keys
or a separate expected key per receive site. The native Host's authorized setup
registry governs incoming PCS headers. An authorized value may decode and be
observed before `pcs.check` rejects a different explicit verifier key. Slots do
not name outputs: an unchecked returned commitment or proof is authorized but
not automatically tied to a specific output setup.

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

## Translation and retained interface

The source model has Math, Local and Protocol body modes, checked types, explicit
regions and static arguments. Closing an Entry substitutes already checked bodies;
it never reparses templates. Closed instances are memoized by declaration, mode
and exact static type identity. Only closed definitions enter original MLIR.

Math helpers become private `func.func` definitions. A selected formula relation
adds a non-callable `relation.declare` and a private Boolean `func.func`; its exact
link is retained in the interface. Opaque and captured relations emit declarations
only. Predicate helpers have no executable symbol uses. Every selected predicate
undergoes bounded helper expansion and polynomial observation checks on scratch
copies before interface admission, including unused observations. Ordered helpers become
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
protocol symbol. Run jobs emit `zkc.run/0`; proof jobs use the native proof policy
and deployment schemas. Both contain ordinary `zkc.program/0` participant programs.
Every protocol in the selected closure passes target preparation.

`zkc.language-interface/0` has exactly these JSON members: `format`, `capture`,
`original`, `toolchain`, `entry`, `protocol`, `protocols`, `relations`, `job`,
`setups`. `protocol`
selects one symbol from `protocols`. Every original protocol and relation appears
exactly once. Unknown tags, missing members and extra members refuse.

A run `job` has only `kind: "run"`. A proof job has exactly `kind: "proof"`,
`prover`, `verifier`, `public`, `acceptance`, `completion`, `target` and
`construction`. Roles are roster names; `public` is a sorted array of logical
input indices. Acceptance uses the selector format below. Completion is either
a producer Boolean output selector or JSON null. Target is a clause name or JSON null. An authored
construction has only `kind: "authored"`; a derived construction has exactly
`kind: "fiat_shamir"`, `suite` and logical `service` index. Independent reading
checks these choices against the original signature and the exact native statement.
Source comparison separately checks that they match the selected checked Entry.

`setups` is an array of records with exactly `name` and `inputs`. Each input
selector has exactly `port` and `path`, using logical input and product-field
indices. Native slices are derived from the checked schema. Readers check exact
coverage, nonoverlap, nonempty selections and proof-key availability. Source
comparison additionally binds slot names and selector choices to the checked
Entry. Setup metadata is part of authenticated package bytes.

Each protocol record has `symbol`, `roles`, `inputs`, `outputs`, `services` and
`clauses`. Each port has `name`, display `type`, `roles`, logical `index`, ordered
native leaf indices in `native`, and recursive `schema`. A schema has `kind`,
`identity`, display `type`, `custody`, `permissions`, `leaves`, `fields` and
`alternatives`. Fields have `name`, leaf `offset` and child `schema`; alternatives
have `name` and payload `fields`. Zero-leaf ports retain empty native indices.
Offsets are relative to their product or alternative payload.

A relation record has `symbol`, `inputs` and `definition`. Each formal has `name`,
`purpose`, ordered `native` indices and `schema`. Definition records have exactly
`{kind, function}` for a formula, `{kind}` for an opaque declaration, or
`{kind, asset}` for R1CS/AIR. Their identity triple comes from the actual native
declaration. Formula kind is `zkc.language.formula/0`, key is the closed relation
symbol, and revision is a lowercase SHA-256 representation digest. Its material is
length-framed in this order: kind, predicate helper symbol, decimal logical input
count, each full logical schema digest and purpose, decimal transitive helper count,
then each helper symbol and definition digest, sorted by symbol. A definition digest
hashes framed `zkc.language.formula-helper/0` and canonical generic MLIR without
locations. Frames use unsigned 64-bit little-endian lengths. The closure includes
the root; shared helper definitions are hashed once per immutable checking phase.
Printing pins every flag, disables hex output and uses elision thresholds above
admitted payload sizes, independent of process-global MLIR flags.

The schema digest hashes framed `zkc.language.schema/0`, textual kind, nominal
`identity`, custody, Copy/Drop/Share/Wire (each `0` or `1`), leaf count and ordered
leaf spellings, field count and ordered fields, then alternative count and ordered
alternatives. Counts and offsets use unsigned decimal text. A field contributes
its name, offset and child schema digest; an alternative contributes its name,
field count and fields. Display type spelling is excluded. This binds member names
and structure across captures even when nominal names and native leaves agree.
These identities retain names and printing policy; they are not semantic equivalence.
The formula helper name is `zkf_` followed by lowercase SHA-256 of the bytes
`zkc.language.predicate:` concatenated with the native declaration key. Its JSON
link must equal that derived name. Native formula admission requires a private,
nonempty body with the declaration's signature and no executable references, then
checks polynomial observations on bounded detached clones using the original
helper table. The supplied original is unchanged; limits remain `source.limit`
and invalid observations are `target.admission` with source attribution.
Captured kinds are `zkc.relation.r1cs/0` and `zkc.relation.air/0`, with canonical
asset identity as key and `0` as revision. The reader requires the matching
immutable admitted `RelationAsset` handles, supplied outside this small JSON.

Each clause has `name`, `kind`, `subject`, `residual` and `decision`; absent optional
fields are JSON null. An application has a relation symbol and ordered `operands`.
Selectors have `direction` (`input` or `output`), logical `port` index, field-index
`path` and actual `role` name. Native slices are derived from the admitted logical
schema, rather than supplied again. Relations compare exact logical identities.
Clauses remain on closed component declarations; original `protocol.apply`
occurrences own their operand/result and role mappings. There is no separate
serialized application graph.

The standalone `readInterface` API admits original MLIR and checks the interface
against its exact byte hash, selected protocol, flattened types and participant
roles. It checks contiguous port/field indices, complete native coverage, variant
labels/payloads, custody prefixes and managed-service contracts. Logical types
with the same identity must have consistent kind, label and schema. Kinds are
`boolean`, `index`, `field`, `group`, `unit`, `tuple`, `array`, `record`, `variant`,
`associated` and `builtin`. Scalars have their matching single native leaf; unit
has none. Tuples/arrays have positional fields, with one common element identity
for nonempty arrays. Records have identifier fields; associated representations
have exactly one `value` field. Only variants have alternatives. An empty product
cannot hide data leaves. Custody belongs only to nominal kinds.

`identity` is the lowercase SHA-256 digest of the closed canonical source type
key used by nominal custody and variant descriptors. It includes static arguments,
including phantom and zero-length array element types. The key encodes the type
kind tag, symbolic flag, length-framed domain and normalized dimension, then the
argument count and recursively framed argument keys; a natural uses its kind tag
and framed normalized dimension alone. Tags follow `Type::Kind`; framing is an
unsigned decimal byte length followed by `:` and the exact bytes. The toolchain
identity fixes this encoding. Native custody carries the exact digest; a variant
carries its preimage under the `zkc.language` nominal namespace. The reader checks
both anchors. Other source type identities remain source assertions until checked
against the retained project. `type` is display text, never equality authority.
An empty array's element meaning is bound by its identity and source agreement;
no selectable element field is invented for it. Promised Copy, Drop and
Wire permissions cannot exceed native leaves; aggregate Share is checked through
logical children while native admission checks actual placement.

`compareInterface` checks the decoded view against the retained source layouts,
ports, services, relations and clauses. It independently checks the clause inventory
against immutable templates and captured `spec` block/clause spans and tokens.
Omitting a clause and its predicate together cannot satisfy source correspondence.
This check does not replace native admission or the source-to-original SSA check.
`admitOriginal(entry, original, interface)` performs formation, formula admission,
source-to-SSA comparison, structural interface decoding and source-interface
comparison on one parsed original. It then requires byte agreement with canonical
source emission for both original and interface, fixing declaration order, symbol
spelling and diagnostic locations. It retains those exact bytes and returns
`CheckedOriginal`. `prepareOriginal` emits and runs the same independent checks;
its emitted bytes need no second canonicality comparison.
`CheckedOriginal::interface()` exposes the checked view; `selectedProtocol()`
selects its Entry's protocol record. Host authentication must bind the retained
interface bytes, not arbitrary caller JSON that happens to compare semantically.
The byte overload of `inspectApplications` admits the entire original and interface before calling a
read-only visitor for each static `protocol.apply`. Each occurrence exposes its
caller/callee records, actual MLIR operation, callee-to-caller role substitution,
and clauses bound to actual operand/result SSA values. Its path indexes operations
in the caller block and then enclosing `protocol.repeat` blocks. Repetition is one
static occurrence; runtime iterations and transitive calls are not expanded. This
keeps contracts on definitions and derives their uses from the original program,
without serializing another call graph. The operation, values and referenced views
are borrowed for the callback only. Visitor work is the caller's responsibility;
traversal and binding use the source work and nesting limits. Structural inspection
has the standalone reader's guarantees. The `CheckedOriginal` overload additionally
uses its retained source authority and captured assets. Selector paths cannot
project through associated representations, even when structurally copyable.

`checkInterface` compares decoded JSON against the retained original's
exact source interface. This binds source names, nominal schemas, permissions and
capture/Entry selection. The standalone structural view does not establish source
correspondence or constructor authority and cannot authorize private input decoding.
Both readers reject duplicate/unknown keys, unknown tags and malformed metadata.
Object member order is immaterial for semantic interface comparison; admission of
a published checked original requires canonical bytes. The original identity hashes exact MLIR bytes
without debug locations under a fixed printing policy. The toolchain identity binds
the installed catalog, compiler source build identity and actual LLVM/MLIR release.
The catalog uses `zkc.language-catalog` length framing. Kernel rows contain
their signatures and parameter contracts.
Source availability still requires an installed declaration at an admitted
authoring stage, with all applicable semantic-facet and source-effect checks.
The identities bind the checked environment; they are not an authenticity signature or
security claim. The independent comparison binds generated coordinates to source
spans; diagnostic paths do not affect capture or original identity.

External interface JSON uses unique decoded object keys and canonical unsigned
decimal numeric tokens. Signed, leading-zero, floating and exponent spellings
refuse. Boolean and null tokens retain ordinary JSON grammar and remain subject
to the interface schema. Lexical limits apply before schema admission. External
input passes through the byte reader; an already decoded JSON value does not
retain its original numeric spelling.

### Published Entry package

`packageEntry` accepts only an owned `CompiledEntry`. It emits `zkc.entry/0`
with exactly `format`, `original`, `interface`, `artifact`, and `options`.
Original MLIR, interface JSON and native run bundle or proof deployment are exact
strings. Options contain Boolean `simplify` and `release_storage`. The job kind
and complete source interface remain in the retained interface, avoiding a second
name or participant table. Package SHA-256 covers the exact emitted bytes,
including source capture, selected Entry, toolchain and compilation options.
Complete Entry aliases can share executable bytes while naming different packages.

The whole escaped package is bounded to 64 MiB; callers may lower this limit.
The original, interface and artifact retain their own component limits. The
`language-package` command writes exact package bytes without a trailing newline.
Package identity is distinct from the original identity used by native proof
binding. A consumer must obtain its expected package identity independently;
internal hashes do not authenticate a supplied package. Retaining MLIR does not
require the Host to recompile it or establish a security theorem.

### Rust interface admission

The native Host reads `zkc.language-interface/0`. It checks strict object members,
including required nullable fields, before using source names. Recursive schema
validation preserves kind, exact logical identity, permissions, custody, field
slices and nominal alternatives. Every logical port remains present, including
zero-leaf values. Selectors and Entry choices must agree with those schemas.

Compiler publication and both readers bound interface bytes at 4 MiB, JSON
nesting at 256 and lexical nodes
at 200,000 before typed decoding. Scalar tokens have at most ten bytes; encoded
string tokens have at most six times 256 KiB. Decoded strings retain their owning
name/type limits. Schema depth is at most 32, each aggregate has at most 1,024
leaves, and validation has a cumulative work allowance of 1,000,000. Native leaf
parsing retains its own structural bounds; cached descriptors have an additional
16 MiB total retained charge. Work bounds apply independently to each admission
algorithm; a caller may also lower the compiler's phase limits. Unknown and
duplicate fields refuse. The bounded tree format retains self-contained schemas;
identities permit descriptor reuse without introducing cyclic schema references.

Native binding checks the exact artifact bytes from the authenticated package,
selected entry, participant roster, logical data types, services and output
mappings. Proof binding additionally checks the original digest, original
acceptance port, public inputs, construction and compile options against the
admitted deployment. Run bundles carry no independent original/options record;
those choices are authenticated package metadata. The compiler/checker publication
path owns source correspondence and relation meaning. Reading metadata or binding
its ports does not interpret MLIR or establish a protocol security judgment.

### Named setup authority and initialization

Both source Hosts accept `entry::SetupAuthority`, whose `keys` map covers setup
slot names exactly and supplies independently authorized verifier-key identities.
Unknown or missing names refuse with `entry-setup-authority`. The adapter derives
native maps from the authenticated interface: run maps use role-local operand
indices; proof maps pin every original public verifier-key index and associate
other setup-bearing inputs with the slot's lowest verifier-key index. Native
admission independently checks complete coverage and concrete types.

The source Host derives one immutable port plan from the checked interface. It
records role order, public/private inputs, setup-key ports, selected outputs and
external services. Generated bindings, file requests and native ABI comparison
use that plan. Native artifact facts are read independently during comparison.

`RunRequest::setups` and `ProofRequest::setups` supply verifier-key bytes for every
slot exactly. The Host authenticates and imports them through its existing bounded
setup loader. Whole verifier-key inputs are initialized automatically: applications
omit them from both named role inputs and named public values. Supplying a second
value under that port name refuses. Prover-key inputs remain explicit named
`Value::Leaf` values containing authenticated `ProverMaterial` or a
`ProverKeyFile` with an independently expected material fingerprint. Other
constructors, including arbitrary native key values, refuse.

Each invocation checks prover material against its assigned slot. Immutable
material may be reused across calls; runtime accounting and setup checks still
apply per call. Names and byte/copy limits are checked before constructing public
key input vectors. Native input admission owns key parsing, canonical bytes,
setup metadata checks and execution budgets. This does not establish honest setup
generation or authorize a private source representation.

### Named run calls

Rust `entry::RunEntry::admit` retains an authenticated package, validates its
interface and admits the exact run artifact through `RunHost`. Proof jobs use a
separate API. Before accepting a run, every logical output must be copyable and
have no affine custody; unsupported custody returns `entry-output-custody`.
Every ordinary input must have source `Wire` constructor permission or admission
returns `entry-input-constructor`. Whole builtin key ports instead use the explicit
setup route above. These checks precede native bundle admission.

`RunRequest` names every participant and its ordinary/prover-key input ports
exactly. Its service map supplies optional budget overrides for declared services;
unknown names refuse. Each role remains required even when it has no inputs. Unit values and empty
products also remain explicit. Records use exact field names, tuples and arrays
use ordered elements, variants name an active alternative and its payload fields,
and associated values wrap their checked representation. Numeric alternative
field names follow the declared payload order. The checked schema supplies all
native slices and nominal descriptors; display type strings are not executable
layout descriptions.

Ordinary leaves use `entry::Value::Leaf(InputValue::Native(...))` or `Wire`.
The admitted source schema's `Wire` constructor permission applies recursively
through products and alternative payloads. A matching native representation does
not confer private constructor authority. Source randomness comes through named
managed services; setup keys use the named initialization route above. Native
leaves retain the upstream cryptographic library invariants stated
by the run Host. Variant payloads can mix native and wire data; common admission
checks complete types, aggregate collection counts and retention before decoding
or constructing payload containers.

`prepare` consumes the named request and returns a single-use plan backed by the
same native Host. `execute` retains the complete native outcome, usage and cleanup
report. On complete execution with successful cleanup, it reconstructs all named
results, including empty products. Other outcomes publish no complete logical
result; they remain visible in the native report. An unexpected reconstruction
failure has its own `output_error` and cannot become successful named output.
`RunReport::is_success` checks completion, successful cleanup and decoded outputs;
`into_result` preserves the full report on either branch. A successful interactive
run does not imply a protocol acceptance predicate: the caller must inspect its
explicit result values. No source evaluation or protocol-specific execution loop
is added.

### Named proof calls

`entry::ProofEntry::admit` authenticates the same package/interface boundary and
binds the exact deployment through `NativeDeployment`. Inputs retain the source
constructor requirement and outputs must be copyable without affine custody.
`prove` and `verify` take separate `ProofRequest` values; the verifier receives
only its own inputs and the candidate proof. Neither method needs a live peer.
The SDK supplies public values once through `ProofRequest::public`; `private`
contains only nonpublic inputs and external service budgets. The source adapter
assembles shared operands from these public values. Private overrides refuse;
native admission still checks canonical agreement. Setup imports may reuse
identical canonical bytes under the same authorized pin within an invocation;
each native operand retains its usual resource charge.

Each request also supplies application context bytes and an optional transcript
budget. Public values remain independently authorized by the application.
Zero-leaf public and private inputs remain required in their respective maps.
The selected derived verifier service is compiler-owned and cannot also appear
in the caller's service map. Products and nominal alternatives use the same
logical schema and common admission as run calls.

`ProofOptions::binding` defaults to `TranscriptRequired`. Authored construction
requires explicit `AllowHeaderOnly`; otherwise admission returns
`entry-proof-binding-policy`. `binding_scope()` and each `ProofReport` distinguish
`Transcript` from `HeaderOnly`. This identifies the selected binding mechanism,
not a cryptographic security judgment. The authored header checks consistency;
it does not by itself prevent rewrapping a proof under another context.

A successful `ProofReport` reconstructs that participant's named original
outputs, including empty products. Rejection, stop, refusal or cleanup failure
publishes no named outputs; the native outcome, usage and cleanup remain visible.
Unexpected reconstruction failure is recorded in `output_error`. An outer `Ok`
means preparation succeeded, not proof acceptance. The report is `must_use`;
`is_success()` checks execution, cleanup and output reconstruction together.
`into_result()` returns the entire report on either branch, preserving rejection
and cleanup details.

### Attempts and operational defaults

When completion is selected, `prove(request)` delegates to the native attempt
controller with a one-attempt limit. A false completion withholds proof bytes and
returns `native-attempt-limit`; it does not authorize another attempt.
`prove_attempts(request, AttemptOptions)` requires the Entry's `complete` choice,
otherwise it refuses with `entry-attempt-completion`. The adapter resolves that
logical selector to its checked original native output and delegates to the
existing attempt controller. `AttemptOptions` supplies count (default one) and
per-attempt proof-byte ceiling (default the native proof limit). The admitted
`ProofOptions::capacity` supplies cumulative interpreter work and payload limits;
external work keeps its existing Host ceiling. Native policy admission checks all
limits before loading resources. No raw native port policy is needed in the
source API; direct IR callers retain the native API.

The authenticated Entry interface and independent source comparison own the
completion selection. It is an application policy, so the native artifact does
not repeat that selection. Native attempt-policy admission checks that the
selected original output maps to a prover Boolean output; the controller uses
its actual result to decide whether to publish a proof.

Managed providers persist across attempts with their actual remaining allowances.
A false completion discards its proof buffer; fatal stops and cleanup failures do
not become retries. Only final successful outputs are published. The source
profile has no affine RNG input constructors; the native policy therefore has no
RNG input/successor pairs. Extending that ingress needs its own custody mapping.
Neither the final proof nor the policy digest establishes the retry distribution.

An omitted declared service budget uses `entry::DEFAULT_DRAW_BUDGET` (1,000,000),
the current native admission ceiling. `ProofRequest::transcript_budget` is optional:
omission uses that allowance for derived construction and zero for authored jobs.
Explicit values, including zero, override defaults. A nonzero explicit transcript
budget for an authored job still refuses. Unknown service names and attempts to
supply the compiler-owned derived service still refuse.

These are operational allowances, not inferred draw counts. They allocate no
random tape and confer no independence or honest-provider claim. Existing native
resource/transcript observations report consumed transitions and remaining
allowances. Provider budgets persist for the whole invocation; each derived
attempt transcript starts its separately bounded allowance. Callers can lower
budgets and native hard limits still apply.

### File adapters and Rust bindings

The CLI and generated bindings use the same named Hosts. `zkc compile` invokes
a compiler selected by an explicit path or absolute directories in the caller's
trusted `PATH` (default
`zkc-compile`), reports its resolved path and toolchain, captures its
bounded package output and publishes exact bytes with their SHA-256. Existing
packages require a caller-supplied expected digest for `run`, `prove`,
`verify` and `bindings`. No digest derived from candidate bytes authorizes them.

A `zkc.entry-run/0` request has required `format`, `session` and `roles`, plus
optional `setups` (default empty). Every role record has required `inputs` and
optional `services` (default no overrides). A `zkc.entry-proof/0` request has
required `format` and `public`, plus optional `inputs` (private value map,
default empty), `services` (default no overrides), `context` (default empty hex), `transcript_budget` (default absent) and `setups`
(default empty). Public and input maps use exact logical port names. The file
adapter fills shared role operands from `public`; `inputs` cannot repeat or
override public names. Independent callers still provide their own public maps. Setup
material maps slot names to canonical verifier-key bytes in hex. Whole VK ports
are omitted from value maps. A whole prover-key port supplies exactly `path`
and `sha256`; key paths resolve from the invoking process working directory.

Values use Boolean JSON for Boolean source values, unsigned 64-bit integers for
indices, null for unit, arrays for tuples/fixed arrays, and exact named objects
for records. A variant has exactly `case` (the alternative name) and `fields`
(a named object, including numeric field names for positional payloads).
Associated representations are transparent. Installed mathematical leaves use
hex of their complete canonical native wire frame. Native decoding retains its
exact type, canonicality, setup and quota checks. Typed Rust ingress avoids this
file encoding and retains its independent immutable-value validation.

CLI inputs and authority use bounded regular-file descriptors; nonregular files
refuse before execution. File requests have a 16 MiB byte limit, depth at most 72 and a 200,000-node
allowance including object keys. Decoding rejects duplicate keys, unknown record
fields, trailing documents and numeric values outside unsigned 64-bit naturals.
The optional application authority file is bounded by 64 KiB and contains exactly
`format: "zkc.entry-setups/0"` and `keys`, mapping source slots to expected 32-byte
key identities in hex. Authority is separate from invocation material.

Diagnostics omit returned values and proof payloads. Explicit `--results` output
uses `zkc.entry-outputs/0`, with `roles` for a run or `values` for a proof call.
Serialization uses admitted native capacity, a 16 MiB whole-file limit and only
installed Wire encodings for native leaves. Every requested output is encoded and
staged before publication. Preflight, encoding or staging failure preserves all
existing destinations. The final publication order is proof, then optional results.
Output destinations must differ from each other and all input/configuration paths,
including referenced prover-key files, parent directory aliases and, on Unix,
existing hardlinks. Symlink destinations refuse. The plan is rechecked before publication;
this configuration check does not isolate filesystem races. On Unix, staged outputs have mode `0600`. Each file is atomically
replaced. If a later replacement fails, the report identifies earlier publications
and retains the execution report. This is not a multi-file transaction or a crash
durability guarantee. No automatic retry follows a publication error. Success exit status requires complete execution,
cleanup and requested publication.

Generated Rust modules pin the exact package digest and delegate admission to the
common Host. They provide named participant/public input and output structures,
structural value conversions, and Rust representations of Boolean/index/unit,
array and nominal data. Mathematical leaves remain `entry::Value`, with concrete
domain and authority validation at invocation. Identifier conversion avoids Rust
keywords and collisions while retaining original source keys in conversions.
Field and variant names retain exact source spelling. Reserved path names, `_`
and names beginning `__zkc_` use that prefix followed by hex of the full source
identifier. Generated naming-lint allowances cover these intentional spellings;
they do not disable general warnings. Fixed public-interface names are allocated
before source-derived names. Role conversion helpers and name constants delegate
to the same request/result maps.
Bindings emit no protocol algorithm or new execution/authority implementation.
Generated source is bounded by 16 MiB. Reauthorizing a different package requires
regenerating or deliberately replacing its pin.

## Bounds and scope

Requests can lower these ceilings, never raise them. Checks refuse before charged
work or recursive-depth budgets are exceeded; no truncated result is returned.
Definition checking, specialization, layouts, emission, comparison, predicate admission
and interface serialization each have a work budget. The capture-wide specification
inventory has a separate phase budget from per-Entry interface comparison. The interface writer bounds traversal even when repeated empty types
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

Parse depth bounds both recursive parsing and constructed type/natural syntax
trees, including operator chains.

The comparator performs whole-module admission once before comparing SSA. Target
admission, expansion and execution retain their own limits. A checked source may
fail target preparation or realization with the failure phase identified.

Receive-only setup slots, per-receive setup pins, general private ingress validators,
dynamic source arrays and member-generic conformance remain outside the implemented
profile. Reserved future syntax
refuses explicitly. Existing IR support remains independent. Structural source
comparison and runtime controls establish neither native Lean correspondence nor
protocol security.

# Source definitions and types

This native contract defines captured modules, declarations, types and source bodies.

## Capture and names

A capture is a nonempty map from logical module paths to exact UTF-8 bytes.
Each file starts with `module path;` matching its captured name. Module paths
use `::`; every segment follows the [Unicode 17 identifier profile](lexical.md).
Names retain exact NFC UTF-8 bytes, with no silent normalization. The lexical
contract also defines contextual keywords, ASCII strings, UTF-8 comments and
mathematical tokens. Tokens retain trivia and original UTF-8 byte spans.

Module declarations are private unless prefixed with `pub`. Interface/component
members are exposed through their owner; associated representations retain their
constructor privacy. A declaration can be named
through `use module::{Name, Other};` or by its qualified path when its module
is captured. Imports never discover files. Imports, declarations, static parameters
and local bindings cannot shadow visible declarations or module aliases. Lexical binding rules are
defined in [protocol bodies](protocols.md#bindings-and-local-control). Imports, types and call graphs
must be acyclic. Every declaration is checked, including unused generic bodies.

Capture accepts named assets as explicit bytes alongside modules. Formats are
`r1cs-json`, `r1cs-binary`, `air-json`, `ring-json` and `relation-bundle-json`;
checking never opens a diagnostic path. The CLI accepts `--asset=NAME=FORMAT=FILE`.
Analysis admits every supplied asset, including unused ones, through the
existing bounded R1CS, AIR, [ring expression](../domains/ring-expressions.md)
or [relation bundle](../domains/relation-bundles.md) reader. Canonical
relation identity retains constraint content, field, statement layout and AIR row
scopes; a ring or bundle asset's identity is its canonical definition identity.
Admission does not prove a source-circuit interpretation or key/setup correctness.

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

The CLI accepts a TOML manifest with `format = "zkc.project/0"`, a nonempty
`modules` table mapping logical names to paths, and an optional `assets` table
mapping names to tables with exactly `format` and `path`. Unknown or duplicate
keys and unsupported types refuse. A manifest is a bounded regular file (at most
1 MiB); modules and assets together are limited to 256 files. Each supplied path
is nonempty, contains no NUL, and is at most 4096 bytes.

`--project=FILE` selects an explicit manifest. Otherwise explicit `--module` or
`--asset` inputs disable discovery; they cannot be combined with `--project`.
With neither option the CLI uses the nearest `zkc.toml` in the current directory
or its ancestors. The first filesystem entry is final: malformed, unreadable,
nonregular and dangling-symlink candidates fail rather than fall back to a parent.
Relative mapped paths resolve against the selected manifest's visible parent,
including symlinked manifests. Explicit command-line paths use the invocation
directory. Absolute paths, `..` and ordinary symlink resolution are supported;
imports do not scan directories. SDK captures never discover a manifest.

The manifest carries locations and formats, not execution choices or secrets.
Its path, formatting and discovery location are report metadata and do not enter
capture identity. Identical named source/asset bytes have the same capture.
The CLI protects the manifest, mapped inputs and selected compiler from output
publication, including file aliases. See [Entry selection](entries.md#selection)
for canonical names and check scopes, and the [project guide](../../language/README.md#project-inputs)
for default output paths.

Qualified references first resolve their root in the enclosing component and
then the module's visible declarations, including imports. A resolved lexical
root owns the rest of the path: a missing or private member does not fall back
to an unrelated captured module. If no lexical root exists, a qualified module
path is considered. A leading `::` explicitly selects an absolute module path,
for example `::algebra::Fr`. It is reference syntax, not part of module or
canonical declaration names. Optional prefix lookup preserves privacy and
resource-limit diagnostics.

### Module imports and operator scope

`use zkc::vector;` imports the alias `vector` and that module's public operator,
delimiter and reduction bindings. `use zkc::vector as vec;` changes the alias.
A selected import such as
`use zkc::vector::{Vector, add};` imports only those names;
`use zkc::vector::{Vector, operator +};` also imports the selected public operator
family, including all exported fixities for the token. `notation ⟪` selects a
public delimiter shape; `reduction ∑` selects a public reduction binding.
A qualified reference alone activates no notation.
`pub use` reexports the selected names, aliases and bindings with their original identities; ordinary
imports remain private. Duplicate imports of the same identity are harmless.
Conflicting names/aliases, missing exports and import cycles refuse. Captured
module ordering and import ordering do not choose overloads. Exported bindings
carry their resolved descriptors, including those introduced privately; their
targets must still be public. [Notation scope](notation.md#imports-and-lexical-scope)
defines descriptor conflicts, whole-module visibility and local replacement.

The reserved `zkc::prelude` module belongs to the compiler installation. Its exact
source is embedded and included in installation identity. Captures cannot supply
that module or claim an installation origin. Its public scalar operator bindings
are visible by default; its function names require qualification or explicit
import. The prelude itself has no imports or inherited operator environment.
There is no runtime source-file lookup. Capture identity and captured file/byte
limits exclude the prelude; token, declaration, operation and work limits include
its checking. `Analysis::sources()` and `CheckedProject::sources()` include both
origins and index all diagnostic spans. `capture().sources()` includes only
captured inputs.

## Definition checking and Entry closure

Analysis first collects fixed declaration headers and body token ranges, resolves
the existing import graph, then parses bodies under immutable notation environments.
It checks unused bodies too; [staging](notation.md#staging-and-retained-evidence)
defines declaration-prefix collection and work accounting.

Analysis completes each callable's contract from its declaration and body,
then checks applications against that contract. Callers never determine a
definition's inferred result or preconditions. The resulting `CheckedProject`
is immutable. Selecting an Entry creates
an independent `ClosedEntry` containing the reachable specialized bodies and
retained type declarations. Only those bodies and selected relation declarations enter its original MLIR.
Specification clauses make their relations and mathematical dependencies explicit
closure roots, even when execution never calls them. An
unselected Entry's target-admission failure does not invalidate another Entry;
source errors in any definition still reject analysis.

An instance key contains the qualified declaration name and canonical static
arguments, with each component length framed. A declaration fixes its body mode.
Declaration symbols use the [UTF-8 segment encoding](translation.md#source-and-native-names)
for ASCII and Unicode names alike. Concrete instances retain that symbol when
it fits the native 128-byte identifier limit. Longer paths and specializations use `zkl_`
followed by the complete SHA-256 key digest; distinct keys that produce the same
symbol are refused. No declaration-table index enters the symbol. Local logical
origins name the source definition, allowing a selector to denote its instances.
An origin exceeding 128 bytes uses `zkl_origin_` followed by the SHA-256 digest
of that encoded definition symbol. This origin is shared across specializations;
the exact generated symbol and retained closure identify one specialization.
Adding an unreachable definition changes capture identity but does not rename
reachable instances. Template bodies are shared immutably. Specialization has its own work and instance budgets; retained templates do not consume the emitted-declaration allowance. Only reachable body copies are specialized before original emission.

`zkc check --declarations` adds a diagnostic array of completed public callable
contracts from captured modules, sorted by qualified name, under `declarations`.
Installation declarations remain accessible through the checked SDK graph. Callable members
are visible through their public owner. Members identify that owner and mark
inherited static parameters; `abstract` distinguishes interface declarations
from definitions with bodies. Each item reports its kind, static
parameters and permissions, role roster, data/service argument order, typed
ports, services, requirements, body effects (or abstract allowance), and captured
module byte span and source `origin`. `definition` is `body`, `abstract` or
`primitive`; primitive definitions also report the installed `primitive` identity.
Natural/capability bounds retain their inferred flags; explicit
or inherited effect allowances remain separate; abstract declarations always
include their effective allowance, including the default. Type and natural
strings are descriptive mathematical spellings,
not a serialization accepted by the checker. The view never supplies linking
or admission authority. Its unembedded JSON array is bounded by `interfaceBytes`;
an exceeded bound refuses without publishing a partial result.

The direct compiler and CLI emit the same flat `zkc.source-check/0` successful
result. It records `status`, `phase`, `scope`, `capture`, `installation`, optional
`declarations`, and `entry`/`original` for Entry scope. The CLI adds `compiler`.
The separate [notation inspection view](notation.md#inspection) describes syntax
environments and occurrences; it does not change callable declaration records.

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
`Type`, `Field`, `Group`, `Commitment`, `Transcript`, `Codec`, `Ring`, `Bundle`,
`nat`, or a selected interface. Sort names take precedence in static parameter
bounds; elsewhere names retain ordinary module resolution. Field and group
domains also denote their runtime value types. Commitment, transcript and codec
domains are static only: they cannot be runtime ports, tuple/array elements or
arguments to a `Type` parameter.

### Asset domains and projections

```text
domain Product = ring(asset product);
domain Recurrence = bundle(asset recurrence);
fn round<F: Field, A: Ring>(values: Vector<F>) -> Vector<F>
    where 1 <= A::Inputs, A::Outputs <= 1 {
  let rows = kernel("index.div", kernel<F>("vector.length", values),
                    index<A::Inputs>());
  return kernel<F>("ring.affine_sum", values, values, rows; A);
}
```

An asset domain names a captured ring expression (`ring`) or relation bundle
(`bundle`). The declaration resolves the captured name at definition checking:
an absent name or an asset of another kind refuses. The domain denotes the
asset's canonical identity, so two declarations over the same admitted contents
are the same term. `Ring` and `Bundle` are the static sorts of these terms. They
are capture-local: an asset term never enters the installed catalog identity,
never becomes a binding static argument and never names a runtime value. Like
the other static-only sorts, an asset term cannot be a port, a field, a tuple or
array element, a native container argument or a `Type` argument, and it has no
permissions. Instance keys include the asset identity.

Projections derive naturals from the asset, never from the author. A ring term
`A` has `A::Inputs`, the ordered input count; `A::Outputs`, the output count;
and `A::Degree`, the largest output degree with every input weighted one. A
bundle term `B` has `B::Tables`, `B::Publics` and `B::Channels`, its table,
public slot and channel counts. A
closed term yields the constant at once. A generic term of either sort yields a
distinct natural factor that closure substitutes from the captured asset, also
through a renamed parameter: inference never solves a parameter
through a projection, and `pow2` of a projection is unsupported. A degree above
the arena limit is saturated and refuses when it is requested, at definition
checking for a closed term and at closure for a generic one. Projections take
part in ordinary natural arithmetic and bounds: `where 1 <= A::Inputs` is
checked against the closed asset and entailed from a caller's explicit bound
like any other natural requirement. Associated asset members on interfaces are
not supported.

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
Calls must prove permission bounds from the caller's explicit assumptions or the selected
concrete type. Closed permission requirements are evaluated immediately; a true
requirement adds no generic assumption. Group permissions do not imply scalar permissions.
Requirements follow a callable's result type or a nominal declaration's parameter
list; an alias places them before `=`. Symbolic inequalities must match a
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
symbolic requirements must follow from caller bounds and installed
unary implications; arguments match by normalized source identity. A closed
requirement is checked against installed facts, even in an unused declaration,
and never established by an assumption. These are operation availability
requirements, not cryptographic guarantees. Before source checking, the installed
catalog must sustain inherent sort facts and every installed unary implication.
This preserves generic assumptions when type aliases normalize away their bounds.

Defined `fn`, `math fn` and `protocol` declarations without a `where` clause infer
missing open catalog and natural preconditions from signature formation,
specification selectors and body operations, including calls. Inference records
requirements; it does not prove them or invent catalog facts. Every concrete
application still checks them. A written `where` clause is complete: checking
cannot silently add a condition. `where ()` states that the sort and parameter
bounds suffice. Abstract members, relations, types, interfaces and components
retain explicit preconditions. Component implementations may infer member
conditions only when their interface and component contract establish them.

`Copy`, `Drop`, `Share` and `Wire` remain explicit resource permissions. Omitting
them from `T: Type` promises none; `Field` and `Group` retain their inherent Copy
and Drop. An inline bound such as `T: Type + Copy` supplies that permission while
leaving catalog and natural inference enabled when `where` is absent. Inference
does not change move behavior, select participants or insert communication.
The checked declaration API exposes completed result types and requirements;
each inferred bound records its origin span and `inferred` flag.

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
bound for that index, inferred or written under the contract rules above.
Dynamic array indexing is outside this profile.
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

A contract whose parameter is an asset identity takes an asset term of the
accepted sort instead of a literal: `kernel<F>("ring.point", v; A)` or
`; Product`. The parameter declaration's `assetFormat` selects `Ring`
(`zkc.ring/0`) or `Bundle` (`zkc.relation-bundle/0`); the frontend does not infer
the family from the operation name. The term may be a declared asset domain or a generic parameter.
A literal digest, a term of another sort or an asset term at a position that
takes a literal refuses. The compiler writes the closed term's canonical
identity into the emitted parameter when the body closes, retains the asset for
the Entry package, and checks the family's reference rules. Ring substitution
admits the carrier field and its base field; a Bundle table view checks the
table index and exact declared column fields. The Bundle
[polynomial view](../domains/relation-bundles.md#compiler-visible-polynomial-view)
also admits the carrier's base field and requires a height policy that admits
a power of two `n >= 2` whose root of order `n` the carrier installs. The
[interaction view](../domains/relation-bundles.md#compiler-visible-interaction-view)
extends that carrier check to every interaction output; its policy kernel
needs no such height. Source comparison compares the closed body's identities
with the original MLIR, so a changed digest is a correspondence failure.

Generic checking uses completed capability bounds, inherent Field/Group facts and
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

## Checked pointwise maps

```text
math fn affine<F: Field>(low: F, high: F, r: F) -> F {
  return low + (high - low) * r;
}
fn fold<F: Field>(low: Vector<F>, high: Vector<F>, r: F) -> Vector<F> {
  return map affine(each low, each high, r);
}
```

`map helper<...>(arguments...)` applies one static, defined `math fn` at every
row of runtime vectors; `map` and `each` are keywords. `each` marks an argument
read one row at a time, which must be a native `vector` of the helper's field.
Other arguments are scalars shared by every row, and at least one is marked.
After replacing each marked vector by its element type, the arguments match the
helper's parameters exactly. Every parameter and the single result use one scalar
field `F`; the map returns a vector of `F`. Static arguments are inferred or
written as for calls. There are no function values, closures, interface members
or dynamic dispatch, and every argument remains an ordinary operand for use,
capture and effect checking.

`map` occurs only in ordinary local functions; protocols call a local wrapper.
It is checked execution with the [pointwise meaning](../domains/vectors.md#pointwise-maps).
Unequal row counts fail its ordered shape check. Like a vector kernel's own
check, this is a backend failure reported as `rejected:require`, not a native
`reject`, and the caller conservatively infers `stop`. Code that should reject
unequal lengths natively first requires them equal, for example
`require(kernel<F>("vector.length", a) == kernel<F>("vector.length", b))`.

Every operation of the helper and of the helpers it calls, used or not, may be
only a field constant, `+`, `-` or `*` in the map's field. Formation of the
emitted [IR declaration](../ir/protocols.md#checked-pointwise-maps) refuses
anything else with `algebra-map-formula`. The expanded formula must also fit the
[Ring limits](../ir/limits.md), including depth 1,024, where subtraction costs an
extra level on its right operand; a deeper formula refuses with the same
identifier when the original is prepared. Both refusals name the source map and
its helper. Invalid value-argument binding uses `source.call`; invalid static
binding uses `source.generic`, as for ordinary calls. Other map-specific source
refusals use `source.map`; a map outside local code uses `source.mode`.

## Finite vector reductions

```zkc
use zkc::vector as vec;
fn weighted<F: Field>(xs: vec::Vector<F>, ys: vec::Vector<F>, α: F) -> F {
  return reduce vec::sum [(x, y) in zip(xs, ys)] { x * y + α };
}
```

A finite reduction applies a checked pointwise map to the written collections,
then calls the selected reducer on that vector. The single-row form is
`reduce reducer [x in xs] { body }`. Multiple rows require the explicit strict
`zip` form above. [Reduction notation](notation.md#finite-reduction-syntax)
gives the equivalent library-bound `∑` and `∏` spellings.

All collections have the installed dynamic `Vector<F>` type for one field `F`.
The reducer is a statically resolved, defined local callable with exactly one
`Vector<F>` input, one `F` result and no service inputs. Reduction notation
bindings require a written result type, as other callable notation does. Named and
symbolic forms use ordinary callable resolution, static argument inference and
definition-site identity. A custom reducer may stop; it is an ordinary call,
with no inferred sum/product law. Component dispatch and function values are
outside this reducer profile.

Evaluation has this order:

1. Evaluate every collection once, left to right, in the enclosing scope.
   Repeated collection expressions remain separate evaluations. Row bindings
   are not in scope in any collection.
2. Read each captured outer binding once after all collections, in the order
   of its first textual use in the body. Captures are whole immutable scalar
   bindings of field `F`, with the ordinary copy/drop permissions. Projection
   from an aggregate must be assigned to an outer scalar `let` first; mutable
   bindings, services, vectors and other aggregate captures refuse.
3. Check every row length in written order against the first row, including
   `_` and named rows the scalar result does not use. Only then realize the
   scalar formula over the rows and call the reducer. Unequal lengths retain
   the map's backend shape refusal, not truncating zip or native rejection.

Named rows are distinct lexical bindings local to the scalar body; `_` introduces
no name. Rows can shadow outer immutable bindings under the ordinary binding
rules, without changing collection resolution or capturing those outer values.
Shadowing a mutable binding remains forbidden. Body-local immutable lets follow
normal shadowing. Extraction uses resolved binding identities and original
definition scopes; generated
names neither capture source bindings nor become source-callable declarations.

The body returns one scalar of `F`. It admits immutable scalar lets, scalar
aliases, field constants, addition, subtraction and multiplication, and concrete
static mathematical helpers whose entire reachable bodies satisfy the same
field-ring rule. Admission checks every operation, including dead operations;
field-typed results or custom symbols alone do not establish this rule. Deferred
call and notation inference inside the body uses Math mode, with the generated
helper edge included in depth accounting. Local calls, effects, mutation,
services, nonfield values, component dispatch and nested reductions refuse.
The initial binder occurs only in module-level local functions, not directly
in protocols, math functions or component members. Protocols can call a local
wrapper. Existing named `map` retains its later IR formula admission; the binder
adds this earlier source-body check.

For the library sum, matched empty rows return zero; for the library product,
they return one. A custom reducer instead receives the empty mapped vector and
retains its own behavior. Empty selected rows do not bypass other row checks,
collection evaluation or scalar capture snapshots.

Each binder owns a private generated mathematical helper with positional row
inputs followed by captures in their snapshot order. Helpers remain in a
checker-owned pending collection until authored bodies, signatures and Entries
are checked and their live inference references have expired. Finalization
inherits the completed enclosing static parameters and requirements. Generated
helpers have distinct semantic identities, consume declaration/instance/work
limits, and add a call-depth edge even for a constant body. Closure rechecks
the retained limits and does not reparse or resolve the extracted expressions.

A separate extraction witness checker reconstructs row bindings, free captures
and their order from retained authored syntax and resolved identities. It checks
the scalar body, positional inputs, map mask, field, reducer, sites and lexical
selection against the actual checked graph before source-to-IR comparison.
This bounds the extraction check; it is not a proof of parser, resolver, capture
semantics or native runtime adequacy.

## Boolean formulas

`!a`, `a && b` and `a || b` accept Boolean operands. Negation evaluates its
operand once. In a local `fn`, `&&` evaluates its right operand only when the
left is true; `||` does so only when the left is false. They follow the same
typing, effects, capture and resource-join rules as local `if` expressions.
Specifically, `a && b` checks as `if a { b } else { false }`, and `a || b`
as `if a { true } else { b }`. A noncopyable capture used only on the right
therefore needs `Drop` on the skipped path.
Both operands are checked, including a statically skipped operand. A block on
the right may perform ordered work or stop. Its continuing result must be Boolean.

In `math fn`, relations and protocol formulas, these operators denote total
mathematics. Both operands retain their dependencies and formation obligations,
including in `false && x` and `true || x`. Protocol `&&` and `||` operands must
contain only mathematical work, including inside blocks and unused bindings:
local calls, service queries, messages, mutation, rejection and control refuse
with `source.mode`. An empty effect allowance on a local function does not make
it mathematical. Put conditional execution in a local `fn` and call it from
the protocol; this does not introduce a conditional message schedule.

Total Boolean operations use the same mathematical helper path as field and
group expressions. `intrinsic("bool.and", a, b)`, `"bool.or"` and `"bool.xor"`
take two Boolean operands and return one Boolean. They have no static arguments
or literal parameters. Both operands are evaluated; these are mathematical
operations, not conditional execution. Libraries can expose ordinary functions:

```text
math fn both(a: bool, b: bool) -> bool {
  return intrinsic("bool.and", a, b);
}
math fn negate(a: bool) -> bool { return !a; }
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
variables. It is an SSA value in Protocol IR and has no executable value
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
which may be a tuple or unit. A defined helper may omit `-> T`: its body must
determine the result without caller context. Numeric literals and empty arrays
need a type context; a function with no continuing result needs an explicit
result type. Abstract members require result types. Protocols retain named,
typed output ports with explicit participant sets.

Within an expression, type equations connect operands, call parameters and
results, aggregate fields, block tails and all continuing branch results. Type
information flows in both directions: `id(if b { x } else { x })` infers the
same result as binding that conditional before calling `id`. An array's elements
and a conditional's continuing arms constrain one another regardless of order;
`[0, x]` and `[x, 0]` have the same element type when `x` supplies a field context.
Partial aggregate information is retained, so `[(0, x), (x, 0)]` also has a
determined type. Numeric literals restrict their type to a field or local index;
they never select a default domain.

Each authored statement must resolve before the next. A block's preceding
statements have their own scopes of inference; its tail participates in the
enclosing expression. Thus `id({ x })` can use the call's expected type, but a
later use cannot resolve `let x = 0;`. Inference does not execute expressions,
consume resources or choose participants. Resource checks and evaluation remain
in source order; participant inference follows its
[own statement constraints](protocols.md#participant-meaning).

### Arguments and inference

User-declared helper and protocol parameters accept positional arguments followed
by named arguments. A named argument is `parameter = expression`; its name belongs
to the resolved declaration. For example, `pair(right = n, left = flag)` binds
the same parameters as `pair(flag, n)`, while evaluating `n` before `flag`.
Every value or managed-service parameter must be supplied exactly once. Unknown
names, duplicate bindings, missing/excess arguments and a positional argument
after a named argument refuse with `source.call`. Runtime arguments have no
defaults. Interface calls use the interface's parameter names; concrete component
calls use the implementation's names. Renaming a public parameter changes this
source contract even though parameter names do not affect type conformance.

Argument expressions evaluate once, left to right in written order. Expected
types, participant demands and service requirements follow the named destination;
only evaluated operands are arranged in declaration order. The same rule applies
to maps: `map affine(r = r, high = each ys, low = each xs)` associates `each`
with its named parameter. Record fields already use their declared names. Variant
payloads, associated representation constructors and fixed intrinsic,
kernel and service-method interfaces retain positional arguments.

Helper and protocol calls infer bare static parameters from data argument types,
managed-service fields and expected helper results. Static arguments also accept
names: `pair<B = index>(flag, n)` fixes `B` and infers other parameters. Omit
the whole list, supply a positional prefix, select parameters by name, or use `_`
for a whole slot, as in `choose<_, Impl>(value)`. Positional arguments must precede
named ones. Explicit slots constrain inference. Every missing slot or hole must
have one consistent solution; there are no default types, dimensions or component
implementations. Holes are whole call slots, not nested type syntax or kernel,
intrinsic, constructor or Entry arguments. There is no global instance search,
runtime component dispatch or inference through noninjective associations.
Each call has fresh inference variables; the enclosing definition's parameters
remain fixed. Associated types and compound natural expressions normalize
forward after their inputs are known, without inferring those inputs from a
result. Group scaling is written `point * scalar`; it does not infer a group
from its scalar field.

Types, constructors, relation applications and Entries accept named static
arguments with complete coverage, such as `Box<T = Fr>` or
`run Demo = Run<N = 8, F = Fr>;`. These contexts do not infer missing arguments
or accept holes. Invalid static name binding uses `source.generic`. A bound
component already supplies its inherited parameters; a member call cannot
override them. Associated types inherit their component's arguments and accept
no separate static list. Fixed primitive static interfaces remain positional.

### Library-defined operators

Operators, paired-delimiter notation and reduction bindings resolve to ordinary
callable signatures.
The [notation contract](notation.md) defines declarations, fixity, exact binding
powers, delimiter holes and scope. A target must be mathematical or local, have
one written result type and exactly the descriptor's number of data inputs:
two for infix, one for prefix/postfix, and one per delimiter hole. Only reserved
`==` requires a Boolean result. Protocols and implicit services are not targets.
Public bindings require public targets. Unused bindings are checked too.
Reduction descriptors have one mapped-vector operand and the additional
[finite reduction target rules](#finite-vector-reductions).

A block can begin with `operator + = A::add;`, where `A` is an explicit component
parameter, or with other callable bindings. Targets accept partial static
arguments, names and holes, such as `operator * = scale<F = F>;`. The nearest
block declaring a descriptor replaces its entire inherited callable family;
there is no fallback based on operand types. Target names resolve at the binding's
definition site. Component dictionaries are explicit, with no instance search.

Named, operator and delimited calls share signature constraints. Candidates are
filtered by descriptor arity before input-coherence checking. Each statement is
solved as one problem, including expected results, literals and nested calls. Existing
`let` boundaries remain: a later statement cannot resolve an earlier one.
Structural contexts such as `match` propagate constraints from uniquely viable
signatures before reading their scrutinee type. They still require a known
scrutinee before checking arms; they do not finalize call identities early.
Results may determine operand types or static arguments, but cannot select between
distinct bindings that accept the same fixed operand types. An unresolved,
consistent alternative prevents unique resolution. Capabilities, natural bounds,
effects, body modes, participants and backend availability never break ties.
Candidate equations are isolated and all explored work counts toward the invocation
limit. Incomplete inference uses `source.inference`; missing or ambiguous operator
meanings use `source.operator`; exhausted search uses `source.limit`.

Only the selected target proceeds through ordinary body, cycle, permission,
requirement, effect and participant checks. Every operand evaluates once in written
order. Collecting constraints evaluates no operand and introduces no synthetic
`let` boundary. Definition checking retains the chosen target, statics, component,
source binding and canonical visible family. A separate structural checker re-enumerates
the descriptor-specific lexical family from the checked scope, validates descriptor
identity, arity and binding origin, checks input coherence and the complete authored
operand-order vector `[0, ..., arity - 1]`, compares the inferred result, and
validates the emitted native action without invoking the overload solver or its
candidate enumerator. Inconsistent evidence refuses with `source.binding-witness`. Specialization substitutes static arguments and retains
the definition's target/family identities; it never resolves notation in a caller's
scope. This executable check is not a formal proof of elaboration correctness.

### Primitive function definitions

A function can name an installed operation as its complete body:

```text
pub math fn add<F: Field>(a: F, b: F) -> F = primitive("field.add");
pub operator + = add;
```

`primitive` validates a registered signature, body mode, effects and mathematical
input dependencies. It introduces no foreign semantics or unverified effect
annotation. Static roots are recovered from written ports by structural matching
and forward association. Extra or reordered source parameters do not change native
root order. Schemes requiring literal attributes or roots that cannot be recovered
from ports use an ordinary `kernel`/`intrinsic` body. A primitive requires one
written result; a tuple can represent multiple native results. Invalid declarations
use `source.primitive` or the more specific installed-contract diagnostic.

The installed scalar prelude provides field addition/subtraction/multiplication/
equality, group addition/scaling/equality, Boolean equality, and ordered index
addition/subtraction/multiplication/equality. Group scaling is `point * scalar`.
Total scalar calls emit mathematical or local primitive operations directly.
Index arithmetic retains possible failure; index equality is total. Ordered
vector operations retain shape checks and stop behavior. Calls to ordered
primitives in protocols keep the participant-owned helper boundary. Formal
intrinsics called from local code retain the existing realization boundary.
Retained helper calls, including mapped primitives, count toward the call-depth
limit; directly emitted primitive operations add no helper edge.
The prelude is excluded from capture file/byte limits, but its parsing and
checking count toward token, declaration and work limits for the invocation.
`!`, `&&` and `||` keep their fixed Boolean control/formula semantics and are not
redefined by library equality bindings.

### Components and body modes

An interface declares associated types/domains and math/local member signatures.
A component selects one interface and defines every member exactly once. Associated
runtime types default to no permissions; their promised permissions must be supported
by their representation. Associated `Field` and `Group` declarations expose their
selected domain. Conformance checks callable modes, types, permissions, natural
preconditions and effect allowances. An implementation cannot require more than
its interface allows. Interfaces and components may have static parameters;
abstract signatures may declare member-specific generic parameters.
`Component::method<F, ...>(value)` supplies the component parameters directly;
`C::method(value)` through a bound component uses the parameters already in `C`.
Records and variants are module declarations. An abstract call or type projection
requires a bound component; a free interface name cannot select an implementation.

Defined local functions infer `stop` and `opaque` effects from their bodies.
An optional `!{stop, opaque}` is an upper bound, and `!{}` forbids both. Abstract
local signatures default to allowing both; math signatures allow neither. An empty
effect allowance never turns ordered code into a total mathematical function.
Opaque runtime intrinsics are not exposed by this profile.

Bodies use lexical `let` and `let mut` bindings, whole-name assignment, nested
block expressions and a final `return`. [Body semantics](protocols.md#bindings-and-local-control)
define scopes, patterns and resource joins. Arithmetic retains the fixed
`*`, `+`, `-` and `==` descriptors and field/group contracts; imported notation
adds callable spellings under the [binding-power rules](notation.md#expression-association).
Chained equality requires parentheses. No implicit field conversion occurs. Field literals need a unique
expected field from an annotation, operand, call or result. Installed contracts
check canonical spelling and characteristic bounds without modular reduction.
For an abstract field, only the universally valid literals `0` and `1` are admitted.
Boolean literals need no domain. Record construction supplies every field exactly
once. Variant construction uses `Choice::Some<Fr>(x)` in local code.

## Bounds and scope

Requests can lower these ceilings, never raise them. Checks refuse before charged
work or recursive-depth budgets are exceeded; no truncated result is returned.
Capture lexing, parsing and definition checking share one work budget.
Specialization, layouts, emission, comparison, predicate admission and interface
serialization each have a separate work budget. The capture-wide specification
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
| Charged work per phase | 4,000,000 |
| Emitted MLIR; interface JSON | 16 MiB; 4 MiB |
| Encoded symbol; diagnostic path bytes | 4096 each |
| Active notation descriptor keys per environment; delimiter holes | 4096; 64 |
| Notation inspection JSON | 8 MiB |
| Location records, five 64-bit coordinates each | 16 MiB |

The work ceiling accommodates composed source libraries while preserving charges
for each traversal. File, type, instance, operation and output ceilings remain
independent; a higher work allowance does not admit a larger type or deeper call.

Parse depth bounds both recursive parsing and constructed type/natural syntax
trees, including operator chains. [Notation limits](notation.md#bounds) also
count fixed Boolean descriptors, retain environment/hole maxima and recheck
lowered limits before reuse of a checked project.

The comparator performs whole-module admission once before comparing SSA. Target
admission, expansion and execution retain their own limits. A checked source may
fail target preparation or realization with the failure phase identified.

Receive-only setup slots, per-receive setup pins, general private ingress validators,
dynamic source arrays and member-generic conformance remain outside the implemented
profile. Reserved future syntax
refuses explicitly. Existing IR support remains independent. Structural source
comparison and runtime controls establish neither native Lean correspondence nor
protocol security.

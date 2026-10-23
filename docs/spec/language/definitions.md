# Source definitions and types

This native contract defines captured modules, declarations, types and source bodies.

## Capture and names

A capture is a nonempty map from logical module paths to exact UTF-8 bytes.
Each file starts with `module path;` matching its captured name. Module paths
use `::`; every segment follows the [Unicode 17 identifier profile](lexical.md).
Names retain exact NFC UTF-8 bytes, with no silent normalization. The lexical
contract also defines contextual keywords, ASCII strings, UTF-8 comments and
mathematical tokens. Tokens retain trivia and original UTF-8 byte spans.

A file body and an inline `module Name { ... }` are the same static module
construct. Modules may contain declarations, imports, notation and nested modules.
A header may have static parameters, an interface and requirements:
`module Name<N: nat>: Contract<N> where 1 <= N { ... }`. The file form uses a
semicolon instead of braces and consumes the remainder of the captured file.

`module Child;` links the separately captured `parent::Child` file to its parent;
`pub module Child;` also exposes that child. The child file declares its complete
logical path and its own parameters/interface. It inherits its parent's names,
static parameters and requirements, exactly as an inline body does. The manifest
must capture both files. A captured descendant of another captured module must
have this explicit link; missing children, duplicate inline/file bodies and
unlinked descendants refuse. No files are discovered and no bodies are merged.
A path prefix without its own captured declaration is only a namespace prefix.

File roots are public. Other declarations are private unless prefixed with `pub`.
Private names and representation authority are available in their owning module
and descendants; parents and siblings gain no access from sharing a file. A
public qualified path requires each traversed module/member to be accessible.
Interface members and the corresponding authored implementation members are
public through their owner. Additional implementation helpers remain private
unless marked `pub`.

Imports and direct declarations share one binding table per module. Duplicate
names refuse; child declarations may use names present in ancestor scopes. Static
parameters and runtime bindings cannot shadow visible declarations or module
aliases. [Body binding rules](protocols.md#bindings-and-local-control) define local
scope. Import, type and call dependencies must be acyclic. Every declaration is
checked, including unused generic bodies. Modules have no runtime value or object.

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

The CLI accepts a TOML manifest with `format = "zkc.project/0"`, an optional
`modules` table mapping logical names to paths, an optional `dependencies` table
mapping local labels to library directories or workspace selections, and an optional `assets` table
mapping names to tables with exactly `format` and `path`. Unknown or duplicate
keys and unsupported types refuse. A manifest is a bounded regular file (at most
1 MiB). Each dependency directory supplies its own `zkc.toml`, interpreted
relative to that manifest's visible parent. Dependency labels do not rename
modules. The closure must contain at least one module. An individual manifest
must contain modules or dependencies. At most 64 manifest contexts and 32 active
levels are admitted; the entire closure has at most 256 module and asset bindings.
A context is the canonical parent directory plus the visible manifest filename,
so directory aliases share a context and symlinked manifest files retain their
relative-path meaning. Shared dependencies are expanded once; active cycles
refuse with `source-project-cycle`. A repeated logical module or asset name must
refer to the same filesystem path (allowing symlink aliases), with the same asset
format. Other collisions refuse with `source-project-conflict`; neither traversal
order nor dependency labels select a winner. Distinct files with equal bytes are
still distinct providers. The resulting maps are sorted by name before capture.
All participating manifests and mapped files are protected compilation inputs.
No registry lookup, implicit module discovery or version selection occurs. Each supplied path
is nonempty, contains no NUL, and is at most 4096 bytes.

Optional root `[build]` and `[profile.NAME]` tables contain partial Boolean
implementation settings: `simplify`, `finite-bulk`, `release-storage`,
`fuse-vector-reductions`, `fuse-collect-fold` and `calculation-batching`.
Resolution is shipped defaults, root build, selected profile, then explicit
request overrides. Omission preserves the preceding value; explicit `false`
overrides it. At most 256 named profiles are admitted, with nonempty names of at
most 128 bytes. `default` is reserved for the root build without a named profile.
Unknown profiles and fields refuse. Dependency settings are validated but never
applied to a consumer. Settings select checked implementations and never disable
required source, mathematical or physical verification. Effective values and
origins are diagnostic metadata; the package retains its published policy.

Optional root `[test.NAME]` tables describe consumer invocations, with required
`entry`, optional `operation` (`check`, `run`, `prove` or `verify`; default
`check`), string-array `args`, and `expect` (`success` or an exact refusal code;
default `success`). At most 256 tests are admitted, with nonempty names of at most
128 bytes. An Entry name is at most 4096 bytes; there are at most 64 arguments of
4096 bytes each and an expectation is nonempty and at most 128 bytes. Recipes
cannot replace source roots, the compiler, pinned packages, profiles, reports or
compilation caches. File arguments resolve beside the root manifest. Dependency
recipes are validated but never run implicitly. Tests use ordinary checking and
Host execution. See [tooling](../../compiler/tooling.md) for defaults and usage.

A manifest may declare `[workspace]` with exactly one string `path`. A dependency
may then be a table with exactly one nonempty string `workspace`, naming a
package in that explicitly selected catalog. String dependencies retain their
directory meaning. Mixed forms and unknown keys refuse. The workspace path is
relative to the declaring manifest's visible parent; dependencies do not inherit
another manifest's workspace. There is no ancestor catalog search.

A catalog is a regular TOML file with exactly `format = "zkc.workspace/0"` and
`packages`, a table mapping nonempty package names to location strings. The
whole syntax and every name and location are validated, including unselected
entries. A selected location resolves against the catalog's visible parent and
names a directory containing `zkc.toml` or an explicit manifest file. File
symlinks preserve visible parent semantics. Only selected files are opened;
declaring an unused workspace validates its table but does not open its catalog.
Catalog keys and dependency labels never rename source modules.

At most 16 used catalog contexts, 256 entries per catalog and 1 MiB per catalog
are admitted, independently of the project closure limits. Every used catalog
joins the protected input set. The same cycle, provider and asset checks apply
to path and catalog edges. Catalog formatting, paths and selection provenance
are metadata and do not enter capture or artifact identity. Invalid schema or a
missing selection refuses with `source-project-format`; unreadable selected
files with `source-project-io`; exceeded ceilings with `source-project-limit`.

`--project=FILE` selects an explicit manifest. Otherwise explicit `--module` or
`--asset` inputs disable discovery; they cannot be combined with `--project`.
With neither option the CLI uses the nearest `zkc.toml` in the current directory
or its ancestors. The first filesystem entry is final: malformed, unreadable,
nonregular and dangling-symlink candidates fail rather than fall back to a parent.
Relative mapped paths resolve against the selected manifest's visible parent,
including symlinked manifests. Explicit command-line paths use the invocation
directory. Absolute paths, `..` and ordinary symlink resolution are supported;
imports do not scan directories. SDK captures never discover a manifest.

Manifest paths, formatting, profiles and test recipes do not enter source
capture identity. Identical named source/asset bytes have the same capture;
effective build settings separately determine the published implementation policy.
Execution inputs and secrets remain outside source capture.
The CLI protects the manifest, mapped inputs and selected compiler from output
publication, including file aliases. See [Entry selection](entries.md#selection)
for canonical names and check scopes, and the [project guide](../../language/README.md#project-inputs)
for default output paths.

Qualified references first resolve their root in the nearest lexical scope,
then each enclosing module, including imports. A resolved lexical
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
`indexing []` selects all exported indexing arities.
Import aliases have whole-module scope and may refer to aliases written later.
The names introduced by an import are excluded from its own source path; for
example, `use library::sub as library;` resolves the enclosing or captured
`library` before introducing the alias.
A leading `::` starts import lookup at captured roots. Alias dependency cycles and
depth limits are checked independently of authored order. Name bindings are
resolved first; a separate pass validates the completed module dependency graph
and propagates notation exports. Visibility checks authorize the resolved routes.
A qualified reference alone activates no notation.
`pub use` reexports the selected names, aliases and bindings with their original identities; ordinary
imports remain private. A reexport requires the selected declaration itself to be
public. It may expose a public item through an accessible private ancestor without
changing the item's identity or making that ancestor public. Duplicate imports of the same identity are harmless.
Conflicting names/aliases, missing exports and import cycles refuse. Captured
module ordering and import ordering do not choose overloads. Exported bindings
carry their resolved descriptors, including those introduced privately; their
targets must still be public. [Notation scope](notation.md#imports-and-lexical-scope)
defines descriptor conflicts, whole-module visibility and local replacement.

The `zkc` root is reserved. The `zkc::prelude` module belongs to the compiler installation. Its exact
source is embedded and included in installation identity. Captures cannot supply
either name or claim an installation origin. Installed sources cannot be linked
as external children. Its public scalar operator bindings
are visible by default; its function names require qualification or explicit
import. The prelude itself has no imports or inherited operator environment.
There is no runtime source-file lookup. Capture identity and captured file/byte
limits exclude the prelude; token, declaration, operation and work limits include
its checking. `Analysis::sources()` and `CheckedProject::sources()` include both
origins and index all diagnostic spans. `capture().sources()` includes only
captured inputs.

## Definition checking and Entry closure

Analysis first collects fixed declaration headers and body token ranges, resolves
module/import bindings, authorizes visibility and orders notation dependencies,
then parses bodies under immutable notation environments.
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

Entries must belong to a closed module scope; they cannot retain inherited static
parameters. A client module selects a generic protocol with concrete arguments.

An instance key contains the qualified declaration name, canonical static
arguments and selected scoped helper identities, with each component length
framed. Scoped helper identities retain their lexical body and module
substitution. Runtime capture values and caller participants are operands, not
instance-key components. A declaration fixes its body mode.
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

`zkc inspect --view=placement` reports a diagnostic array of public modules, interfaces,
completed callable contracts and constructions from captured modules, sorted by qualified name, under `checked.declarations`.
Module/interface records report directly declared public member names and any
implemented contract. The inventory uses canonical declaration paths with public
owners; it does not enumerate import alias or reexport routes.
Installation declarations remain accessible through the checked SDK graph. Callable members
are visible through their public owner. Members identify that owner and mark
inherited static parameters; `abstract` distinguishes interface declarations
from definitions with bodies. Each item reports its kind, static
parameters and permissions, role roster, data/service argument order, typed
ports, services, requirements, body effects (or abstract allowance), and captured
module byte span and source `origin`. `definition` is `body`, `abstract` or
`primitive`; primitive definitions also report the installed `primitive` identity.
Natural/capability bounds retain their inferred flags; explicit
effect allowances remain separate; abstract Local declarations always include
their explicit allowance. Effect objects report fixed `stop` and `opaque` flags
and a `dependencies` array whose entries identify zero-based `callback` slots
and their label-specific `stop` and `opaque` bounds. Fixed callback acceptance
ceilings remain separate in each `scoped_inputs` item. Type and natural
strings are descriptive mathematical spellings,
not a serialization accepted by the checker. The view never supplies linking
or admission authority. Its unembedded JSON array is bounded by `interfaceBytes`;
an exceeded bound refuses without publishing a partial result.

`zkc inspect --view=api` reports a diagnostic `checked.api` object with format `zkc.source-api/0`.
Its `roots` are the captured root modules. Its `exports` form a compact graph:
each edge records the canonical `owner`, exported `name`, canonical `target`,
whether it is `imported`, and its source location. Following an alias does not
allocate another declaration or enumerate every possible path. `notations`
records exported syntax bindings per reachable owner, with descriptor key,
symbol, canonical target, static arguments and binding source. The separate
notation view retains detailed syntax environments and occurrences.

`declarations` describes all declarations reachable through these public routes,
including types, domains, associated types, relations and Entries. Callable
contracts use the same descriptive fields as the declaration inventory.
Capability requirements additionally provide `export`, a canonical qualified
source name for writing the predicate in a `where` clause.
`requirements_written` and `effects_written` distinguish authored contracts
from completion by the checker. Record and variant descriptions expose public
fields and constructor visibility, but omit private field names and types.
Associated types report permissions and abstract status without their private
representation. Canonical names may pass through private ancestors when a
public reexport provides access; inspection grants no additional source access.

`references` records checked references from captured source, including private
helpers and unused imports. Each record has the source `owner`, `written` path,
the `provider` source module selected by that path, its `provider_origin`
(`captured` or `installation`), canonical `target`, its
`target_module`, and source location. A facade provider remains distinct from
its implementation target. Calls through a static module parameter additionally
identify the `abstract_module` and its interface member. Locations use logical
source module, origin, and UTF-8 byte offsets. The provider of an abstract call
is the route used to bind its interface, including for inherited parameters;
reexporting an interface does not impose its implementation package on callers.
Tables are sorted by canonical
names and source spans; repeated equivalent references are coalesced.

The API view is bounded by `apiInspectionBytes` (8 MiB by default), checked
work/declaration/operation limits and public graph depth. Limit exhaustion
refuses with `source.limit` and publishes no partial successful report. The
combined successful check report is bounded by 32 MiB. Inspection is diagnostic
metadata: it changes no capture, installation, original or program identity,
and does not supply linking, admission or security authority.

The direct compiler and CLI emit the same flat `zkc.source-check/0` successful
result. It records `status`, `phase`, `scope`, `capture`, `installation`, optional
`declarations`, `api`, `notations`, and `entry`/`original` for Entry scope. The CLI adds `compiler`.
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
fields/groups, native data containers, nominal records/variants and associated module types. `(T,)`
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
associated fields/groups are identical to their directly declared types. A module
may expose an associated domain (`type C: Commitment`); this adds no runtime value
or constructor. Static-only domains have no runtime usage or boundary admission.
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
`where Copy(C::Item)` can constrain an abstract associated projection.
Calls must prove permission bounds from the caller's checked contract or the
selected concrete type. Closed permission requirements are evaluated immediately; a true
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

Defined `fn`, `math fn`, `domain fn`, `protocol` and `construction` declarations
without a `where` clause infer missing usage, open catalog and natural
preconditions from signature formation,
specification selectors and body operations, including calls. Inference records
requirements; it does not prove them or invent catalog facts. Every concrete
application still checks them. A written `where` clause is complete: checking
cannot silently add a condition. `where ()` states that the sort and parameter
bounds suffice. Abstract members, relations, types, interfaces and modules
retain explicit preconditions. Module implementations may infer member
conditions only when their interface and module contract establish them.

A bare `T: Type` promises no usage property. A defined body infers `Copy(T)`
when it reuses a value and `Drop(T)` when a continuing path leaves one unused.
Identity forwarding needs neither. `Copy` implies `Drop`; `Field` and `Group`
supply both. An inline bound such as `T: Type + Copy` remains an explicit promise.
A written `where` clause closes usage inference as well as catalog and natural
inference. Abstract members expose only their written contracts.

```zkc
fn identity<T: Type>(x: T) -> T { return x; }
fn duplicate<T: Type>(x: T) -> (T, T) { return (x, x); } // infers Copy(T)
fn ignore<T: Type>(x: T) -> () { return (); } // infers Drop(T)
```

The compiler collects authored uses and continuing paths, freezes the resulting
contract, then elaborates moves under that contract. Captures transfer into a
control region; mutable state crosses a join as a whole. Inference follows these
transfer rules, including stopped branches and partial moves. Explicit resource
restrictions and native policies cannot be strengthened by inference. Collection
and elaboration share bounded compiler work; exceeding that budget refuses.
The checked declaration exposes inferred bounds with their origin and `inferred`
flag. Boundary obligations are separate, typed conditions with the originating
site and intervening call sites; an explicit `where ()` does not disable them.

Bounds apply to generic type and module applications as well as calls. Parent
bounds are inherited. Associated type declarations cannot introduce their own
capability requirements; inherited module bounds still apply. A module member
cannot add requirements beyond those
provided by its module and interface member; interface bounds are substituted
through the implementation's parameters and associated types. Type applications
inside a clause use its complete set of bounds, independent of written order.
Specialization discharges and removes bounds. They introduce no runtime values,
instance-key fields or equality assumptions. Checking is bounded by the source
work budget and the finite requirement checker's term and assumption limits.

Fixed arrays have bounded closed lengths after selection. `[a, b]` constructs an
array; `a[0]` uses a numeric static index. A symbolic length needs a corresponding
bound for that index, inferred or written under the contract rules above.
Dynamic array indexing is outside this profile.
Runtime loops can use a closed natural as an index value. Index literals and
`index<N>()` are also available in Math and protocol expressions; they denote
unsigned 64-bit values. `intrinsic("index.equal", a, b)` and
`intrinsic("index.less", a, b)` are total mathematical comparisons. The prelude's
index equality uses that mathematical identity and keeps its direct native
operation in Local code. Index addition, subtraction and multiplication retain
their checked Local semantics. Indices are not field elements.

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
`indices`, `bytes`, `polynomial`, `table`, `point`, `round`, `sequence`, `field_array`,
`commitment`, `commitments`, `proof`, `prover_key`, `verifier_key`, `opening_state`
and `opening_states`, as well as scalar `field`, `group`, `bool` and `index`. Runtime collections remain
one native value; fixed source arrays retain their structural layout. Runtime
polynomial data does not denote a formal polynomial expression. The native type
policy owns mathematical and shared-data eligibility. Copy and Drop alone do not
admit runtime polynomial data into `math fn`, including through an aggregate or
a generic helper instantiated for ordered execution.

A `sequence` element must be executable source data with `Copy` and `Drop`.
These bounds are checked at generic definition checking as well as closure.
Its carrier is `sequence<Pack(T)>`. `Pack(T)` retains an existing single native
carrier for scalars, containers and source variants. A source record, tuple,
array, unit or concrete associated product uses a canonical single-alternative
native variant. Its nominal identity is `["zkc.language.pack",
encodeNominalIdentity(typeIdentity(T))]`, and its sole alternative has native
label `case00000000` and the ordinary flattened leaves in declaration/index order.
Empty products have an empty payload. Full source identity distinguishes nominal
records and their static instantiations; normalized export aliases agree.
Native descriptor depth, payload and byte bounds still apply.

This is contextual packing: ordinary source ports, calls, projections and
returns keep their flattened ABI. No native generic fixed-array type is implied.
The four installed `sequence.empty`, `sequence.append`, `sequence.length` and
`sequence.at` kernel/primitive contracts accept these logical element types and
bind the exact concrete `Pack(T)` identity. Append packs its element; lookup
unpacks to the ordinary ABI. Other native Type roots retain their existing
admission rules. Local packing uses variant injection and a single-arm match
whose yield preserves every payload position. Mathematical adapters use
`data.make` and ordered `data.get` projections. Independent source comparison
checks the actual operations, fields, binding identities and result mappings.

Packing conveys no field access or constructor authority. Sequence usage follows
its element type. Packing a private representation does not grant external
construction authority; explicit resource restrictions remain in force.
Affine/non-Drop values, formal data and managed services cannot be elements.
Existing source variant construction and match semantics are unchanged.
Managed services are separate from these data types. Container permissions retain
element permissions, and concrete external boundaries require native message
admission. A symbolic message shape still needs an admitted codec at closure.
Commitments and proofs may be messages when concrete native admission permits.
Keys and opening state remain local, copyable private data; they do not gain
participant-family or external construction admission. Commitment collections
retain the native collection policy, which does not currently admit them as
protocol messages. Admitting a constructor does
not admit every domain instance. External key/state inputs still require an
explicit ingress contract; this constructor support supplies none.

`kernel<...>("contract", operands...; "parameter", ...)` calls an installed
source/construction contract from an ordinary local function. The semicolon and
parameters are optional. Static arguments explicitly select the contract's root
terms in declaration order; their kinds come from the catalog. Projections and
input/output types follow that signature. Multiple native results form a source
tuple, and no results form unit. Constant parameters use the contract's own
validation, including field-literal bounds. A generic field admits only `0` and
`1` as literals; concrete field parameters are checked against that field,
including a binary field's bit-pattern literals.

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

## Finite reduction binders

```zkc
use zkc::vector as vec;
use zkc::finite_domain::{zip};
use zkc::finite::{sum};
fn weighted<F: Field>(xs: vec::Vector<F>, ys: vec::Vector<F>, α: F) -> F {
  return ∑ (x, y) in zip(xs, ys), (x * y + α);
}
```

A binder is an ordinary statically selected finite consumer call. The example
has the same computation as `sum(zip(xs, ys), fn((x, y)) => x * y + α)`.
The [notation contract](notation.md#finite-reduction-syntax) fixes its parsing,
selection and optional predicate. Names, tuple patterns, `_`, lexical captures,
module dispatch and nested computations use the ordinary scoped-function
machinery. There is no separate ring-body checker or generated-map subsystem.
Binders work directly in protocols, local functions and module members;
mathematical functions use a binding to a total mathematical consumer.

The first argument is a [finite domain](#finite-domains), including ordinary
collection conversion. A pair of independent groups, `(x ∈ xs) (y ∈ ys)`,
constructs a lexicographic product. Use explicit `zip(xs, ys)` for strict
pairwise traversal and nested binders for dependent domains. Independent groups
do not put earlier names in scope in later domains. An outer value whose name
matches an earlier binder cannot be read from a later domain: rename the outer
value or write nested binders to make the intended dependency clear.

Evaluation follows the selected ordinary call:

1. Evaluate domain data once in written order, in the enclosing scope.
2. Snapshot predicate and body captures in argument order and first-use order
   within each callback. Captures follow the shared free-place and permission
   rules, including immutable aggregate projections.
3. Admit every domain constructor, including ignored strict-zip inputs, before
   entering callbacks. Visit items in the domain's order. Evaluate the predicate
   first; false skips that item's body. Nested domains are admitted when reached.

The target's mode and callback contracts determine whether a body can stop or
perform local work. No effects or expected result choose another binding. Total
consumers require established domain formation and access conditions. Local
consumers retain checked failure behavior. Empty sums and products use the
library's zero and one identities; a custom consumer keeps its own semantics.
An arbitrary `Vector<F> -> F` reducer uses `vector::reduce(rows, term, reducer)`,
which collects first and calls the reducer exactly once, including on empty input.
It is not implicitly interpreted as an associative combiner.

Retained evidence uses the shared scoped extraction, domain and call witnesses.
They compare lexical captures, callback arguments, structural product recipes,
definition-site target selection and actual checked operations before closure
and source-to-IR comparison. Limits count generated scoped work. The parser's
construction of the lambda patterns and product syntax, lexical resolution and
inference remain trusted frontend steps; these checks are not a proof of source
elaboration or native execution correctness.

## Group identity

In a `math fn`, `intrinsic<G>("curve.identity")` is the total identity of `G`.
It takes exactly one static group argument, no value arguments and no attributes,
and requires `zkc::curve::ScalarAction(G)`. A generic `Group` sort alone does not
discharge this capability. A mathematical primitive declaration can infer its
static group from its result: `math fn zero<G: Group>() -> G where
zkc::curve::ScalarAction(G) = primitive("curve.identity");`.
Calling that helper from ordinary `fn` code realizes the same nullary native
operation with its usual possible resource exhaustion. The shared
`zkc::curve::identity<G>()` wrapper uses this primitive declaration.

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

`formal("quotient",Q,N)` separately denotes a negacyclic quotient-ring element,
with static naturals `2 <= Q` and `1 <= N`. Its projection, arithmetic and
canonical coefficient observation are specified in
[quotient rings](../domains/quotient-rings.md#formal-calculations). The same
formal-value boundary rules below apply; it does not inherit field-polynomial
laws or an executable representation.

A formal polynomial denotes an expression over a field and an ordered list of
variables. It is an SSA value in Protocol IR and has no executable value
encoding. Its type carries the field and natural arity. It has Copy and Drop
and cannot cross participant or external boundaries. Mathematical helper ports,
products, fixed arrays and ordinary record fields can contain formal values. A zero-length array retains
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

Ordinary records, variants, products and arrays derive reuse and abandonment
from their fields. Reusing data does not authorize duplicating or reordering the
effect that produced it. Effects and resource custody retain their own checks.
`Copy` implies `Drop`. Explicit restrictions use attributes:

```zkc
#[affine] struct Ticket { value: bool }
#[linear] struct Claim {}
#[sealed] struct Snapshot { pub value: bool }
```

`#[affine]` forbids copying and permits abandonment only if every field permits
it. `#[linear]` forbids copying and requires transfer or consumption on every
successful path. Both seal construction and representation access to the defining
module. `#[sealed]` supplies that access boundary without restricting ordinary
usage. Restrictions cannot grant properties missing from a field, and written
usage bounds cannot contradict them. These attributes also apply to opaque
runtime type definitions. Associated domains
such as `type F: Field` and `type C: Commitment` cannot carry them: selecting a
domain does not introduce a nominal runtime wrapper.

Private fields, sealed declarations and opaque associated types do not grant
external constructor authority. Concrete associated types derive usage from their
representation; abstract types expose only their declared promises. `Field` and
`Group` parameters promise `Copy` and `Drop`. Target representation, custody and
codec checks remain independent.

Fields are private unless marked `pub`. A restricted nominal constructor and its
representation are available in its defining module and descendants. Private associated
representations are sealed behind module members. `unpack(value)` requires
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

Boundary checks derive three independent facts from source structure and the
installed native type declarations:

- Participant families require reusable component data; restricted resources and
  participant-local native material cannot have multiple components.
- External construction requires transparent source authority. Private fields,
  sealed types and opaque associated types refuse. This also applies to empty
  arrays whose element type is private or restricted.
- Message transport requires an installed codec for the concrete native type.
  Public construction authority alone does not supply one.

Boundary admission is derived rather than expressed as a generic usage bound.
An open generic message retains its constructor and codec obligations. Generic calls substitute and propagate
these conditions; concrete application and Entry closure must discharge them.
Known invalid types fail immediately, including in unused definitions. Repeated
conditions are stored once, retaining a representative message or placement
origin and call chain for diagnostics. No condition selects a
codec, inserts communication or supplies a private constructor.

Entry inputs undergo these checks after generic selection. Internal protocol
applications transfer existing values without introducing an ingress boundary.
To receive data for a sealed type, accept transparent data and call its module's
validation function explicitly. A public native representation does not grant
source construction authority.

## Callables and static modules

```text
math fn square<F: Field>(x: F) -> F { return x * x; }
interface Increment<F: Field> {
  math fn apply(x: F) -> F;
}
module PlusOne<F: Field>: Increment<F> {
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
defaults. Interface calls use the interface's parameter names; concrete module
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
have one consistent solution; there are no default types, dimensions or module
implementations. Holes are whole call slots, not nested type syntax or kernel,
intrinsic, constructor or Entry arguments. There is no global instance search,
runtime module dispatch or inference through noninjective associations.
Each call has fresh inference variables; the enclosing definition's parameters
remain fixed. Associated types and compound natural expressions normalize
forward after their inputs are known, without inferring those inputs from a
result. Group scaling is written `point * scalar`; it does not infer a group
from its scalar field.

Types, constructors, relation applications and Entries accept named static
arguments with complete coverage, such as `Box<T = Fr>` or
`Run<N = 8, F = Fr>::Inputs`. These contexts do not infer missing arguments
or accept holes. Invalid static name binding uses `source.generic`. A bound
module already supplies its inherited parameters; a member call cannot
override them. Associated types inherit their module's arguments. A direct
reference `Store::State<F, N>` supplies those arguments; a bound `S::State` uses
its module term. Within the same generic scope, omitted inherited arguments
reuse identical enclosing binders in type references and calls. Written arguments
and inference holes retain their usual meaning. Fixed primitive static interfaces
remain positional.

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
[finite reduction target rules](#finite-reduction-binders).

A block can begin with `operator + = A::add;`, where `A` is an explicit module
parameter, or with other callable bindings. Targets accept partial static
arguments, names and holes, such as `operator * = scale<F = F>;`. The nearest
block declaring a descriptor replaces its entire inherited callable family;
there is no fallback based on operand types. Target names resolve at the binding's
definition site. Module dictionaries are explicit, with no instance search.

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
`let` boundary. Definition checking retains the chosen target, statics, module,
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
primitives in protocols keep the participant-owned helper boundary. The stopping
bound is a source contract, not inferred from a backend implementation. Formal
intrinsics called from local code retain the existing realization boundary.
Retained helper calls, including mapped primitives, count toward the call-depth
limit; directly emitted primitive operations add no helper edge.
The prelude is excluded from capture file/byte limits, but its parsing and
checking count toward token, declaration and work limits for the invocation.
`!`, `&&` and `||` keep their fixed Boolean control/formula semantics and are not
redefined by library equality bindings.

### Modules and body modes

An interface declares associated types/domains and math/local member signatures.
A module may select one interface and must define every required member exactly
once. Additional declarations and private helpers are allowed. A generic `M: I`
client sees only `I`; concrete module paths may use additional public members. Associated
abstract runtime types expose only their promised usage properties. Concrete
associated types derive usage properties from their representation; explicit
resource attributes can strengthen those restrictions. Associated `Field` and `Group` declarations expose their
selected domain. Conformance checks callable modes, types, permissions, natural
preconditions, callback acceptance contracts and implementation effects. An
implementation cannot require more than its interface allows. Interfaces and
modules may have static parameters;
abstract callable signatures may declare member-specific generic parameters.
Associated types use only their owner's static parameters; member-specific
parameters on associated types are rejected.
`Module::method<F, ...>(value)` supplies the module parameters directly;
`C::method(value)` through a bound module uses the parameters already in `C`.
`type Name = T;` is always a transparent alias. `type Name: Type = T;` or
`type Name: Copy + Drop = T;` declares a sealed associated type, including outside
an interface implementation. Interface `type Name;` is an abstract requirement;
its implementation must explicitly declare a nominal type with `:` or a resource
or sealing attribute. Interface
membership never changes an alias's meaning. The module path and canonical static
arguments determine nominal identity, independent of imports or file layout.
Records and variants are ordinary module declarations. An abstract call or type projection
requires a bound module; a free interface name cannot select an implementation.

Defined Local functions infer a symbolic union of fixed `stop` and `opaque`
effects and dependencies on invoked callback inputs. An optional `effects(...)`
clause is an absolute upper bound. It follows the result and precedes `where`.
`effects()` forbids both tracked effects; `effects(stop, opaque)` allows both.
An output clause may name its own callback inputs, as in `effects(body)` or
`effects(first, second, stop)`. These names resolve to signature slots and denote
unions, not invocations. Duplicate entries, data names and unknown names are
rejected. `effects` remains a contextual word, usable as an ordinary identifier.
The former punctuation spelling is rejected.

A truly abstract Local output requires an explicit clause. A registered
`primitive(...)` or `finite(...)` definition instead obtains its effects from
its checked implementation contract. Math signatures allow neither tracked
effect. An empty Local effect allowance never establishes Math formation or
freedom from arbitrary host failures. Opaque runtime intrinsics are not exposed
by this profile.

Containment holds for every admissible assignment of effects to callback slots.
For each tracked label, a fixed effect on the left requires a fixed allowance
on the right; a dependency requires the same slot on the right unless that
label is allowed unconditionally. Labels excluded by a callback ceiling do not
contribute. Comparing maximum effect sets is insufficient: `effects(first)`
does not permit invoking `second`, even when their ceilings match. Module
input contracts remain equal after substitution, including callback mode, types,
ceilings and domain contracts. The implementation body must be pointwise within
both its own written output bound and the interface output contract. A wider
written bound on a defined member does not discard its more precise body summary.

Bodies use lexical `let` and `let mut` bindings, whole-name assignment, nested
block expressions and a final `return`. [Body semantics](protocols.md#bindings-and-local-control)
define scopes, patterns and resource joins. Arithmetic retains the fixed
`*`, `+`, `-` and `==` descriptors and field/group contracts; imported notation
adds callable spellings under the [binding-power rules](notation.md#expression-association).
Chained equality requires parentheses. No implicit field conversion occurs. Field literals need a unique
expected field from an annotation, operand, call or result. Installed contracts
check canonical spelling and characteristic bounds without modular reduction.
For an abstract field, only the universally valid literals `0` and `1` are admitted.
A binary field's characteristic is two, so its other constants are
[bit-pattern literals](../domains/values.md#bit-pattern-literals) passed as
`field.constant` parameters, such as `kernel<K>("field.constant"; "0x1b")`.
Boolean literals need no domain. Record construction supplies every field exactly
once. Variant construction uses `Choice::Some<Fr>(x)` in local code.

## Finite domains

A finite domain is a static description of an enumeration. Its ordinary data
operands remain checked values; the domain itself is not a runtime `Type`, an
Entry port, or a value that can be returned by an ordinary function.

```zkc
domain fn elements<F: Field>(xs: Vector<F>) -> domain<F>
  = domain("elements");
domain fn indices<F: Field>(xs: Vector<F>) -> domain<index>
  = domain("indices");
domain fn range(lower: index, upper: index) -> domain<index>
  = domain("range");

domain fn positions<F: Field>(xs: Vector<F>) -> domain<index> {
  let rows = indices(xs);
  return rows;
}
```

Registered domain definitions validate their complete signatures. Constructors
cover container elements and indices, half-open ranges, strict zip, independent
product, explicit matrix rows/columns/coordinate order, and fixed source arrays.
The [finite IR contract](../ir/finite.md#domain-declarations) defines enumeration
and admission. Defined factories compose domain calls and immutable aliases;
ordinary computations producing their data operands stay at the call site.
Interface and module members use the same resolved factory identities.

At an expected scoped-domain input, an ordinary collection expression has one
implicit element traversal: native vectors, group vectors, immutable sequences,
index collections and fixed field arrays use `elements`; fixed source arrays
use `source_array`. The expression is evaluated once at its written argument
position. The conversion changes neither its representation nor the surrounding
call's mode. It records the source expression and exact operand for independent
checking. Domain factories may use the same conversion on their data inputs.
A matrix requires an explicit view; a scalar or unknown representation cannot
be converted by guessing a domain from the callback's result type.

Math and Local functions may accept `rows: domain<I>`, forward it, or
capture it in scoped computations and local control. A domain factory accepts
ordinary data and domain parameters. Protocol signatures cannot expose domain
parameters, but protocol bodies can construct domains and use them in calls or
nested protocol repetitions. Each captured data operand must be available to its
executing participant; a domain does not introduce communication.

Domain data expressions execute at their written argument positions, alongside
ordinary arguments and callback snapshots. Aliasing a domain does not reevaluate
these expressions. A selected factory retains its complete constructor recipe,
including unused intermediates, for admission at a finite consumer. Merely
forwarding a domain through an ordinary helper does not admit its constructors.
Unrelated domain bindings are not admitted with a consumed domain. A nested
consumer admits its domain only when that computation is reached.

Closure retains constructor order, exact item types and the identities of data
operands. Shapes and static selections determine specialization; runtime contents
do not. Shared immutable operands can reuse capture ports. Equal types alone do
not identify two containers, and a mutable successor remains distinct from its
earlier snapshot. The independent domain witness checks a supplied closed shape
against the checked factory recipe and caller operand mapping, without trusting
its cached identity. This is a checked-recipe witness, not a source-elaboration
correctness theorem.

## Finite computations

Registered finite definitions connect ordinary typed functions to the retained
[finite computation IR](../ir/finite.md). They use the same domain arguments,
scoped functions, effects and capture rules as authored helpers:

```zkc
fn fold<I: Type + Copy + Drop, S: Type>(
  rows: domain<I>, initial: S,
  step: fn(S, item: I) -> S effects(stop) where item_from(item, rows)
) -> S effects(stop) = finite("local.fold");

fn collect<I: Type + Copy + Drop, B: Type + Copy + Drop>(
  rows: domain<I>, body: fn(item: I) -> B effects(stop) where item_from(item, rows)
) -> Sequence<B> effects(stop) = finite("local.collect.sequence");
```

The complete signature is checked against the selected identity. Fold state
and domain item types are independent; Unit is a valid state. Fold requires
exactly the origin map `{1 -> 0}`: its second callback input receives the whole
item from its sole domain formal. Collect and predicates require `{0 -> 0}`.
The general callback contract supports arbitrary positions; a registered finite
definition must still obey its fixed state/item ABI.
`local.fold_where` adds a predicate before the step parameter. Its predicate
has signature `fn(item: I) -> bool effects(stop) where item_from(item, rows)`; false skips the step.
The corresponding collect identities are `local.collect.vector`, `.groups`,
`.sequence`, `.indices` and `.field_array`; each admits the matching native
result type. Appending `_where` adds a predicate before the body, except for
fixed field arrays, whose result length cannot follow from a general filter.
`math.` identities require Math functions and total Math callbacks.

Eager argument computations and capture snapshots execute in written order,
including named arguments. Domain admission follows those computations. A fold
then calls its step in enumeration order; an empty fold returns its initial
state after admission. A collect preserves body-result order. Stops propagate
through the ordinary Local path. No associativity law is assumed for a fold.
Nested finite calls admit their own domains only on reached body invocations.
Fixed source arrays use the same finite consumer through a checked immutable
sequence conversion; this preserves their ordinary flattened source ABI and
array element order, including empty arrays and Unit elements.
The [status page](../../status.md) records source integration coverage.

Callback origin contracts are canonical partial maps from explicit input
positions to enclosing domain formal positions. For forwarding, substitute the
actual domain arguments first: every restriction of the supplied callback must
appear in the receiving consumer's guarantees at the same input position and
with the same domain identity. Thus the supplied restriction map must be a
subset of the receiving guarantee map. An unrestricted callback can flow to a
restricted consumer; the reverse and partially guaranteed multi-input contracts
refuse. Generic definitions are checked with distinct abstract domain identities,
independently of eventual callers. Equal types or equal domain contents do not
identify origins. A wrapper cannot promise items from `a` and forward its
callback to a fold over `b`.

Literal bodies receive a whole-item fact at every constrained input position.
Multiple independent origins do not imply a shared iteration or correlation;
correlated coordinates require one whole item from a zip/product domain. Immutable aliases,
capture snapshots and invariant region inputs preserve it. A checked concrete
Math helper returning that whole input also preserves its item provenance,
including through nested exact forwarding. Returning only a projection does not
make that projection the whole item. Invoking a restricted
callback requires its whole item, so constructing an equal-looking tuple or
performing arithmetic does not establish provenance. Control results and loop
state successors are fresh; a loop may capture an item as an invariant and call
the callback on that captured item. Domain aliases retain identity; separate
factory applications do not imply domain equality.

These contracts are checked over the completed typed body and its static call
environments. Named arguments can therefore place the callback before the domain
without delaying its capture snapshots. The retained source witness reruns the
same semantic validation from the actual graph. `source.scoped-domain` reports
an invocation or forwarding contract that cannot be established. This check
alone grants no total indexing bound.

### Total access and data preconditions

A total access needs a bound on the exact immutable container and index. Math
functions can declare input conditions separately from static type/natural
requirements:

```zkc
math fn at<F: Field>(xs: Vector<F>, i: index) -> F
  where in_bounds(i, xs) {
  return intrinsic<Vector<F>>("container.at", xs, i);
}

math fn read_other<F: Field>(xs: Vector<F>, ys: Vector<F>, i: index) -> F
  where in_bounds(i, xs), equal_extent(xs, ys) {
  return at(ys, i);
}
```

Selectors name input ports and immutable product fields, such as `record.values`
or `pair.0`. `in_bounds(i, xs, axis)` defaults to axis zero;
`equal_extent(xs, ys, left_axis, right_axis)` defaults both axes to zero.
A vector-like container has axis zero; a matrix has row axis zero and column
axis one. These conditions are supported on native collection carriers,
including packed sequences and fixed field arrays. A flattened source array is
not a single carrier and cannot be used in a declared data condition. Implementations may use a subset of their interface member's conditions,
with logical selectors and axes matched by input position; condition order is
irrelevant. Additional conditions require an explicit interface contract.
Declaration inspection includes these conditions in `requirements`.

`container.at` takes the complete container type as its static argument and
returns its logical element. `matrix.at<Matrix<F>>(m, row, column)` requires
both coordinate bounds. The corresponding intrinsics are written
`intrinsic<Container>("container.at", xs, i)` and
`intrinsic<Matrix<F>>("matrix.at", m, row, column)`. Packed sequence records and
tuples are unpacked using their ordinary source layout.

An item from `indices(xs)` establishes its bound to `xs`; matrix coordinates
establish both axis bounds. Zip/product item projections and invariant captures
preserve those facts. Equal extents transfer bounds between containers without
equating their elements. A range item, shifted index, reconstructed value or
mutable successor supplies no implicit container bound. Constant indices can
use known fixed extents. Invalid accesses are rejected even when their results
are unused.

Concrete checked Math helpers can preserve exact input identity through their
results, including full product projections and chains of forwarding calls.
Each call must discharge its own input conditions before that information is
available. Forwarding an index literal preserves its known value; returning an
unrelated container or computing an index does not supply that fact. These
observations belong to the current source check and do not change callback
capture layouts. Result observations are cached only over an immutable checked
helper closure; each call substitutes its actual inputs and projections.
Sequential SSA dependencies use bounded work rather than recursive call depth.
Helper-call depth remains bounded independently of enclosing control regions
and callback bindings.

An unfiltered finite collection has a fresh value identity and preserves its
domain's cardinality. Element and index domains also relate its extent to the
selected input axis, so indices of the original collection can read the result.
These result properties also pass through total acyclic helpers and immutable
record fields, while each constructed result retains its fresh identity.
A domain parameter can describe a result count without identifying its items.
Filtered collections generally provide only an upper count; zero is also exact.
Such an upper count cannot justify a positive indexing bound or fixed length.
Known ranges and products use checked cardinality arithmetic. All constructor
admission remains required, including unused zip constructors and empty domains.
For a fixed-size result, a known conflicting count is rejected during source
checking, including in an unused declaration. Its type supplies its extent;
unresolved formation supplies no additional count or equality to the source
domain. Closure must still establish the exact unfiltered size.

A direct Math call to a registered Math finite definition is specialized at the
call occurrence with its actual domain and callback bindings. For example,
`field_array::collect(range(0, 4), fn(i) => value)` can establish four elements
without turning the endpoints into unconstrained helper parameters. Its output
type must still request that exact length. Ordinary helpers receiving a domain
parameter retain their generic formation boundary; caller-specific constants
do not justify a generally typed helper or a Local finite declaration.

An ordinary Math call discharges its callee's conditions. Local and protocol code
can realize an unconditional whole Math computation; they cannot assume input
conditions or treat a runtime check as a Math proof. At closure, extracted helpers
receive explicit conditions on their ordinary inputs. The enclosing finite
computation discharges callback conditions from its domain, captures and input
conditions. Ordinary Math functions must discharge all requirements using their
declared conditions. Specialized scoped/domain combinators can carry residual
conditions for their selected static environments; a caller does not silently
strengthen an ordinary function's contract. Closed descriptor formation also checks every retained zip and
matrix view, including unused factory intermediates and empty enumerations.
A fixed-size collect requires an exact unfiltered cardinality. Failure to derive
these facts is `source.data-bound`; installed backend support remains a separate
requirement.
For Local collects, that size must follow from the formal input types retained
by the emitted declaration. Call-site constants and source-array lengths erased
by conversion to dynamic Sequence inputs cannot establish a fixed Local result.

## Scoped computations

Named Math and Local functions, including interface/module members, may take
statically bound, nonescaping computations as a separate input category:

```zkc
math fn apply_math<A: Type + Copy + Drop, B: Type + Copy + Drop>(
  value: A, body: math fn(A) -> B
) -> B {
  return body(value);
}

fn apply<A: Type, B: Type>(value: A, body: fn(A) -> B) -> B effects(body) {
  return body(value);
}

fn forward<A: Type, B: Type>(value: A, body: fn(A) -> B) -> B effects(body) {
  return apply(value, body);
}
```

Computation parameters, written `fn(...) -> ... effects(...)` or `math fn(...) -> ...`,
are static, nonescaping inputs. Their signatures are not runtime `Type` values.
A computation argument is a literal or an in-scope
computation parameter. It cannot be bound by `let`, put in a product or variant,
returned, sent, used as a data argument, or selected by runtime control.
Protocol signatures and Entry ports cannot expose it. A protocol body may call
a named function with a literal scoped argument. Invocation and forwarding
select a statically known body; there is no dynamic dispatch or closure ABI.

A callback signature accepts optional labels on its data inputs:
`fn(state: S, item: I) -> S effects(stop) where item_from(item, rows)`.
The order is inputs, result, optional effects, then optional callback-local
`where`. Named and unnamed input types can mix;
only inputs selected by a condition require a label. Labels are unique within a
callback and obey ordinary binding-name/shadowing rules. Different callbacks
may reuse labels. Labels do not bind values or types, and literal binders and
positional invocations need not use them.

Callback-local `where` accepts only `item_from(input, domain)` clauses separated
by commas, or `where ()`. The first selector names this callback's input; the
second names an enclosing domain formal, independently of textual parameter
order. Input and domain item types must match. Unknown/category-invalid selectors,
projections, numeric selectors, duplicate clauses and multiple domains for one
input refuse. There is no implicit last-input selection, arbitrary predicate,
result condition or alternative parenthesized nonempty clause list.

`item_from` is contextual, not reserved. After a clause comma, a two-token
`name :` prefix begins the next enclosing parameter; `item_from (` begins another
condition. A parameter named `item_from` therefore remains valid. A malformed
condition stays a callback-clause error. The callback clause never sets the
outer declaration's explicit requirements flag: open catalog/natural inference
continues, while an outer `where ()` still closes the outer contract. Outer
`where item_from(...)` is rejected with a diagnostic directing it to the callback.
Anonymous literals inherit conditions; they cannot author their own clause.

Conditions require compiler-tracked whole original items from exact domains,
not value membership or equality. Each invoker proves the conditions and a
literal body assumes them. A canonical position-to-domain map excludes source
labels, clause order and spans from semantic compatibility and specialization
identity. Interface/module conformance requires exact normalized map equality
after type substitution; it does not apply forwarding subtyping. Source-bearing
artifacts may still change when labels change. Parsing, normalization, map
substitution and independent witness reconstruction charge the shared work budget.

The literal syntax is `fn(x) => expression` or `fn(x) => { statements; result }`.
The same `fn` keyword introduces named declarations; an anonymous literal omits
the name and starts its parenthesized input list immediately. Inputs are
comma-separated, with an optional trailing comma. `fn() => expression` takes no
inputs; `fn(()) => expression` takes one Unit input.
`fn(x, y) => expression` binds two inputs. `fn((x, y)) => expression` destructures
one tuple input; it does not curry the function. Ordinary binding patterns,
including `_`, apply. Input and result types are inferred contextually using
the ordinary expression solver and the receiving scoped signature. Generic
functions and their literal computations are checked even when unused. The
enclosing definition infers requirements under the ordinary `where` rules;
call sites check that contract and do not repair malformed definitions.

A signature fixes the body's mode. `math fn(A) -> B` is total Math;
`fn(A) -> B` is ordered Local. An omitted Local callback ceiling allows both
tracked effects. An explicit `effects()` accepts only nonstopping, nonopaque
callbacks; `effects(stop)` excludes opaque effects. The written callback ceiling
contains fixed labels only, never sibling or enclosing callback names. In callback
headers, `effects(...)` precedes `where item_from(...)`.

Invoking a callback contributes its bounded symbolic dependency, not its full
ceiling. Calls substitute actual callback summaries into the callee summary.
Defined helpers retain body precision below their written upper bound; abstract
calls use the published contract. Forwarding preserves slot identity, including
captured outer callbacks in nested literals. An unrestricted callback cannot be
forwarded to an empty-effect receiver. An unused callback contributes no
invocation effect, but eager arguments, domain operands and capture evaluation
retain their effects. Local finite admission still contributes `stop`, including
empty traversals, and registered Local finite callbacks exclude `opaque`.

A Local computation cannot be invoked in Math. Module members retain lexical
member resolution, notation and `self`, including through nested lambdas.
Open bodies have one canonical symbolic effect summary. Specialization produces
a closed summary from the selected helpers; independent extraction and closure
checks reconstruct effects from operations and validate retained identities.
Immutable authored signatures independently anchor callback ceilings, item-origin
selectors and output contracts, including abstract declarations.
Origin maps belong to the declaration's callback parameters, whose domain slots
they reference; body signatures carry only types, mode and effects. Independent
checking also compares a module's callback contracts with its interface after
substituting the module's types.
Dependency normalization, substitution and witness traversal use the shared
work budget.

Local literals use ordinary blocks, `if`, `match`, loops, mutable local state,
stopping and short-circuit Boolean semantics. A Local literal authored in a
protocol still short circuits. A Math literal authored in a Local function
remains total; dead intermediates must satisfy typing and formation rules.
Control syntax never changes a literal's selected mode.

Free data places are captured by lexical binding identity and projection path.
Whole aggregate captures subsume their descendant projections; sibling
projections remain distinct even when their types match. Captures are ordered
by their first authored use. Every captured type requires both `Copy` and `Drop`.
Immutable records, tuples, arrays, vectors and matrices follow these same rules;
there is no scalar-only capture restriction. A mutable Copy binding is captured
as its current immutable value. Captures are evaluated once, when the literal's
argument position is reached. Named arguments reorder parameter binding but
preserve written evaluation order. Repeated invocation reuses these snapshots;
a nested literal takes its own snapshots when its enclosing code reaches it.

A literal cannot write an outer binding or capture a managed service. Its own
explicit inputs and locally carried state follow the ordinary affine rules and
need not be Copy. A static scoped capture may refer to an enclosing scoped
parameter; its selected body and runtime environment are forwarded explicitly.
No runtime function value is stored in that environment.

For a direct protocol call to a Local accepting function, eager data arguments
and every runtime capture constrain one common owner. P-only captures can select
P when a data argument is shared with V. Incompatible captures or an unresolved
owner refuse. A constant Math callback's result does not choose the owner of an
eager Local argument: `apply_math(local_identity(shared), fn(_) => 0)` still
requires an independently determined owner for `local_identity(shared)`.

The shared summary query uses the checked `Body`. It separates result
dependencies, formation obligations (including dead intermediates), and effects.
An unresolved scoped formal is marked as parameterized; it is never treated as
a concrete constant. Math summaries compose under the selected bodies and
capture mappings. Equal formation dependency sets may be deduplicated; this
does not omit operation coverage. Local placement uses all eager operands and
captures independently of mathematical result dependencies.

Closure materializes ordinary private helpers with explicit capture inputs and
specializes accepting functions with the selected helpers. Their hidden data
inputs follow ordinary data inputs; forwarding passes the matching environment
in that order. The key includes the lexical body, closed static/module
context, signature/layout and recursively selected scoped captures. Runtime
values and caller roles do not prevent code reuse. Scoped invocations are gone
before MLIR emission. Expansion, flattened environments, summary work and helper
instances count against the ordinary work, operation, depth and instance bounds.
Cycles and excessive completed-instance call heights refuse.

Independent origin checking reconstructs normalized contracts from retained
source labels and clauses, checks exact input/domain types and coverage, and
rejects changed slots, domain positions or missing requirements even if body
signatures were changed to agree. These source selectors are compile-time
evidence, not trusted runtime attributes.

Independent capture checking walks retained resolved syntax to reconstruct
free places and compares actual capture slots, snapshot projections, types,
roles, lexical identity and occurrence coverage. A separate specialization
checker relates checked bodies to the actual candidate under explicit static,
scoped and SSA substitutions; it does not call the specializer. It checks helper
selection, hidden operands, forwarding, control regions, owners, effects and
every operation, including dead work. Missing or duplicate occurrence evidence
refuses. These executable checks do not constitute a theorem about the parser
or complete elaboration semantics.

Within scoped bodies, ordinary notation calls are rechecked against retained
definition-site families and authored operands. Every retained notation
occurrence must have exactly one matching call, including its source span and
binding evidence; removing the expression mapping or binding refuses. The
callback result must agree with its authored tail expression. Resolved syntax
and the retained lexical families remain trusted inputs to this check.

Declaration inspection reports `scoped_inputs` separately from `inputs`, with
name, mode, input/result types and effect allowance. Each callback also has
`input_labels`, an array parallel to `inputs` with a string or null per input,
and `item_origins`, an array of exact `{ "input": unsigned, "domain": unsigned }`
objects sorted by input position. Both positions are zero-based; `domain` indexes
`domain_inputs`, not the interleaved authored port list. Both arrays are always
present, including an empty origin list. This is the sole version-0 schema;
there is no legacy suffix or inspection alias. Enclosing `requirements` remain
obligations of the enclosing signature. `input_order` retains `data`, `service`,
`domain` and `scoped` categories. This diagnostic view does not add runtime
interface fields. The [callback example](../../../common/tests/fixtures/projects/scoped-computations/callbacks.zkc)
and [module example](../../../common/tests/fixtures/projects/scoped-computations/README.md)
exercise user-defined apply/forward combinators. General finite domains, named consumers and mathematical binders use this same
foundation.

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
| Charged work per phase | 8,000,000 |
| Emitted MLIR; interface JSON | 16 MiB; 4 MiB |
| Encoded symbol; diagnostic path bytes | 4096 each |
| Active notation descriptor keys per environment; delimiter holes | 4096; 64 |
| Notation inspection JSON | 8 MiB |
| Location records, five 64-bit coordinates each | 16 MiB |

The import-depth ceiling also bounds the dependency chain used to construct
notation environments, including lexical parents and the installed prelude.
Bodies in one source file share its filtered token stream, with a separate
notation environment for each module.

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

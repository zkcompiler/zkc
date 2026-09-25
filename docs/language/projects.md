# Source projects and checked libraries

A project captures its source files, explicit library roots and relation assets
before checking. Resolution chooses exact declarations; it does not concatenate
files or search an ambient package registry. The ordinary PIR emitted afterward
contains no package loader or dynamic component dispatch.

## Authoring and loading

An importable root declares its identity. A client declares the exact dependency
and imports the public names it uses:

```text
// library/lib.pir
module {
  library(namespace="example", name="bits", version="1", resolution="source-v1");
  pub fn Identity(value: bool) -> bool { return value; }
}

// app.pir
module {
  dependency bits = library(namespace="example", name="bits", version="1", resolution="source-v1");
  use bits::Identity as Keep;
  fn Main(value: bool) -> bool { return Keep(value: value); }
}
```

```sh
build/compiler/zkc-compile protocol-analyze app.pir --library=library/lib.pir
build/compiler/zkc-compile protocol-source app.pir --library=library/lib.pir
```

An application need not declare an importable identity. The loader accepts
repeated `--library=FILE` options, each naming a root. Every supplied root must
be in the application's dependency closure; an extra one refuses with
`project-library-unreachable` rather than taking part in origin qualification. Source `mod helpers;`
loads `helpers.pir`; a child `mod arithmetic;` loads
`helpers/arithmetic.pir`, relative to that library's root directory. `pub mod`,
`pub use`, grouped imports and `as` aliases control its public surface. Private
names are available in their defining module and descendants. A public signature
cannot expose an inaccessible concrete declaration. Reexporting a public name
through a private implementation module is permitted.

Dependencies must be captured explicitly and form an acyclic graph. A second
root claiming an already captured identity refuses, including an identical copy;
share one captured root through the dependency graph instead. The installed
contract owner and synthetic application owner are reserved. Anonymous application
identity is derived from the captured contents, independently of physical
filenames. Dependency aliases, file paths and file ordering are not declaration
identity.

Authored references must resolve to a local binding, a visible declaration or
installed vocabulary. Generated implementation symbols cannot be called by
spelling them, including quoted names. A relation helper is reached through its
visible view declaration. Convenience `module <profile>` declarations belong
only to the application root; imported and child code uses explicit domains and
does not inherit that root's profile defaults.

Relation references are relative to their declaring file, remain within the
library root, and are read into the same snapshot. `protocol-resolve` produces a
portable frozen relation snapshot. Later source analysis and compilation consume
those captured bytes. No frontend query implicitly installs packages or fetches
relation files from a network.

## Checking and selection

A checked declaration's environment contains its owner's declarations, direct
public dependencies, the public signature closure and the fixed installed
contracts. It excludes its dependents and unrelated dependency-private bodies.
A shared dependency therefore has the same checked identity through both arms
of a diamond import. Linking separately obtains the checked private bodies it
actually needs and the caller's captured environment for selected static actuals.
That selection environment does not replace a library's own checking context.
A matching spelling or fingerprint cannot replace exact subjects.

An interface's parameter labels are public API. Its implementation can choose
different private binder names. All named arguments are bound to public ports;
expressions execute once in written order before the resulting values are
permuted into port order. Stopping an earlier expression prevents later evaluation.
Static inference uses the existing bounded equality/requirement machinery. It
neither guesses a component nor inverts an abstract associated-type projection.

A checked helper call refers to a formed callable and its checked body dependency.
It can compose ordinary or generic helpers whose contracts pass the same
resource/effect checks. The reachable graph must be acyclic and bounded. Closed
`link` aliases retain logical labels and aggregate types before representation
lowering. `configure` also selects a checked generic helper by its named static
parameters; component applications can be named with `select` and passed to a
link. Protocol code calls the resulting closed algorithm.

Concrete arrays retain both element type and count, separately from tuples,
including `Array<bool, 0>` versus `Array<index, 0>`. Nested records retain nominal
identity. Lexical traversal uses the checked array-traversal owner:

```text
fn Last<N: nat>(items: Array<bool, N>, initial: bool) -> bool {
  return fold items with initial |state, item| { item };
}
configure Three = Last(N = 3);
```

`map items |item| { ... }` collects one result per element. `fold` threads explicit
state in order and returns the initial state for an empty array. The blocks do
not escape or create runtime function values. Free places are captured in first
use order; explicit capture lists remain checked overrides. Repeated captures
require copying permission, while affine elements and state move through the
traversal. Large algebra should use bulk operations instead of expanding a large
finite traversal.

`select` aliases preserve a selection; `seal` introduces an explicit distinct
selection. The split multi-type comparison gives one shared identity per
associated type for two aliases; two seals distinguish both types together.
A component designed with an explicit association parameter can provide the same
separation. Sealing supplies that distinction without changing the provider API.
It remains an advanced option. Concrete nominal wrappers can
separate concrete value types, but currently cannot wrap every abstract associated
type generically. This feature does not mint evidence or establish freshness of
cryptographic randomness.

## Names, observations and queries

Explicit `::` qualification preserves each member's spelling: `Root::child.part`
selects one member named `child.part`, while `Root::child::part` selects two
successive members. Resolution keeps that distinction through imports and aliases.

The frontend keeps exact declaration identity, emitted symbols and logical
origins separate. Imported ordinary symbols have collision-checked compact
locators; equality still uses exact identities. A declaration's name cannot
begin with a prefix of the symbols the compiler generates: `src_` for imported
and module declarations, `lib_` and `client_` for linked library functions and
their entries, and `__library_operation_` for library operation bindings
(`source-name-reserved`). The explicit `carrier module` representation preserves
those names on format/read round trips; it cannot import or define authoring
libraries. `Relation_` is an authored origin convention, not a reserved
implementation-symbol prefix. Readable logical origins acquire
an owner qualifier when different libraries would otherwise collide. Every owner
in that collision class is qualified. The unique anonymous application's qualifier
is `application`; its exact declaration identity remains captured-content scoped.
An old ambiguous selector refuses. Explicit application-root origins can group
several functions, but cannot impersonate automatically allocated imported,
component-member or captured-relation origins.

Construction selectors resolve against the captured source project. The entry
selects a protocol instance; draw selectors choose logical sampling occurrences.
A generic definition selector follows its specializations; a configuration
selector identifies one selected callable. Ordinary functions, including imported
functions and members of explicit origin groups, bind to their emitted symbols;
they do not select sibling group members merely through their explicit origin.
If the direct concrete spelling is also a different origin family's name, the
request refuses `construction-source-selector-ambiguous`: the closed two-field
selector cannot express direct-only scope in that case. The source remains
valid. `use` aliases denote the original
declaration. Under normalized identity a bound selector whose name is not a
carrier declaration has no site map of its own, so the project writes it out as
the functions carrying the requested site. This includes explicit origin groups
and logical component-member selectors. Each function then uses its own site
map. A group with no matching site refuses at normalized site resolution
(`source-site-selection`), or at exact construction (`construction-draw-selector`).
This does not promise that arbitrary helper extraction,
library-version changes or occurrence renaming preserve proof bytes.
Construction identity remains observable.

`protocol-analyze` reports files, resolved identities, source-to-emitted names,
interface/body/link dependencies, retained checked capabilities and diagnostics.
Missing imports can leave independent declarations queryable, but incomplete
projects never emit accepted code. Resource exhaustion reports an unavailable
judgment. Source checking does not imply PIR admission, runtime readiness or a
cryptographic theorem. Ordinary unused-binding warnings do not identify verifier
results by name or prove that acceptance depends on a checked Boolean.

## Executable examples and limits

The [project examples](../../examples/projects/README.md) split library and client
source for Groth16/R1CS, native prepared KZG indexes with compiled opening checks,
AIR/FRI, group/RNG and finite opaque views. Their tests compare imported source
with independently authored closed baselines, use native/Lean admission, and
exercise actual execution and negative controls. Groth16 requires the documented
real external fixtures. KZG's exact index/relation binding remains a host premise;
an ordinary compiled opening check does not establish that binding.

Capture is bounded to 64 roots, 256 source files, 1 MiB per source and 16 MiB total
source, with at most 64 logical module segments. Resolution has a shared work
budget; draw-selector enumeration also refuses after 32,768 paths or a
4,096-byte path. Entry lookup has a separate bounded namespace, so entries do
not consume draw-selector capacity. Existing relation import/byte
budgets apply across the project. Static checking, expansion and descriptor
budgets remain separate. Nested algorithm occurrence names retain their existing
128-byte bound; a source project may resolve yet refuse executable expansion at
that boundary. Measured examples do not establish arbitrary-scale compilation.

There is no package manager, persistent incremental cache, runtime module dispatch,
verified native resolver or general dependent type inference. The finite Lean
source laws and differential tests support the stated boundaries; they do not
verify the C++ frontend or supply protocol security proofs.

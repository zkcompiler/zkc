# Writing protocols

Write `.zkc` modules and select an Entry to compile and execute a protocol. The
frontend checks the source and emits Protocol IR (PIR), built on MLIR, for the
common participant compiler and Rust Host.

Start with the [walkthrough](../getting-started.md), then read the
[mathematical source guide](mathematical.md). The maintained
[Schnorr and Sumcheck projects](../../examples/projects/README.md) use the
[maintained libraries](../../libraries/README.md) with separately authored Entries.

| Task | Reference |
|---|---|
| Define types, helpers, roles, services and control | [Mathematical source](mathematical.md) |
| Use Unicode names, operators and delimiter calls | [Mathematical notation](notation.md) |
| Select a closed job | [Entry declarations](entries.md) |
| Compile, run, prove or verify an Entry | [Entry execution](../runtime/entries.md) |
| Capture relation data and bind its meaning | [Relation Assets](relations.md) |
| Read exact typing, effects and Entry rules | [Mathematical language profile](../spec/language/README.md) |

The compiler checks declared contracts and availability. A relation clause alone
adds no runtime guard or proof of satisfaction. Backend implementations must
satisfy their operation and representation contracts; a successful type check
does not infer cryptographic assumptions. [Status](../status.md) records supported
syntax and native capabilities, and [model guides](../../lean/docs/README.md) explain
the independent semantic foundations.

## Project inputs

`zkc.toml` records explicit source and asset locations. Relative paths use the
manifest's visible parent, including when the manifest is a symlink. Local
dependencies select library directories with their own `zkc.toml`. Their explicit
source maps are combined before compilation; imports never search directories.

```toml
format = "zkc.project/0"

[modules]
example = "main.zkc"

[dependencies]
schnorr = "../../libraries/protocols/sigma/schnorr"

# Optional external relation data.
[assets.constraints]
format = "ring-json"
path = "constraints.ring.json"
```

An explicit local catalog avoids repeating library directory paths:

```toml
[workspace]
path = "../../zkc.workspace.toml"

[dependencies]
schnorr = { workspace = "protocols.sigma.schnorr" }
```

Use this dependency table in place of the path table above. The repository's
[catalog](../../zkc.workspace.toml) lists leaf packages. A catalog contains
`format = "zkc.workspace/0"` and a `[packages]` table of keys to directories or
manifest files, relative to its own visible parent. Only selected packages are
loaded. Each consuming manifest names its catalog explicitly; children do not
inherit a parent's choice. Existing string path dependencies remain supported.
The installed `zkc` package supplies `share/zkc/zkc.workspace.toml` and its source
tree; an external project can explicitly select that catalog or one installed
leaf directory. Catalogs perform no download or version selection.

From the project directory or a subdirectory:

```sh
zkc check
zkc check Proof
zkc compile Proof
zkc compile example::Proof --output=proof.zkpkg
```

`check` checks every definition, including generic library bodies. Its `entries`
array lists canonical names and `run`/`proof` kinds. Selecting an Entry also
checks its closure, Protocol IR and source correspondence. A definitions check
alone does not establish that every specialization can compile. Neither form
executes a protocol. `scope` distinguishes `definitions` from `entry`.
Use `--json` to read these fields programmatically. For input templates and
execution defaults, see the [project workflow](../runtime/entries.md#project-workflow).

A selector is a qualified name or a unique short name across all captured
modules. `compile` can omit it when exactly one Entry exists. Aliases count as
separate candidates. Ambiguity is an error with candidate names; the compiler
never prefers one execution kind or module.

The CLI discovers the nearest `zkc.toml` in the current directory or its ancestors.
An invalid nearer manifest fails instead of selecting a parent. `--project=FILE`
selects one explicitly. Repeated `--module=NAME=FILE` and `--asset=NAME=FORMAT=FILE`
options disable discovery and cannot be combined with `--project`. SDKs use
explicit captures. The manifest chooses no Entry, backend, transcript or setup
policy. See [relation inputs](relations.md) for asset formats.

Project compilation defaults to `build/zkc/<qualified.name>.zkpkg` beside the
manifest. It creates that directory and replaces prior output at the exact
filename, including obsolete or damaged packages. Input aliases and filenames
differing only in case are refused. Use `--output` for another filename; explicit
module mode requires it. Explicit command-line paths are relative to the invocation directory.
Reports include the selected compiler, manifest when used, output path and package
SHA-256. Paths do not enter source capture identity. The `.zkpkg` extension is a
filename convention; readers check the package format.

`zkc inspect --view=api` also reports `project_graph` when using a manifest. Its
`zkc.project-graph/0` diagnostic format records the root manifest and packages
sorted by manifest context. Each package retains its own explicit module and
asset maps and direct dependencies, mapping dependency labels to manifest
contexts. File symlinks keep their visible parent context; shared directory
contexts appear once. This metadata is separate from source capture and is
absent for explicit module/asset maps and SDK captures.
Every package also has `catalog_dependencies`, mapping only catalog-selected
dependency labels to objects with `catalog` (the visible catalog context) and
`package` (the selected key). `dependencies` retains every resolved provider
manifest regardless of how it was selected. Both maps are sorted by label.

## Inspect completed declarations

```sh
zkc inspect --project=libraries/core/polynomial/zkc.toml --view=placement
```

The report's `checked.declarations` array lists public mathematical functions,
local functions and protocols by qualified name. It shows static parameters,
permissions, input/output types, participant roles, services, completed
requirements and effects. Members name their interface/module owner and mark
inherited parameters; abstract members report their allowance explicitly.
Inferred natural/capability requirements are marked; written effect allowances
are separate from actual body effects. Each effect summary contains fixed
`stop`/`opaque` flags and callback dependencies with their remaining effect masks.
A fixed effect removes the corresponding bits from dependency masks; callback
acceptance ceilings remain under `scoped_inputs`. Callback `input_labels` preserve
written names (or null for unnamed inputs); `item_origins` lists canonical input
and domain indices, independent of those labels. Private helpers
are still checked but are omitted from this view. The report is diagnostic data,
not an importable interface or a proof of protocol security.

Use `--api` for public types, aliases, reexport routes, notation exports and
source dependency provenance. Its `api` object keeps the selected provider
separate from the canonical target, so clients of a facade do not acquire its
private implementation dependencies. Public record descriptions omit private
fields; associated representations remain private. Reference records include
private helpers for dependency analysis and grant no access to those helpers.
The [specification](../spec/language/definitions.md) defines the bounded view.

Type errors identify conflicting shapes and related source locations. Unresolved
statics name the parameter needing an argument or result annotation; ambiguous
ordered calls list possible owners. Locations use one-based byte columns.
Excerpts are bounded and escape control/non-ASCII bytes, so caret positions in
the displayed excerpt can differ from the byte column. Rendering reads captured
bytes and never opens a diagnostic path.

The separate [notation inspection view](notation.md#inspect-notation-and-locations)
describes source syntax and visibility, with private/local and installation data
explicitly requested. It carries no native Entry interface authority.

Build settings and named implementation profiles belong to the consuming root
manifest; dependencies do not impose them. Root `[test.NAME]` recipes invoke
ordinary consumer Entries. See [compiler tooling](../compiler/tooling.md) for
configuration, precedence and test workflows.

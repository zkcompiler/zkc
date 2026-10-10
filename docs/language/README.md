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
| Select a closed job | [Entry declarations](entries.md) |
| Compile, run, prove or verify an Entry | [Entry execution](../runtime/entries.md) |
| Capture relation data and bind its meaning | [Relation Assets](relations.md) |
| Read exact typing, effects and Entry rules | [Mathematical language profile](../spec/language/README.md) |

The compiler checks declared contracts and availability. A relation clause alone
adds no runtime guard or proof of satisfaction. Backend implementations must
satisfy their operation and representation contracts; a successful type check
does not infer cryptographic assumptions. [Status](../status.md) records supported
syntax and native capabilities, and [model guides](../../formal/docs/guides/README.md) explain
the independent semantic foundations.

## Project inputs

`zkc.toml` records explicit source and asset locations. Relative paths use the
manifest's visible parent, including when the manifest is a symlink. Imports
never search directories.

```toml
format = "zkc.project/0"

[modules]
example = "main.zkc"
schnorr = "../../libraries/schnorr/lib.zkc"

# Optional external relation data.
[assets.constraints]
format = "ring-json"
path = "constraints.ring.json"
```

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

## Inspect completed declarations

```sh
zkc check --project=libraries/zkc/zkc.toml --declarations
```

The report's `declarations` array lists public mathematical functions,
local functions and protocols by qualified name. It shows static parameters,
permissions, input/output types, participant roles, services, completed
requirements and effects. Members name their interface/component owner and mark
inherited parameters; abstract members report their allowance explicitly.
Inferred natural/capability requirements are marked; effect allowances (written
or inherited) are separate from actual body effects. Private helpers
are still checked but are omitted from this view. The report is diagnostic data,
not an importable interface or a proof of protocol security.

Type errors identify conflicting shapes and related source locations. Unresolved
statics name the parameter needing an argument or result annotation; ambiguous
ordered calls list possible owners. Locations use one-based byte columns.
Excerpts are bounded and escape control/non-ASCII bytes, so caret positions in
the displayed excerpt can differ from the byte column. Rendering reads captured
bytes and never opens a diagnostic path.

# Writing protocols

Write `.zkc` modules and select an Entry to compile and execute a protocol. The
Language implementation checks the source and emits mathematical MLIR for the
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

A project file records the source and asset map. Paths are relative to that file;
imports never search directories. For example, `zkc.json` can contain:

```json
{
  "format": "zkc.project/0",
  "modules": {"example": "main.zkc", "schnorr": "../../libraries/schnorr/lib.zkc"},
  "assets": {}
}
```

```sh
zkc check --project=zkc.json
zkc check --project=zkc.json --entry=example::Proof
zkc compile --project=zkc.json --entry=example::Proof --output=proof.entry
```

`check` checks every definition, including generic library bodies, without
requiring an Entry. With `--entry`, it also closes that Entry and checks its
mathematical IR and source correspondence. Neither form executes a protocol.
The JSON report records the reached scope and capture identity. The compiler and
CLI use the same flat `zkc.source-check/0` result; the CLI adds its selected
compiler path.

Use a project file or repeated `--module`/`--asset` options, never both. The
manifest selects no Entry, backend, transcript or setup policy. Assets have
`{"format": "ring-json", "path": "product.ring.json"}` entries keyed by their
source names; see [relation inputs](relations.md) for supported formats.
[Example projects](../../examples/projects/README.md) contain complete manifests.

## Inspect completed declarations

```sh
zkc check --project=libraries/zkc/zkc.json --declarations
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

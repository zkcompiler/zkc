# Running source Entries

A Protocol defines computation and interaction. A `run` or `proof` Entry selects
one closed invocation. The common Host executes its compiled participant programs.

## Project workflow

Keep reusable protocols in libraries or `protocol.zkc`, concrete Entries in
`main.zkc`, and the explicit module/asset map in `zkc.toml`. The language also
allows protocols and Entries in the same file.

```sh
zkc new my-project
cd my-project
zkc check
# Edit the source, then prepare any new input files.
zkc prepare
```

`new` creates a directory; `init` initializes an existing directory (the current
directory by default). Both create an index echo protocol, its Entry and an input
template. They refuse an existing project or conflicting source files and preserve
existing regular input files.
Fill `inputs/example.Main/P.json`
with `{"value":"7"}`, then run:

```sh
zkc inputs check --operation=run
zkc run
```

Commands discover the nearest `zkc.toml`. Use `--project=FILE` to select another
project, or explicit `--module=NAME=FILE` and `--asset=NAME=FORMAT=FILE` mappings.
`--compiler=PATH` selects a trusted compiler; otherwise the compiler is resolved
from absolute directories in trusted `PATH`. Execution compiles in memory and
reports the resulting package identity. It does not publish an intermediate package.

`check` checks source without requiring input values. `prepare` checks input
interfaces and creates missing templates for all Entries, or one named Entry.
It preserves existing regular files byte for byte, including stale or unfilled
ones. It does not validate or migrate their contents. After changing a port,
update its input map or remove that file and run `prepare` again. Use `inspect`
for the current schema and `inputs check` to validate actual values.

With several Entries, supply a unique short name or `module::Name`:

```sh
zkc prepare example::Proof
# Fill the generated public and witness maps.
zkc prove example::Proof
zkc verify example::Proof
```

Omitted names require one eligible Entry: `run` considers run Entries;
`prove` and `verify` consider proof Entries. `inspect`, `compile`, `bindings`
and `inputs init` consider both kinds. An explicitly ambiguous short name
requires qualification. A unique Entry of the wrong kind is an error.

### Paths and sessions

| Purpose | Default beside `zkc.toml` | Override |
|---|---|---|
| Proof public inputs | `inputs/<qualified.name>/public.json` | `--public=FILE` |
| Prover witness inputs | `inputs/<qualified.name>/witness.json` | `--witness=FILE` |
| Run participant inputs | `inputs/<qualified.name>/<Role>.json` | `--input=ROLE=FILE` |
| Compiled package | `build/zkc/<qualified.name>.zkpkg` | `--output=FILE` |
| Produced or verified proof | `build/zkc/<qualified.name>.zkproof` | `--output=FILE` / `--proof=FILE` |
| Run output values | `build/zkc/<qualified.name>.results.json` | `--results=FILE` |

For `example::Proof`, the qualified filename is `example.Proof`. Unicode source
names retain their exact spelling in default filenames. Explicit paths are
relative to the working directory and override only that group or artifact.
Missing or malformed selected files fail; there is no search for alternate files.
Default output directories are created as needed. Prove and verify write named
output values only when `--results` is supplied.
For a run that needs no result file, use `--no-results`; it conflicts with
`--results`. This also allows execution when a returned value has no file codec.

Package and explicit-module modes require explicit input paths and proof paths;
they do not borrow defaults from a nearby project. A run without `--session`
receives a fresh random session identifier, shown in its report. An explicit
session is used exactly as supplied; callers are responsible for its freshness.

### Input templates

`inputs init` is the lower-level, single-Entry template command. It accepts an
explicit output directory and refuses existing files. `prepare` is the usual
project command. Both create only required groups. Null leaves are unfilled
placeholders, except for actual unit values. Neither command invents dynamic
lengths or chooses variant cases. `inputs init` reports suggested command arguments.
All initialization commands report additional `requirements`: an authored proof
needs explicit `--allow-header-only`, and each setup slot needs independent
`--setups` authority and `--key` material. Initialization never grants those permissions.
`inspect` describes the schema, choices and whether each input has an installed
constructor. `inputs check --operation=...`
uses the same native preparation as execution, including setup and capacity
checks, but runs no protocol and issues no resources. Successful preparation
is not proof acceptance or a protocol security judgment.

## Source names and native labels

Entry inputs and logical outputs retain exact NFC source names, including Unicode
participants, ports, fields, alternatives and setup slots. Raw UTF-8 and equivalent
JSON escapes identify the same decoded name. Use the names reported by `inspect`.

The authenticated interface maps names by declaration order to native
`role00000000`, `setup00000000` and `case00000000` labels (eight lowercase hex
digits, starting at zero), including ASCII source names. Direct Runner/PIR APIs
and Bundle commands use native labels; Entry commands convert source names.
Applications cannot supply an alternative renaming table.

## Input values

Input files are plain maps with exact source port names. Proofs have one public
map and a separate prover witness map. Verification accepts no witness file.
Runs use `--input=ROLE=FILE` for each role with inputs; omitted empty groups are
filled automatically. A shared source port remains a separate role-local input
in a run. Project paths follow the table above; verification never opens a witness map.

| Source value | JSON |
|---|---|
| Field or index | Canonical nonnegative decimal string, such as `"7"` |
| Boolean / unit | `true` or `false` / `null` |
| Tuple, array, vector or indices | Array of element values |
| Record | Object with exact field names |
| Variant | `{"case":"Name","fields":{"0":"7"}}` |
| KoalaBear extension field | Eight ascending coefficient strings, or a base-field decimal string |
| Sparse matrix | `{"rows":"2","columns":"3","entries":[["0","1","7"]]}` |
| Group element | `{"bytes":"CANONICAL_ELEMENT_HEX"}` |
| Explicit native encoding | `{"wire":"COMPLETE_ZKCV_FRAME_HEX"}` |

Decimal values are range checked, never reduced modulo the field. Leading zeros,
signs and numeric JSON are rejected. Hex uses lowercase digits. Native admission
still checks exact types, canonicality, setup and quotas.

Large native values can use `{"file":"data/value.zkcv","sha256":"BYTE_DIGEST"}`.
References are relative to that input document's directory, cannot traverse
symlinks or `..`, and are read through retained regular-file descriptors.
Reference traversal is supported on Unix; other platforms refuse it.
Documents share a 16 MiB and 200,000-node allowance. Use native file references
for data that exceeds the JSON allowance; native capacity limits still apply.

## Packages and policies

For deployment, compile a package and authorize its exact digest independently:

```sh
zkc compile example::Proof --output=proof.zkpkg
zkc inspect --package=proof.zkpkg --sha256=EXPECTED_SHA256
zkc verify --package=proof.zkpkg --sha256=EXPECTED_SHA256 \
  --public=public.json --proof=proof.bin
```

Pinned package mode cannot be mixed with source options or an Entry name.
Rehashing an unknown package does not authorize it. Authored proof jobs require
`--allow-header-only`; derived jobs choose their transcript suite in source.

Use `--service=ROLE.NAME=COUNT`, `--transcript-budget=COUNT` and `--context=HEX`
for invocation settings. Explicit zero budgets remain zero. `--capacity=FILE`
sets [native limits](../spec/runtime/capacity.md); run Entries also accept
`--limits=FILE` for [work limits](../spec/runtime/joint.md).
`prove` accepts services of the selected prover; `verify` accepts services of the
selected verifier. Other roles refuse.
[Retries](attempts.md) require an Entry completion selection and an explicit count.

## Setup authority

`--setups=authority.json` provides independently trusted setup identities:

```json
{"format":"zkc.entry-setups/0","keys":{"main":"EXPECTED_KEY_ID_HEX"}}
```

Supply verifier-key bytes separately with `--key=main=main.vk`. Both material and authority use source slot names; the Host maps them to the
same authenticated native setup labels. Whole verifier-key
ports are initialized by the Host and omitted from input maps. A prover-key input
uses `{"file":"main.pk","fingerprint":"EXPECTED_MATERIAL_ID_HEX"}`. Its
fingerprint identifies imported key material; it is distinct from a file SHA-256.
The key path obeys the same document-relative confinement as other references.
[Setup associations](../spec/language/entries.md#setup-associations) select ports;
[setup authority](../spec/formats/messages.md#application-authorized-setups)
authorizes incoming PCS values. Material does not establish its own authority.

## Reports and Rust applications

Commands print a human-readable summary by default; refusals go to standard
error. Use `--json` for a structured report on standard output, including outcomes,
resource use, stops and publication results. Help and version remain text.
Proof commands report the proof's SHA-256 as well as the package identity.
`--results=FILE` writes readable named values using `zkc.entry-outputs/0`.
[Publication](../spec/runtime/publication.md) defines bounds, protected paths,
per-file replacement and partial publication reports. Failures never trigger
automatic reexecution.
An encoding or staging failure preserves previous files; a later `verify` still
reads the selected existing proof. Check the command outcome and reported digest.

The public `project::{Project, Compiler, Selection}` API resolves source projects
and returns checked interfaces or packages. `Project::layout()` supplies standard
paths. `Compiler::prepare()` returns a `Preparation` of checked interfaces and
`Template` files; the CLI publishes it through the common Host.
`entry::Interface` describes logical
inputs; `BoundInterface` ties that view to a package. `entry::inputs::Decoder`
accepts readable maps, with an optional explicit file resolver. Typed applications
can construct `RoleInputs`, `RunRequest` and `ProofRequest` directly and invoke
`RunEntry` or `ProofEntry`. Their preparation, native execution and authority
checks are shared with the CLI. Both provide `check_inputs` without execution.

The nested `execution` diagnostics and Rust `native` report retain native labels;
logical result maps retain source names.

```sh
zkc bindings --package=proof.zkpkg --sha256=EXPECTED_SHA256 --output=bindings.rs
```

The module pins that package and provides named input/output structures, setup
and service constants, `into_inputs`, `into_role` and `take`. Mathematical leaves
use `entry::Value`; native admission still checks domain, permissions and setup.
Generated Rust identifiers use `__zkc_` plus full UTF-8 byte hex for Unicode,
Rust keywords and source names beginning with that reserved prefix; an allocator
also resolves generated-name collisions. Serialized keys and role constants keep
original source names. The bindings contain no protocol arithmetic or custom interpreter. Regenerate
them when the authorized package changes. The [tools crate](../../crates/zkc-tools/README.md)
owns the API inventory.

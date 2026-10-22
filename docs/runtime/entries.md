# Running source Entries

A protocol defines participant computation and interaction. An `entry fn` exposes
application control; a `proof` declaration configures proving and verification.
Both execute through the common Host and native VM.
A concrete protocol is also directly runnable: `zkc run ProtocolName` uses its
generated Entry with one `inputs` argument, keyed by participant. Inspect or
prepare that name to obtain its schema and input template. A generic protocol is
directly selectable with closed source arguments, for example
`zkc run 'Schnorr<G>'`. Quotes protect the brackets from the shell. Qualify ambiguous
static names, for example `Schnorr<example::G>`; the compiler does not choose a
lexical module or infer static arguments from runtime inputs. Use an `entry fn`
to give a configuration a stable short name or add application logic.

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
directory by default). Both create a minimal Entry function and its argument
template. They refuse an existing project or conflicting source files and preserve
existing regular input files.
Fill `inputs/example.Main/arguments.json`
with `{"value":"7"}`, then run:

```sh
zkc run --dry-run
zkc run
```

Commands discover the nearest `zkc.toml`. Use `--project=FILE` to select another
project, or explicit `--module=NAME=FILE` and `--asset=NAME=FORMAT=FILE` mappings.
`--compiler=PATH` selects a trusted compiler; otherwise the compiler is resolved
from absolute directories in trusted `PATH`. Execution compiles in memory and
reports the resulting package identity. It does not publish an intermediate package.

`--no-simplify`, `--no-finite-bulk`, `--release-storage`,
`--fuse-vector-reductions` and `--fuse-collect-fold` choose
compilation options without skipping source comparison, for `compile` and
commands that compile source before invocation. Both fusion options default to
false. Collect–fold [composition](../spec/ir/kernel.md#collectfold-composition)
streams eligible total collection/reduction pairs. Vector reduction fusion
can replace an eligible multiply-map/sum with shape guards and dot under the
[preparation contract](../spec/ir/protocols.md#optional-vector-reduction-fusion).
Its values and ordered shape refusals agree under sufficient resources, while
resource exhaustion can differ. The package records the choice, including for
proof Entries. Checking source and inspecting input interfaces reject these
executable optimization options; pinned-package invocations use the recorded
choices. Maintained [projects](../../examples/projects/README.md) provide
complete inputs and commands.

`check` checks source without requiring input values. `prepare` checks input
interfaces and creates missing templates for all Entries, or one named Entry.
It preserves existing regular files byte for byte, including stale or unfilled
ones. It does not validate or migrate their contents. After changing a port,
update its input map or remove that file and run `prepare` again. Use `inspect`
for the current schema and add `--dry-run` to `run`, `prove` or `verify` to validate values.

With several Entries, supply a unique short name or `module::Name`:

```sh
zkc prepare example::Proof
# Fill the generated public and witness maps.
zkc prove example::Proof
zkc verify example::Proof
```

Omitted names require one eligible Entry: `run` considers Entry functions;
`prove` and `verify` consider proof Entries. `inspect`, `compile`, `bindings`
consider both kinds. `prepare` without an output override prepares all project Entries;
with `--output` it selects one Entry across both kinds. An explicitly ambiguous short name
requires qualification. A unique Entry of the wrong kind is an error.

### Paths and sessions

| Purpose | Default beside `zkc.toml` | Override |
|---|---|---|
| Proof public inputs | `inputs/<entry-stem>/public.json` | `--public=FILE` |
| Prover witness inputs | `inputs/<entry-stem>/witness.json` | `--witness=FILE` |
| Entry function arguments | `inputs/<entry-stem>/arguments.json` | `--input=FILE` |
| Compiled package | `build/zkc/<entry-stem>.zkpkg` | `--output=FILE` |
| Produced or verified proof | `build/zkc/<entry-stem>.zkproof` | `--output=FILE` / `--proof=FILE` |
| Run output values | `build/zkc/<entry-stem>.results.json` | `--results=FILE` |

For `example::Proof`, the stem is `example.Proof`. Generic runs append a full
selector digest to the qualified protocol stem, as described below. Unicode source
names retain their exact spelling in default filenames. Explicit paths are
relative to the working directory and override only that group or artifact.
Missing or malformed selected files fail; there is no search for alternate files.
Default output directories are created as needed. Prove and verify write named
output values only when `--results` is supplied.
For a run that needs no result file, use `--no-results`; it conflicts with
`--results`. This also allows execution when a returned value has no file codec.

Package and explicit-module modes require explicit input paths and proof paths;
they do not borrow defaults from a nearby project. Joint child invocations receive
fresh sessions by default. Explicit child sessions and policies belong in
`--invocations=FILE`; callers are responsible for explicitly selected freshness.

### Input templates

`prepare` creates only required groups and preserves existing regular files. With
`--output=DIRECTORY`, it prepares one selected Entry in that directory; an omitted
name requires a unique Entry. Package and explicit-module modes require this
output override. Null leaves are unfilled placeholders, except for actual unit
values. Preparation never invents dynamic lengths or chooses variant cases.
Each Entry in the report includes suggested `commands` and additional
`requirements`: an authored proof needs explicit `--allow-authored`, and each
setup slot needs independent `--setups` authority and `--key` material.
Initialization never grants those permissions.

Generic selections are prepared explicitly; `prepare` without a name does not
enumerate possible static arguments. Their default directory and artifact stem
is `<qualified.protocol>-<digest>`, where the full SHA-256 covers the reported
selection name. `prepare` reports exact paths and replayable command argument
arrays. Source argument spelling is preserved apart from whitespace/comments;
using an alias or a different natural expression can produce a different default
path even when the closed computation is identical. Use a named Entry function
when that configuration should have one application-owned path.

`inspect` describes the schema, choices and whether each input has an installed
constructor. Add `--dry-run` to `run`, `prove` or `verify` to check actual inputs,
setup authority and bounds through the same native input validation as execution.
It runs no protocol, issues no resources, reads no proof bytes and publishes no
proof or result values. Verification does not read witness files. Output paths
need not exist; `--output`, `--proof` and `--results` have no effect in this mode.
Compilation reports requested with `--report` are still written. Execution count
instrumentation cannot be combined with `--dry-run`. Successful input validation
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
Entry functions use one `--input=FILE` map keyed by parameter names. Generated
protocol Inputs records contain a nested record per role, for example
`{"inputs":{"P":{"value":"7"},"V":{"value":"7"}}}`. A shared port remains
a separate role-local input. Empty parameter lists need no input file. Project
paths follow the table above; verification never opens a witness map.

| Source value | JSON |
|---|---|
| Field or index | Canonical nonnegative decimal string, such as `"7"` |
| Boolean / unit | `true` or `false` / `null` |
| Tuple, array, vector or indices | Array of element values |
| Record | Object with exact field names |
| Variant | `{"case":"Name","fields":{"0":"7"}}` |
| KoalaBear extension field | Eight ascending coefficient strings, or a base-field decimal string |
| Sparse matrix | `{"rows":"2","columns":"3","entries":[["0","1","7"]]}` |
| Bytes | Array of byte integers from `0` through `255` |
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
`--allow-authored`; derived jobs choose their transcript suite in source.

Direct proof commands use `--service=ROLE.NAME=COUNT`,
`--transcript-budget=COUNT` and `--context=HEX` for invocation settings. Explicit zero budgets remain zero. `--capacity=FILE`
sets [native limits](../spec/runtime/capacity.md); Entry functions also accept
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
`entry::FunctionInterface` describes Entry function signatures; `Interface` and
`BoundInterface` describe native proof/deployment interfaces. `entry::inputs::Decoder`
accepts readable maps, with an optional explicit file resolver. Typed applications
can construct `RoleInputs`, `RunRequest` and `ProofRequest` directly and invoke
`RunEntry` or `ProofEntry`. Their preparation, native execution and authority
checks are shared with the CLI. Both provide `check_inputs` without execution.

Applications making repeated calls can retain immutable input data explicitly:

```rust,ignore
use zkc::execution::{Capacity, InputValue, PreparedData};

let public = PreparedData::from_value(native_value, Capacity::default())?;
// Reuse this handle when constructing each call's named input map.
request.public.insert("values".into(), InputValue::Prepared(public.clone()).into());
let report = entry.prove(request)?;
```

`from_wire(type, bytes, capacity)` imports canonical bytes instead. Preparation
retains decoded data and its encoding; `retained_bytes()` reports that payload
cost. Each call still checks its current limits and input authority and creates
fresh execution resources. Keep private values as `InputValue::Native` when
encoding them would be unnecessary. This process-local API adds no cache files
or implicit CLI reuse.

The nested `execution` diagnostics and Rust `native` report retain native labels;
logical result maps retain source names.

```sh
zkc bindings --package=proof.zkpkg --sha256=EXPECTED_SHA256 --output=bindings.rs
```

For a proof, the module pins that package and provides named input/output structures, setup
and service constants, `into_inputs`, `into_role` and `take`. Mathematical leaves
use `entry::Value`; native admission still checks domain, permissions and setup.
Generated Rust identifiers use `__zkc_` plus full UTF-8 byte hex for Unicode,
Rust keywords and source names beginning with that reserved prefix; an allocator
also resolves generated-name collisions. Serialized keys and role constants keep
original source names. The bindings contain no protocol arithmetic or custom interpreter. Regenerate
them when the authorized package changes. The [SDK crate](../../crates/zkc/README.md)
owns the API inventory.

## Entry Host and SDKs

Entry control and numerical computation have separate owners. The compiled Host
program selects control branches and static calls; numerical functions use the
existing Kernel pipeline and VM. Protocol and proof calls use their native
admission, setup, transcript and cleanup owners. The outer invocation shares
cumulative work and value limits across reached calls. A fresh child does not
reset these allowances. The live allowance includes retained parent data and
native transport; children receive a conservative share of its remainder. A
nested computation can therefore reach the limit before the same standalone
runner. See the [execution contract](../spec/runtime/entries.md#function-execution)
for the partition policy. Calls are ordered, and no retry or result caching is
implicit. Only the successfully returned source root is published.

`--invocations=FILE` can set policies for exact static child deployment IDs shown
by inspection. Ordinary data stays in arguments.json. Child configuration carries
sessions, semantic contexts, service budgets and independently authorized setup
material. Its `inputs` maps supply only the named setup/key ports excluded from
generated ordinary records; inspection exposes their schemas. Context cannot
replace source call operands. Defaults cover children without
setup slots. Required setup authority must be supplied explicitly.

Function packages generate an `Arguments` structure, an admission function pinned
to the package, and a typed `call` wrapper with the source result type:

```rust,ignore
let host = bindings::admit(package_bytes, options, authority)?;
let result = bindings::call(&host, arguments, context)?;
// result.report retains usage, reached calls and failures.
// result.value is present only after successful execution and conversion.
```

Applications may also use `FunctionEntry::prepare(FunctionRequest)` directly.
Authority and context are separate from ordinary arguments. Generated wrappers
check exact package identity before preparation; schema equality alone cannot
select a different deployment.

The [Python SDK](../../python/README.md) calls the installed CLI, which uses this
same Host. It accepts checked JSON-shaped arguments and returns the source value
with its native report. It passes proof bytes unchanged. Each call starts a fresh
process; retaining an admitted Host for repeated calls is available in Rust.

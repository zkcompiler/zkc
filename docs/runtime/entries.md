# Running source Entries

A Protocol defines computation and interaction. A `run` or `proof` Entry selects
one closed invocation. The common Host executes its compiled participant programs.

## Project workflow

Keep reusable protocols in libraries or `protocol.zkc`, concrete Entries in
`main.zkc`, and the explicit module/asset map in `zkc.toml`. The language also
allows protocols and Entries in the same file.

```sh
zkc init my-project
cd my-project
zkc check
zkc inspect
zkc inputs init
```

The scaffold contains an index echo protocol. Fill `inputs/example.Main/P.json`
with `{"value":"7"}`, then run:

```sh
zkc inputs check --operation=run --session=example --input=P=inputs/example.Main/P.json
zkc run --session=example --input=P=inputs/example.Main/P.json --results=results.json
```

Commands discover the nearest `zkc.toml`. Use `--project=FILE` to select another
project, or explicit `--module=NAME=FILE` and `--asset=NAME=FORMAT=FILE` mappings.
`--compiler=PATH` selects a trusted compiler; otherwise the compiler is resolved
from absolute directories in trusted `PATH`. Execution compiles in memory and
reports the resulting package identity. It does not publish an intermediate package.

With several Entries, supply a unique short name or `module::Name`:

```sh
zkc inputs init example::Proof
zkc prove example::Proof --public=inputs/example.Proof/public.json \
  --witness=inputs/example.Proof/witness.json --output=proof.bin
zkc verify example::Proof --public=inputs/example.Proof/public.json --proof=proof.bin
```

Omitted names require one eligible Entry: `run` considers run Entries;
`prove` and `verify` consider proof Entries. `inspect`, `compile`, `bindings`
and `inputs init` consider both kinds. An explicitly ambiguous short name
requires qualification. A unique Entry of the wrong kind is an error.

`inputs init` creates only required files, never overwrites them, and selects
one Entry per call. Null leaves are unfilled placeholders, except for actual
unit values. It does not invent dynamic lengths or choose variant cases.
Its report includes command arguments and additional `requirements`: an authored
proof needs explicit `--allow-header-only`, and each setup slot needs independent
`--setups` authority and `--key` material. Initialization never grants those permissions.
`inspect` describes the schema, choices and whether each input has an installed
constructor. `inputs check --operation=...`
uses the same native preparation as execution, including setup and capacity
checks, but runs no protocol and issues no resources. Successful preparation
is not proof acceptance or a protocol security judgment.

## Input values

Input files are plain maps with exact source port names. Proofs have one public
map and a separate prover witness map. Verification accepts no witness file.
Runs use `--input=ROLE=FILE` for each role with inputs; omitted empty groups are
filled automatically. A shared source port remains a separate role-local input
in a run. Files are always selected explicitly, with no implicit witness lookup.

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
[Retries](attempts.md) require an Entry completion selection and an explicit count.

## Setup authority

`--setups=authority.json` provides independently trusted setup identities:

```json
{"format":"zkc.entry-setups/0","keys":{"main":"EXPECTED_KEY_ID_HEX"}}
```

Supply verifier-key bytes separately with `--key=main=main.vk`. Whole verifier-key
ports are initialized by the Host and omitted from input maps. A prover-key input
uses `{"file":"main.pk","fingerprint":"EXPECTED_MATERIAL_ID_HEX"}`. Its
fingerprint identifies imported key material; it is distinct from a file SHA-256.
The key path obeys the same document-relative confinement as other references.
[Setup associations](../spec/language/entries.md#setup-associations) select ports;
[setup authority](../spec/formats/messages.md#application-authorized-setups)
authorizes incoming PCS values. Material does not establish its own authority.

## Reports and Rust applications

Standard output contains outcomes, resource use, stops and publication results.
`--results=FILE` writes readable named values using `zkc.entry-outputs/0`.
[Publication](../spec/runtime/publication.md) defines bounds, protected paths,
per-file replacement and partial publication reports. Failures never trigger
automatic reexecution.

The public `project::{Project, Compiler, Selection}` API resolves source projects
and returns checked interfaces or packages. `entry::Interface` describes logical
inputs; `BoundInterface` ties that view to a package. `entry::inputs::Decoder`
accepts readable maps, with an optional explicit file resolver. Typed applications
can construct `RoleInputs`, `RunRequest` and `ProofRequest` directly and invoke
`RunEntry` or `ProofEntry`. Their preparation, native execution and authority
checks are shared with the CLI. Both provide `check_inputs` without execution.

```sh
zkc bindings --package=proof.zkpkg --sha256=EXPECTED_SHA256 --output=bindings.rs
```

Bindings pin the package and provide named Rust inputs and outputs. They contain
no protocol algorithm or custom interpreter. Use `is_success` or `into_result`
to check complete execution and acceptance. The [tools crate](../../crates/zkc-tools/README.md)
lists APIs; [Entry contracts](../spec/runtime/entries.md) specify exact behavior.

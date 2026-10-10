# Running source Entries

A Protocol defines computation and interaction; an Entry selects a closed run
or proof job. The common Host executes its compiled participant programs.
Applications supply actual values, trusted package/setup identities and limits.
[Entry contracts](../spec/runtime/entries.md) own exact admission and call rules.

## Compile and invoke

After [building the tools](../development/README.md), compile a trusted source
tree with explicit module paths:

```sh
zkc compile example::Proof --module=example=protocol.zkc --output=proof.zkpkg
zkc inspect proof.zkpkg EXPECTED_SHA256
zkc prove proof.zkpkg EXPECTED_SHA256 prover.json proof.bin
zkc verify proof.zkpkg EXPECTED_SHA256 verifier.json proof.bin
```

Store the compilation report's `package_sha256` in trusted deployment
configuration. `EXPECTED_SHA256` comes from that configuration; rehashing an
unknown received package does not authorize it. Authored proof jobs require
`--allow-header-only`. Derived jobs select their suite in source.

`inspect` authenticates the package and reports its checked source interface:
roles, named ports, services, setup names and proof selections. It does not
execute a protocol or establish native admission or protocol security.

Run Entries use:

```sh
zkc run run.zkpkg EXPECTED_SHA256 inputs.json --results=results.json
```

Use `--project=zkc.toml` for an explicit [project map](../language/README.md#project-inputs),
or repeat `--module=NAME=FILE` and `--asset=NAME=FORMAT=FILE` to capture dependencies.
`--compiler=PATH` selects a trusted compiler; otherwise it resolves from absolute
directories in trusted `PATH`. `--no-simplify` and `--release-storage` choose
compilation options without skipping source comparison. Maintained
[projects](../../examples/projects/README.md) provide complete inputs and commands.

## Source names and native labels

Entry requests and logical outputs use the original NFC source names, including
Unicode participants, ports, fields, alternatives and setup slots. They do not
silently normalize names. Raw UTF-8 and valid equivalent JSON escapes identify
the same decoded name. Use the names reported by `inspect`.

The authenticated interface maps those names by declaration order to native
`role00000000`, `setup00000000` and `case00000000` labels (eight lowercase hex
digits, starting at zero). This applies to ASCII source too. Direct Runner/PIR
APIs and `run-bundle`, `prove-bundle` and `verify-bundle` use the native artifact's
labels; `run`, `prove` and `verify` perform the source-name conversion. Applications
cannot supply an alternative renaming table.

## Named inputs

A run request names every participant, including those without inputs:

```json
{
  "format": "zkc.entry-run/0",
  "session": "example_run",
  "roles": {
    "P": {"inputs": {"done": true}},
    "V": {"inputs": {}}
  }
}
```

A proof request supplies public values once and only the invoked participant's
private inputs:

```json
{
  "format": "zkc.entry-proof/0",
  "public": {},
  "inputs": {"done": true},
  "context": ""
}
```

The [attempt fixture](../../compiler/test/fixtures/language/attempts.zkc) accepts this
producer request; its verifier omits `inputs`. Values follow the checked source
schema: ordinary JSON for Booleans, indices and containers; canonical framed hex
for mathematical leaves. A raw scalar integer is not a native frame. The
[file-adapter contract](../spec/runtime/entries.md#file-adapters-and-rust-bindings)
defines exact objects, variants and unknown-field handling.

Optional `services` and `transcript_budget` override the
[operational defaults](../spec/runtime/entries.md#attempts-and-operational-defaults).
Explicit zero remains zero. `--capacity=FILE` selects [capacity limits](../spec/runtime/capacity.md).
Run Entries also accept `--limits=FILE` for the `zkc.bundle-limits/0`
[work limits](../spec/runtime/joint.md).
[Retries](attempts.md) require an Entry completion selection and explicit count.

## Setup material and authority

`--setups=authority.json` supplies independent expected key identities:

```json
{"format":"zkc.entry-setups/0","keys":{"main":"EXPECTED_KEY_ID_HEX"}}
```

The request's `setups` map supplies canonical verifier-key bytes for those slots.
Both this material map and the authority file use source slot names. The Entry
Host translates both to the same authenticated native setup labels.
Omit verifier-key input ports: the Host initializes them through checked Entry
associations. Prover-key inputs use a pinned file or Rust `ProverMaterial`.
File paths resolve from the invoking process's working directory.

[Setup associations](../spec/language/entries.md#setup-associations) select
inputs. [Setup authority](../spec/formats/messages.md#application-authorized-setups)
governs incoming PCS values and terminal checks. A package or supplied key file
does not establish trust in its own setup.

## Reports and publication

Standard output reports outcome, resource usage, stops, cleanup and publication.
It omits application values and proof payloads. `--results=FILE` writes named
logical results using `zkc.entry-outputs/0`; non-Wire private values cannot be
serialized. [Publication](../spec/runtime/publication.md) defines file limits,
path admission, staging, per-file replacement and partial publication reports.
A publication failure never triggers automatic reexecution.
The nested `execution` diagnostic retains native report labels, including
ordinal participants; logical result maps retain source names. The Rust report's
`native` member follows the same native-report contract.

## Rust applications

Use `entry::RunEntry` or `entry::ProofEntry` in `zkc-tools`. An admitted immutable
handle prepares independent calls. `RoleInputs`, `RunRequest` and `ProofRequest`
carry values, services and context. Public proof values appear only in `public`;
`private` contains the invoked participant's nonpublic inputs and service budgets.

Use `is_success` or `into_result` to inspect complete execution, acceptance where
applicable, decoded outputs and cleanup. Preparation errors are `EntryError`;
its [phase and code](../spec/runtime/entries.md#error-phases) identify the
failed boundary. Reports retain execution failures and cleanup details.

Generate optional data bindings from a trusted package:

```sh
zkc bindings proof.zkpkg EXPECTED_SHA256 bindings.rs
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

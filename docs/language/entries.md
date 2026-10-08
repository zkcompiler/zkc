# Running source Entries

A `.zkc` Protocol defines the computation and interaction. Its Entry selects a
closed run or proof job. The common Host executes its compiled participant
programs. Applications supply actual inputs, trusted package/setup identities and
operational limits.

## Compile and invoke

Compile a trusted source tree with the installed compiler:

```sh
zkc compile --entry=example::Proof --module=example=protocol.zkc --output=proof.entry
```

The JSON result contains `package_sha256`. Store it in trusted deployment
configuration. Then use separate proof processes:

```sh
zkc prove proof.entry EXPECTED_SHA256 prover.json proof.bin
zkc verify proof.entry EXPECTED_SHA256 verifier.json proof.bin
```

`EXPECTED_SHA256` is the value authorized by that configuration. Computing a new
hash of an incoming package does not authorize it. An authored proof job requires
`--allow-header-only`; derived jobs use their Entry's explicit transcript suite.

For a run Entry, use:

```sh
zkc run-entry run.entry EXPECTED_SHA256 inputs.json --results=results.json
```

Compilation accepts repeated `--module=NAME=FILE` and
`--asset=NAME=FORMAT=FILE` selections. `--compiler=PATH` selects the trusted compiler; the default resolves `zkc-compile`
from absolute directories in the caller's trusted `PATH`. The build report records its absolute path and
toolchain identity. Compiler and runtime may be installed separately.
`--no-simplify` and `--release-storage` select compilation options. The compiler
still checks source correspondence before publishing the package.

Failed compilations retain up to 64 KiB of diagnostics and report truncation.
The child deadline and stdout/stderr capture ceilings remain bounded.

## Named inputs

A run request names every participant, including those with no inputs:

```json
{
  "format": "zkc.entry-run/1",
  "session": "example_run",
  "roles": {
    "P": {"inputs": {"done": true}},
    "V": {"inputs": {}}
  }
}
```

Proof requests supply the independently authorized public values and only the
invoked participant's private inputs:

```json
{
  "format": "zkc.entry-proof/1",
  "public": {},
  "inputs": {"done": true},
  "context": ""
}
```

The [attempt fixture](../../compiler/test/fixtures/language/attempts.zkc) accepts
this producer request. Its verifier omits `inputs`. This small
fixture exercises the Host boundary; it is not a cryptographic security example.

Values follow the checked source schema:

| Source value | JSON |
|---|---|
| Boolean, index | Boolean, unsigned 64-bit integer |
| Unit | `null` |
| Tuple, fixed array | Array in source order |
| Record | Object with exact field names |
| Variant | `{"case":"Name","fields":{…}}`; positional payload fields use `"0"`, `"1"`, … |
| Associated representation | Its wrapped representation |
| Field, group, installed data leaf | Hex of the complete canonical native wire frame |

A wire frame includes its installed codec framing. A scalar's raw integer bytes
alone are not a frame. Rust applications can supply immutable native values
through the same Host instead of encoding them. Unknown or duplicated fields,
wrong shapes and unsupported ingress refuse.

Omitted service budgets use the documented operational allowance. Override them
with `"services": {"coins": 100}` inside a run participant record or at the top level of a proof request. A proof
request may set `"transcript_budget": 100`; explicit zero is preserved. Retries
require `zkc prove … --attempts=COUNT` and an Entry completion selection. One-shot
proving also withholds a proof marked incomplete.

`--capacity=FILE` selects the shared [native capacity](../compiler/mathematical-composition.md#application-capacity)
limits. It does not change the proof's mathematical identity. The CLI uses default
joint dispatch, total wire and external-work allowances; Rust applications can
lower these further through `HostLimits` or `ProofOptions`.

## Setup material and authority

Use `--setups=authority.json` with independent expected key identities:

```json
{"format":"zkc.entry-setups/1","keys":{"main":"EXPECTED_KEY_ID_HEX"}}
```

The request's optional `"setups"` object maps the same slot names to canonical
verifier-key bytes in hex. Omit verifier-key input ports: the Host initializes
them through the checked associations. A prover-key input uses
`{"path":"prover.key","sha256":"EXPECTED_MATERIAL_SHA256"}`. Paths resolve from
the invoking process's working directory. Key files are bounded regular files,
authenticated before use. The package and supplied material confer no setup trust.

## Reports and returned values

Standard output contains a structured status report. It retains resource usage,
attempt decisions, stops, cleanup and publication state. It omits returned values
and proof payloads. Exit status is zero only when the requested operation finishes.

Use `--results=FILE` to publish returned logical values. Run files contain a
`roles` map; proof files contain `values` for the invoked participant. Both use
`zkc.entry-outputs/1`. Encoding honors admitted native capacity and a 16 MiB whole
file limit. Non-Wire private results cannot be serialized.

Input and authority paths name bounded regular files; unconnected streams refuse.
Output paths must differ from each other and all input/configuration paths,
including referenced prover-key files. Each file is replaced atomically after
successful execution and cleanup. The proof is published before optional result
encoding and publication. If either result step fails, the report
retains `proof_published: true` and the execution observations. Publication errors
never cause an automatic rerun.

## Rust applications

The common API is `entry::RunEntry` or `entry::ProofEntry` in `zkc-tools`. An
immutable admitted handle can prepare independent calls. `RoleInputs`,
`RunRequest` and `ProofRequest` hold invocation data; reports keep outcomes and
cleanup even when no complete result exists. `RunReport::is_success` requires
completed execution, successful cleanup and decoded outputs; `into_result` keeps
the complete report on either branch. Interactive completion alone does not
establish a protocol's acceptance predicate. For verification,
`ProofReport::is_success` requires the selected acceptance result; for proving,
it requires a complete proof and returned outputs. Both retain cleanup failures.

Calls that fail before execution return `EntryError`, whose `phase` identifies
package authentication, interface reading, setup authority, native admission,
interface binding, request conversion or native preparation. `code()` retains the underlying diagnostic.
Execution failures and cleanup remain in the report.

Generate optional convenience bindings from a trusted package:

```sh
zkc bindings proof.entry EXPECTED_SHA256 bindings.rs
```

The generated module pins that exact package in its `admit` helper. It provides
named input/output structures for each participant and public proof inputs.
Booleans, indices, units, arrays and nominal structures have Rust data shapes.
Mathematical leaves use `entry::Value`; native admission still checks their exact
domain, permissions and setup. Conversions preserve source field and variant
names. Rust field/variant spellings preserve source names; special path names
and names beginning `__zkc_` use an injective hexadecimal escape. Generated
attributes permit source naming conventions without suppressing other warnings.
Input structures provide `into_inputs` and `into_role`; output structures provide
`take`. Role, setup and service constants avoid handwritten source-name strings.

Bindings construct and decode common Host values. They contain no protocol
arithmetic, custom interpreter or alternate authority rules. Supply service
budgets, setup material and context through the common request structures, then
call `prepare`, `prove`, `prove_attempts` or `verify`. A Rust `ProofRequest` carries
public values once in `public` and only the invoked
participant's nonpublic inputs and service budgets in `private`. Both the SDK
and CLI assemble shared role operands from the public map; repeated public names
in private inputs refuse. Native admission independently checks the assembled
values against the artifact. Regenerate bindings when the authorized package changes.

The [source profile](../spec/profiles/source/mathematical-language.md#named-run-calls)
owns exact admission semantics. Native Lean correspondence and remaining older
consumer migration are separate obligations in the [roadmap](../roadmap.md).

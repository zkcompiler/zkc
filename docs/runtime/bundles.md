# Run mathematical IR

`zkc run-bundle` executes a compiler-produced joint bundle with the same role
interpreter used by proof hosts. It needs the compiler and Rust tools; this route
does not call Lean. The [bundle specification](../spec/profiles/compiler/run.md)
defines its authority, input formats, limits and reports.

## A complete example

After [building the tools](../development/README.md), run from the repository root:

<!-- executable: native-bundle -->
```sh
work_dir=$(mktemp -d)
compiler="${ZKC_COMPILER_BIN:-build/compiler}/zkc-compile"
native="${ZKC_NATIVE_BIN:-${CARGO_TARGET_DIR:-target}/release}/zkc"
cat > "$work_dir/message.mlir" <<'IR'
module {
  "protocol.module"() ({
    "protocol.func"() ({
    ^entry(%value: i1):
      %received = protocol.exchange %value {sender="Alice", receiver="Bob", site="message"} : i1
      "protocol.return"(%received) : (i1) -> ()
    }) {sym_name="main", function_type=(i1) -> i1, roles=["Alice", "Bob"],
        input_roles=[["Alice"]], output_roles=[["Bob"]]} : () -> ()
  }) {profile=#protocol.profile<protocol>} : () -> ()
}
IR
"$compiler" protocol-bundle "$work_dir/message.mlir" > "$work_dir/message.bundle"
# This pin comes from our own trusted compilation. Store it with the artifact.
pin=$(sha256sum "$work_dir/message.bundle" | cut -d ' ' -f 1)
cat > "$work_dir/inputs.json" <<'JSON'
["zkc.bundle-inputs/1", "example-session",
 [["Alice", [["0", "bool@native.bool/1", ["wire", "5a4b4356010500"]]], []],
  ["Bob", [], []]], []]
JSON
"$native" run-bundle "$work_dir/message.bundle" "$pin" "$work_dir/inputs.json"
```

The result is `status: executed`, `outcome: ["completed"]`, and Bob returns the
same false Boolean wire value. Exit zero means completed execution, not verifier
acceptance. The report's `acceptance` is null. Programs define their own result
interfaces; applications select the intended decision explicitly.

The `layout` field describes each role's ordered inputs, services and outputs.
Configuration uses these positions and full physical types, never generated SSA
names. A malformed input refusal after artifact admission includes that layout.
Resource/service budgets, session names and key-file paths are host configuration:
applications must authorize them before passing an invocation to this API. It is
not a sandbox for arbitrary client-chosen filesystem paths. The digest must come
from trusted compilation/distribution, not from rehashing an unknown received file.

## Programmatic use

```rust,ignore
use zkc_tools::run::{HostLimits, RunHost, SetupAuthority};

let host = RunHost::admit(&bundle_bytes, &authorized_digest,
                         HostLimits::default(), SetupAuthority::default())?;
let plan = host.prepare(&invocation_bytes)?;
let report = plan.execute();
let record = report.json();
```

Preparation captures key files and validates every role before issuing execution
resources. Each plan executes once; the admitted host can prepare another call.
The caller keeps any returned resource-unit custody in the report's backends and
outputs. Created units returned by a completed role remain valid even if another
role later stops. Issued RNG/nonce roots and managed services are retired by this
host. Private outputs are diagnostic kinds in JSON, never portable capabilities.

`HostLimits` separates structural admission, native value/kernel capacity,
per-role external work and joint dispatch/wire limits. The CLI accepts
`--capacity=FILE` and `--limits=FILE`; see their exact formats in the specification.
Reports preserve the effective limits, reached prefix, failed-load usage, cleanup
and output diagnostics. A setup or diagnostic failure cannot erase earlier effects.

Preparation uses the shared host input diagnostics: `artifact-byte-limit` and
`artifact-json*` bound ingress, while `artifact-input-count-limit`,
`artifact-input-bytes-limit` and `artifact-input-work-limit` bound loading and
entry occurrences. These stable error strings also serve other hosts; their
prefixes do not identify an artifact-specific execution path.

## Independent proofs

For noninteractive execution, use the compiler's selected transcript construction
and the separate `produce-native-proof` and `validate-native-proof` processes,
described in [native proof deployments](../compiler/native-proofs.md). A joint
bundle is an interactive scheduling artifact, not the proof format. The installed
joint host currently refuses transcript-typed entry inputs because it has no
application-authenticated transcript-root configuration.

Named source applications use the [Entry Host](../language/entries.md), which
binds its source interface to these same execution and proof boundaries.

## Separate producer and validator

This minimal example returns a received Boolean as the selected validator decision.
It exercises deployment and proof framing; it does not establish a cryptographic
statement. Real protocols author their equations and guards in the same IR.
The empty suite selects transcript-free execution under policy `/4`.

<!-- executable: native-proof -->
```sh
work_dir=$(mktemp -d)
compiler="${ZKC_COMPILER_BIN:-build/compiler}/zkc-compile"
native="${ZKC_NATIVE_BIN:-${CARGO_TARGET_DIR:-target}/release}/zkc"
cat > "$work_dir/message.mlir" <<'IR'
module { "protocol.module"() ({
  "protocol.func"() ({
  ^entry(%value: i1):
    %received = protocol.exchange %value {sender="P", receiver="V", site="message"} : i1
    "protocol.return"(%received) : (i1) -> ()
  }) {sym_name="main", function_type=(i1) -> i1, roles=["P", "V"],
      input_roles=[["P"]], output_roles=[["V"]]} : () -> ()
}) {profile=#protocol.profile<protocol>} : () -> () }
IR
cat > "$work_dir/policy.json" <<'JSON'
["zkc.native-proof-policy/4", "main", "P", "V", "0", "", "", [], []]
JSON
"$compiler" protocol-proof "$work_dir/message.mlir" "$work_dir/policy.json" > "$work_dir/deployment.json"
# Authorize these exact bytes from our own trusted compilation.
pin=$(sha256sum "$work_dir/deployment.json" | cut -d ' ' -f 1)
cat > "$work_dir/producer-inputs.json" <<'JSON'
["zkc.native-proof-inputs/1", [], [["0", ["wire", "5a4b4356010501"]]], "", [], "0"]
JSON
cat > "$work_dir/validator-inputs.json" <<'JSON'
["zkc.native-proof-inputs/1", [], [], "", [], "0"]
JSON
"$native" produce-native-proof "$work_dir/deployment.json" "$pin" "$work_dir/producer-inputs.json" "$work_dir/proof.bin" > "$work_dir/producer.json"
"$native" validate-native-proof "$work_dir/deployment.json" "$pin" "$work_dir/validator-inputs.json" "$work_dir/proof.bin" > "$work_dir/validator.json"
cat "$work_dir/validator.json"
printf 'Proof files: %s\n' "$work_dir"
```

The producer reports `produced`; the separate validator reports `accepted`.
The validator receives no private producer inputs. Its trusted deployment pin
selects both the program and the policy, including which output is the decision.
The [proof guide](../compiler/native-proofs.md) explains transcript construction,
public bindings, repeated attempts and setup authority for larger protocols.

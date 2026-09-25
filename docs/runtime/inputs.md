# Running generic protocols locally

The development host accepts the original `zkc.library/1` source, actual compiled
participants and a `zkc.run/2` input file. Lean checks the source and candidate
together. The host uses the checked source port and local-call maps; configuration
does not depend on compiler-generated function or SSA names.

This is the `run-protocol` development host. Artifact producers and validators
use `zkc.artifact-inputs/1`, defined in the
[artifact format](../compiler/artifact-format.md#canonical-logical-encoding).
Those inputs belong to a different execution route.

For the two-opening example, with `COMPILER` naming a fresh `zkc-compile` build:

```sh
"$COMPILER" protocol-source tests/fixtures/generic-openings.pir > /tmp/openings-source.json
"$COMPILER" protocol-compile tests/fixtures/generic-openings.pir > /tmp/openings-participants.json
cargo run --locked -p zkc-tools --bin zkc -- run-protocol \
  /tmp/openings-source.json /tmp/openings-participants.json \
  tests/fixtures/generic-openings.inputs.json \
  formal/.lake/build/bin/interactive-protocol
```

The [source](../../tests/fixtures/generic-openings.pir) uses shared
generic proving and checking functions for two dynamic setup/rank instances.
The [input file](../../tests/fixtures/generic-openings.inputs.json)
selects those instances explicitly. Its shape is documented below.

## Input format

```text
["zkc.run/2", entry, session,
  [[setup_name, "development", rank], ...],
  [[role, services, source_inputs, port_constraints], ...],
  [[instance, receiver, message_site, setup_name], ...]]
```

Integers use canonical decimal strings. A key service is
`["prover_key"|"verifier_key", handle_name, setup_name]`. RNG and nonce services
use `["rng"|"nonce", handle_name, budget, "entry"|"session"]`; the host issues
them using OS randomness. Inputs retain the existing tagged values, including
`["host", handle_name]`, fields, tables, points, booleans and canonical public wire
bytes. An explicitly bound Boolean or arithmetic-only protocol can use no setups.
Transcript-resource issuance is not yet exposed by this host command.

A port constraint is `[source_port, arity_or_null, setup_name_or_null]`. At least
one constraint must be present in each record. The host resolves the original
port through the checked map, then the backend checks the actual value. Constraints
are optional for ordinary inputs. A serialized commitment/proof input needs its
own expected setup even when the registry contains only one key. A registry
authorizes material; it does not determine which setup each input is meant to use.

Every statically reachable commitment/proof receive needs one setup selection.
Unknown, repeated and missing sites are refused before execution. The receiving
policy uses the receiver's checked envelope and full type, then checks bytes
against that selected key. It never tries other keys to find one matching a
payload header. Other public values use their admitted logical type and storage
representation. Both table layouts have the same logical wire encoding.

Selections apply to all dynamic visits to the named instance/role/site, including
loop iterations and repeated subprotocol calls. Static coverage includes zero-trip
loop bodies. Applications needing a different setup on each dynamic visit can
install a `MessageDecoder` that uses the complete checked origin; this finite host
configuration does not express that policy. The transport remains separate from
the receiving policy. Driver cancellation releases active frames while preserving
completed capability transitions.

Results retain the existing `outcome` and `cancelled_roles` fields and add
structured `stop` and `cancellations` records. Each includes the full dynamic
origin, role, site, stop kind/detail and collected cleanup errors. This preserves
which call or iteration failed, including when peers are cancelled by the driver.

The host limits setup count and aggregate `n * 2^n` setup work before generating
keys. These are development setups, without ceremony provenance. Public-input
agreement is `LocalOnly`; successful execution is not a protocol soundness claim.
Only `zkc.run/2` is admitted; there is no older-version compatibility decoder.
The host constructs per-role `zkc.inputs/1` payloads for the
[backend input contract](../../crates/zkc-backends/README.md), using the checked
source and the setup/service selections above. Authors supply the outer run
carrier rather than composing those backend payloads themselves.

The native/Lean/CLI tests cover different-rank and equal-rank setups, original
port mapping, received-key mismatch, missing policy, nested calls and loops,
zero-trip coverage, consumed randomness on rejection and cleanup. Those host tests establish structural checking plus native execution.
The separate [original-source reference](../compiler/library-design/validation.md#executable-source-reference)
supplies bounded differential evidence for mathematical and stateful services,
including multiple setups. It does not establish general scheduler or allocator
equivalence.

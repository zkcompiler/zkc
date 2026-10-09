# Proof execution

Producer and validator execute separate participant programs through the shared
Runner. A validator needs its authorized public context and final proof; it
does not need a running producer or the witness. The
[proof contract](../spec/runtime/proofs.md) owns completion, failure and result
rules; [deployment and transport](../spec/formats/proof.md) own exact formats.

## Application interface

Source applications use `entry::ProofEntry` with named values. The
[Entry guide](entries.md) covers commands and optional generated Rust bindings.
Lower-level applications use `zkc_tools::proof::NativeDeployment`; the
[bundle walkthrough](bundles.md#separate-producer-and-validator) is executable.

`NativeDeployment::admit` takes an independently trusted 32-byte SHA-256 pin and
setup authority. CLI adapters parse hexadecimal spelling. The Host hashes and
parses one captured buffer: internal hashes do not authorize an unknown
artifact. Admission checks structure and installation; source correspondence
comes from trusted checked compilation.

`execute(&ProofInputs, Invocation)` accepts immutable data and explicit
provider/key declarations. `Invocation` selects `Prove`, `Verify(&proof)` or
`Attempts(&policy)`. `ProofInputs::decode` adapts positional records to the same
typed inputs. Shared `InputValue`, `Capacity` and `ProverMaterial` live in
`zkc_tools::execution`.
Public values are canonically bound; private values can avoid a wire roundtrip.
Reusable `ProverMaterial` shares immutable material across calls while each
invocation retains its own setup admission, quotas, RNG and live resources.

## Setup and input preparation

Applications authorize setup identities independently of packages and supplied
key material. Entry input associations select expected setups; the Host registry
authorizes incoming PCS metadata. The protocol's explicit `pcs.check` operand
enforces the terminal's expected key and arity. An incoming value may be decoded
and observed before that check rejects it. An unchecked returned PCS value need
not belong to a specific output setup. The
[setup contract](../spec/formats/messages.md#application-authorized-setups)
is the authoritative boundary.

Every mapped input is admitted, including unused ports and inactive alternatives.
Data, entry and transcript-root capacities are checked before execution entropy;
capability retention is reserved before issuance. Loading and execution have
separate [capacity ledgers](../spec/runtime/capacity.md). A stopped initializer
does not open a proof reader or writer.

## Execution and results

Derived construction uses explicit affine transcript state. Authored execution
uses the program's own calls and binds context only as declared; CLI use requires
`--allow-header-only`. [Construction](../compiler/construction.md) explains
this distinction.

A validator succeeds only after its actual selected Boolean is true, normal
return, complete proof consumption and successful cleanup. A completed producer
can still have emitted an invalid or incomplete proof. Header agreement alone
does not cryptographically bind an authored proof's body to its context.

Reports preserve primary failure, cleanup errors, stop coordinates and resource
usage. Successful copyable original results are returned by original port index;
private state successors stay within Host custody. The Entry layer decodes named
logical results. An outer `Ok` establishes preparation, so use
`ProofReport::is_success` or `into_result` to inspect the complete outcome.

CLI diagnostics omit application values and proof payloads. Requested outputs
follow [file publication](../spec/runtime/publication.md); a publication failure
does not trigger a rerun. [Attempts](attempts.md) separately authorize retries
while retaining consumed provider state and work.

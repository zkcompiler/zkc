# Runtime design

`zkc-runtime` provides one Runner for the closed `zkc.program/0` executable.
It advances local computation and exposes communication/service cuts. Installed
backends execute admitted operations with their exact type, effect, resource and
representation contracts. Whole protocols remain visible in the program.

## Host responsibilities

| Host | Boundary |
|---|---|
| Entry | Authenticated `zkc.entry/0` publication, named source interface and selected run/proof job |
| Proof | Authenticated native deployment, explicit public context, independent producer and validator execution |
| Joint | Authenticated `zkc.run/0` bundle, role layouts and checked dispatch of actual messages |

In `zkc-tools`, `entry` delegates to the public `proof` and `run` modules;
`host` owns shared input preparation, capacity, setup and I/O support. Entry
execution uses the same Runner through those Hosts. Compiler publication binds the original/interface to the
artifact; Rust authenticates that publication and independently admits the
executable. Retaining MLIR in a package does not mean Rust interprets it.

The application supplies an authorized digest and setup authority. Rehashing an
untrusted artifact supplies an identifier, not authorization. [Identity](artifact-identity.md)
defines the distinct package, deployment and invocation boundaries.

## Preparation and execution

Preparation reads bounded inputs, validates layouts and setup associations, and
captures immutable material before issuing runtime capabilities. Reusable prover
material shares immutable bytes; invocation-local RNG, transcript state and
resource leases remain separate. Runtime service aliases preserve their declared
shared state and failure behavior.

Each participant executes its actual receives. A joint Host schedules those
runners using the bundle; an independent validator consumes proof frames and its
public inputs. The validator's selected Boolean decision determines acceptance.
Proof production or completed joint execution alone does not mean acceptance.

Admission, value capacity, external work and dispatch/wire limits are distinct.
Exhaustion is reported at the boundary it reaches. Cleanup and report publication
cannot erase earlier effects, consumed work or a stopped prefix. Copyable results
publish only according to the Host's completion and cleanup rules; resource
handles are never serialized into portable authority.

[Attempts](attempts.md) retain provider state and accumulated
work across explicitly authorized retries. [Conditional completion](../compiler/control.md)
retains the reached prefix and skips the unreached suffix. Neither permits
replaying consumed affine capabilities.

## Contracts and assurance

The native proof contract covers every admitted program shape.
[Entry inputs](entries.md) and the Host registry authorize setups;
an explicit verifier-key-consuming PCS check enforces the expected terminal key.
The [setup contract](../spec/formats/messages.md#application-authorized-setups)
distinguishes input pins, authorized receives, observation timing and unchecked
returned PCS data.

Compiler checks, structural admission, installed kernel contracts and runtime
tests cover distinct trust boundaries. Native Lean correspondence is open. The
independent formal realization laws state how complete results and states would
have to relate; they do not supply a correctness theorem for this Runner.

## Realization evidence

The [representation laws](../spec/realization/representations.md) relate
complete results, values at actual states, capacities, progress and custody.
Native controls exercise actual parsers, lowering and execution: changed
captures, wrong domains, same-typed swaps, omitted guards, failed writes,
exhausted providers, remaining-byte differences and stale aliases. Compare
the actual reached prefix and residual state, including failures.

Constant-time MSM and diagonal contraction kernels retain their explicit
[physical selection](../compiler/representation.md#checked-physical-decisions).
Selection does not infer public-input authority or prove a protocol leakage law.

# Proof attempts

An application can repeat an admitted producer Entry under a bounded policy.
The selected Boolean result requests retry when false and completion when true.
The Host retains actual RNG successors and service state, starts a fresh
transcript for each attempt, and publishes only the completed result after
cleanup. The [attempt contract](../spec/runtime/attempts.md) owns all lifecycle,
policy, budget and report rules.

## Source Entries

Select a completion result in the Entry declaration, then request a bounded count:

```sh
zkc prove proof.zkpkg EXPECTED_SHA256 prover.json proof.bin --attempts=3
zkc verify proof.zkpkg EXPECTED_SHA256 verifier.json proof.bin
```

Source Entries use persistent managed providers. They expose no affine RNG input
constructors, so their native policy has no RNG input/successor pairs. Rust
applications use `ProofEntry::prove_attempts`. One-shot proving also withholds a
proof marked incomplete. Service budgets, public values, setups and
[capacity](../spec/runtime/capacity.md) remain ordinary invocation inputs.

## Native deployments

Lower-level callers use `NativeDeployment::execute(&inputs, Invocation::Attempts(&policy))`. They authorize an explicit completion port and RNG map:

```sh
zkc prove-bundle deployment.json TRUSTED_SHA256 producer.json proof.bin --attempt-policy=attempts.json
zkc verify-bundle deployment.json TRUSTED_SHA256 validator.json proof.bin
```

The application authenticates the policy and deployment separately. A recorded
policy digest identifies that policy; it does not bind retries into the proof
or prove that a remote producer used it. Validators receive the final proof,
without failed attempts or private provider state.

## Failure and progress

Only an ordinary returned retry decision continues. A zero inverse, malformed
successor, exhausted provider, write-limit failure or cleanup error stays fatal.
Recovery belongs in authored control before a fatal operation. Early abandonment
uses [participant completion](../compiler/control.md#participant-completion).

No-progress retries consume the attempt allowance. Attempt indices add no
cryptographic bytes; changing entropy affects messages and therefore challenges.
The Host supplies no freshness test, probability bound or cryptographic security
claim. Reports retain each decision and reached stop, persistent-root state and
cumulative work. Load-time refusals have no execution coordinates.

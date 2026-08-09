# zkc

zkc is a research compiler for zero-knowledge **protocols**: the layer above
relations, circuits, AIRs, and other arithmetized statements. It turns an
already formed protocol into a content-identified object that can be checked,
projected to verifier and prover endpoints, executed, and analyzed through
explicit conditional security rules.

> **Current status:** active research snapshot. This repository is
> not a production release or a claim of general backend conformance.
> [Current Status](docs/status.md) is the public coverage and evidence
> dashboard for this snapshot.

## The compiler boundary

The input to zkc is Protocol IR (PIR; MLIR dialect `pir`), a carrier for two
connected structures:

- a totally ordered transcript spine of messages, absorbs, challenges, and
  checks; and
- a linear claim-flow graph whose reductions and terminal discharges are
  authorized by content-addressed contracts.

`zkc-seal` checks the protocol fail closed: well-formedness, claim linearity,
structural Fiat-Shamir admissibility, projection-obligation coverage, exact
reduction closure, and typed terminal closure. A successful seal receives a
content-derived PIR identity. Projection then derives Operator IR (OIR)
endpoint programs from that sealed protocol; endpoint programs are not
independent protocol definitions.

Relation compilation remains upstream. zkc currently exercises an opaque
`r1cs` anchor profile while relation tooling retains authority over payload
interpretation, witness production, and satisfaction.

## What runs today

The current snapshot implements and exercises:

- PIR sealing and canonical identity, persisted artifact
  decode/admission, endpoint projection, route-preserving linking, and
  fail-closed registry resolution;
- OIR verifier execution and derived prover-skeleton execution;
- typed, opaque prover witness handles and selected native providers for
  bounded prover operations;
- a C++ implementation and an independently written Python reference twin
  with byte-parity checks at the identity, encoding, and vector boundaries;
- a Soundness Kernel that evaluates explicit derivation plans under typed,
  content-addressed rules and returns conditional, notion-indexed judgments;
- attributed formalization receipts or surveyed absences for each security
  rule, plus a separate pinned ArkLib declaration-drift check; these annotations
  do not participate in derivability or prove correspondence to PIR;
- a separate completeness track with its own judgments and receipts; a
  completeness result is never treated as a soundness result, and an accepting
  run is evidence beside a judgment rather than a proof of that judgment; and
- a general in-process checked-search Compiler Core, currently exercised by a
  bounded same-point KZG batching provider over admitted PIR.

One pinned Plonky3/FRI-shaped path crosses a bounded connected execution path.
zkc seals the protocol and derives both endpoints; the external runner reads
the prover skeleton's declared schedule, matches it entry-for-entry against
the pinned challenger's own event log, and runs the pinned prover — it does
not dispatch the skeleton's holes individually, since `pcs.open` is their
composition upstream; the pinned PCS verifier accepts the resulting opening
proof; zkc's verifier executor accepts the adapter-assembled wire under its
native Plonky3 profile with an independently derived, entry-for-entry equal
challenge stream; and corrupted controls reject.
This is evidence for one fixture, one revision, and one named adapter boundary.
It is not universal Plonky3 conformance, a proof of protocol soundness, or a
generic backend implementation.

The protocol-coverage and architecture-progress matrices are in
[Current Status](docs/status.md).

## Scope

This snapshot focuses on protocol-semantic compilation. Relation compilation
remains upstream; generalized realization, composition, broader judgment
tracks, and deployment are target layers described in the Architecture and
Roadmap.

## Current formats

- Protocol artifact: the canonical encoding / PIR
- Endpoint artifact: OIR
- Protocol vocabulary: `zkc.protocol_vocabulary`
- Construction-profile registry: `zkc.construction_profiles`
- Soundness signature: `zkc.soundness_signature`

A registry is named by its `registry` string and carries no version field
(`docs/spec/versioning.md`). The protocol vocabulary jointly admits six source
sections: `predicate_specs`, `claim_profiles`, `check_contracts`,
`hole_contracts`, `reduction_contracts`, and `terminal_rules`. Unknown fields,
constructors, or unresolved content references refuse.

## Build and check

zkc builds out of tree against MLIR 23 or newer. Point the public `ci` preset
at an MLIR installation, sync the locked reference environment, and build:

```sh
export MLIR_DIR=/usr/lib/llvm-23/lib/cmake/mlir
export LLVM_EXTERNAL_LIT="$(command -v lit)"

uv sync --locked --project reference

cmake --preset ci
cmake --build --preset ci
cmake --build --preset ci --target check-zkc
uv run --locked --project reference python -m oracle.model
```

On Debian or Ubuntu the toolchain comes from
[apt.llvm.org](https://apt.llvm.org) as `libmlir-23-dev`, `mlir-23-tools`, and
`llvm-23-tools`; [Getting Started](docs/getting-started.md) spells that out
along with the normal development workflow. Cargo is not required to build
zkc. When it is available, the lit suite also runs the optional Plonky3
integration tests under `evaluation/`.

The toolchain requirement is a floor rather than a revision, checked when the
build configures. Lockfiles carry the reference environment and the optional
Rust harness. Reproducibility limits are summarized in
[Getting Started](docs/getting-started.md#dependency-policy).

## Read next

- [Documentation map](docs/README.md)
- [Project overview](docs/overview.md) — stable project model and target
  direction; not a current-support claim
- [Architecture](docs/architecture.md) — target architecture,
  including explicitly unimplemented roles and trust boundaries
- [Ecosystem](docs/ecosystem.md) — relation compilers, formal systems,
  proving libraries, compiler infrastructure, and zkVM boundaries; not a
  compatibility matrix
- [Current Status](docs/status.md) — public coverage and evidence dashboard
- [Roadmap](docs/roadmap.md) — planned relation, witness, realization,
  composition, formal-evidence, and system direction
- [Specification overview](docs/spec/overview.md) — normative corpus map
- [Contributing](CONTRIBUTING.md) and
  [Third-party material](THIRD_PARTY.md)

## License

Project-authored material is licensed under the
[Apache License, Version 2.0](LICENSE.md). Third-party material remains under
the terms recorded in
[Third-Party Software and Research Artifacts](THIRD_PARTY.md).

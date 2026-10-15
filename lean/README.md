# Protocol verification in Lean

This package proves claims about **actual imported scalar PIR programs**. The
compiler exports a retained program; Lean checks its typed admission and proves
its open-process contract. Separate consumers derive explicitly selected
properties, including ArkLib interactive Sumcheck soundness and VCVio Schnorr
honest-verifier simulation. A named DSL verification specification can also
connect an authored `spec` target to its imported mathematical relation body.

The [formal reference](docs/README.md) defines the models. [Support](docs/support.md)
states exact claims and assumptions. Native compilation, arithmetic, providers
and the full lowering pipeline are not universally verified by this package.
The [native bridge](bridges/common/README.md) tests the selected boundary with
independent execution and negative controls.
The separate [structured bridge](bridges/structured/README.md) retains shared
helpers, multiple results, finite folds and Local control in a bounded immutable
single-participant profile.

## Architecture

- `Zkc`: typed mathematics and role-local PIR semantics, a shared multi-result
  [structured carrier](docs/design/structured-computations.md), exact refinement,
  specification certificates, protocol contracts and finite security models.
- `ZkcExamples`: actual imported programs, equivalent source forms, composed
  residual/opening clients, effectful structured endpoint examples and a
  downstream custom property.
- `ZkcTools`: executable scalar and structured references, header parser and
  declaration audit.
- [Security integration](integrations/arklib/README.md): optional ArkLib/VCVio
  consumers. The core does not import these libraries.
- [Clean integration](integrations/clean/README.md): isolated finite AIR export
  and native fixture producer; independent of protocol security consumers.

## Build and use

The [toolchain](lean-toolchain) and the three owning Lake manifests pin a coherent
Lean 4.34.1 dependency closure. See the [dependency rationale](docs/dependencies.md).
From `lean/`, `lake build` builds all maintained core libraries, examples, controls,
executables and declaration audits. The optional packages each use `lake build`
from their own directories. [Development](../docs/development/README.md) describes
Nix and the `just fetch-lean`, `just test-lean`, `just test-lean-integration`, and
`just test-lean-clean` entry points.

`just test-lean-native` additionally checks the native import and authored
specification boundary, including differential execution and negative controls.

From the repository root, after preparing the native compiler and Lean packages:

```sh
python3 lean/bridges/common/verify.py \
  --module=example=examples/projects/schnorr/main.zkc \
  --module=schnorr=libraries/schnorr/lib.zkc --entry=example::Interactive \
  --compiler=build/compiler/zkc-compile \
  --spec=lean/bridges/common/requests/schnorr-dsl.json \
  --output=build/reports/lean/schnorr
```

A successful receipt says `verified-in-model`, records exact requested properties,
premises, source/request/certificate identities and dependency manifest identity.
An unsupported contract or an unproved correspondence remains `unresolved`.
The [verification specification](docs/spec/verification.md) explains author input,
proof generation, checked subjects and extension points.

For an isolated build from exact dependency source checkouts, with no prior
project or dependency Lean objects:

```sh
cd lean
python3 reproduce.py --with-arklib --with-clean \
  --dependency-cache .lake/packages \
  --integration-dependency-cache integrations/arklib/.lake/packages \
  --integration-dependency-cache integrations/clean/.lake/packages \
  --output /tmp/zkc-formal-reproduction
```

Use a fresh output directory. The reproducer records source drift, toolchains,
builds, audits, standalone consumers and the Clean fixture comparison. Omit cache
arguments to fetch exact sources. The installed Lean/Std toolchain is trusted.

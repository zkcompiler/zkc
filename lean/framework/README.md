# Standalone protocol-proof framework

This independent Lean package implements fixed requests, top-level proof closure, reusable
component installation, quantitative composition and complete small-model tests. It deliberately
has no imports from zkc's execution model, source readers or production protocol clients.

- [Architecture and research decisions](docs/DESIGN.md)
- [Scope and acceptance plan](docs/PLAN.md)
- [Implementation interfaces](docs/INTERFACES.md)
- [Authoring path and complete examples](docs/AUTHORING.md)
- [Validation and exact claims](docs/VALIDATION.md)
- [Independent review and disposition](docs/REVIEW.md)

The dependency pins and toolchain are part of this package. From this directory:

```sh
lake build
```

During development, select a changed module with `lake build +ProtocolProof.Claims.Closure`.
The root repository's full pipeline is unnecessary for this independent package.

The framework proves model-game claims. Compiler/source integration is a later, separate step
and remains unclaimed here.

The core dependency structure is:

```text
Claims/Request                Semantics/Quantitative
      │                              │
Semantics/System              Components/Contract
      └─────────────┬────────────────┘
Components/Installation ──────┤
                       Claims/Closure
Components/Representation ───┤
                       Claims/Assembly

Claims/Request ──────── Claims/Transfer
```

The component installation and representation modules reuse VCVio's stateful kernel coupling.
The contract rules reuse PolyFun's specification fold. The framework proves their connection
to whole-game claims, rather than adding another program interpreter.

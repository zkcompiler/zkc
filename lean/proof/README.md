# Standalone protocol-proof framework

This independent Lean package implements fixed requests, top-level proof closure, reusable
component installation, quantitative composition and complete small-model tests. It deliberately
has no imports from zkc's execution model, source readers or production protocol clients.

- [Fixed property meanings and receipts](docs/CLAIMS.md)
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
Semantics/Experiment             Semantics/Quantitative (upstream WP/kernels)
       │                                   │
       ├────────── Semantics/System ────────┤
       │                 │                 └── Components/*
       │          Semantics/Access                  │
       │                 │                         │
       └──── Claims/property requests ───── Claims/Closure, Assembly, Transfer
                         │
                Claims/Receipt, Diagnostics
```

`Claims/Request.lean` is a public import module for the unary requests and view comparison.
The extraction and simulation profiles use `Semantics/Access`; `System` does not import claims.
Built-in claim meanings and custom propositions are distinct constructors of `Claim`.


The component installation and representation modules reuse VCVio's stateful kernel coupling.
The contract rules reuse PolyFun's specification fold. The framework proves their connection
to whole-game claims, rather than adding another program interpreter.

# Process-facing protocol-proof framework

This Lean package provides fixed requests, top-level proof closure, exact component installation
and quantitative composition over canonical `PIR.Process`. It shares `PIR.Signature`,
`PIR.Outcome`, `PIR.Execution` and the generic `Zkc.Source.Region` foundation with the concrete
IR through `ZkcProgram`. It has no dependency on concrete IR, source readers, generated subjects
or production protocol clients.

The proof-owned Process migration is implemented and checked. The selected architecture and
remaining integration boundaries are described in [IMPLEMENTATION.md](docs/IMPLEMENTATION.md).
[VALIDATION.md](docs/VALIDATION.md) records the final package build and 1,542-declaration
standard-axiom audit, separately from historical evidence.

- [Fixed property meanings and receipts](docs/CLAIMS.md)
- [Architecture and research decisions](docs/DESIGN.md)
- [Scope and acceptance plan](docs/PLAN.md)
- [Implementation interfaces](docs/INTERFACES.md)
- [Authoring path and complete examples](docs/AUTHORING.md)
- [Validation and exact claims](docs/VALIDATION.md)
- [Independent review and disposition](docs/REVIEW.md)

The package requires **Lean 4.35.0** (`leanprover/lean4:v4.35.0`) and the relative Lake
dependency `zkc_program` at **`../program`**. Keep `lean/program` beside `lean/proof`;
copying the proof directory alone is insufficient. VCVio, PolyFun and Mathlib revisions
are pinned by the package. Run from `lean/proof` so its toolchain is selected:

```sh
lake build
```

During development, select a changed module with `lake build +ProtocolProof.Claims.Closure`.
The package gate checks all complete models and controls. Cross-package wiring and concrete
integration require their own affected checks.

The framework proves model-game claims. Compiler/source integration is a later, separate step
and remains unclaimed here.

The dependency structure is:

```text
ZkcProgram                  pinned VCVio / PolyFun / Mathlib
    │                                      │
    └── Semantics/Execution ── Internal/* ───┘
                                  │
                  Semantics/System, Quantitative
                           │              │
                  Semantics/Access    Components/*
                           │              │
                  Claims/property requests, Closure, Assembly
                           │
                  Claims/Receipt, Diagnostics, Transfer
```

`Claims/Request.lean` is a public import module for the unary requests and view comparison.
The extraction and simulation profiles use `Semantics/Access`; `System` does not import claims.
Built-in claim meanings and custom propositions are distinct constructors of `Claim`.

`System.experiment` returns complete `Execution` records: outcome, reached state and ordered
events. Internally, `Internal.effects` and `Internal.encode` feed one stop-aware interpretation
to upstream `FreeM.runKernel`; authors use Process. Exact `Installation` reuses VCVio couplings,
and Process contracts and root closures reuse the existing backend proofs and PolyFun fold.

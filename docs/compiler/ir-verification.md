# Native IR verification

[`Zkc::IR`](../../compiler/README.md#components) contains dialects, operation
interfaces and mandatory root verification. `Zkc::Translation` separately owns
source import and checked export. IR links common source
services and MLIR IR facilities, without Claims, frontend, passes or driver services.
The optional `Zkc::ClaimTranslation` component links Claims and IR for claim
import and independent candidate checking; claim dialect structure stays in IR.
This page maps native checks to their owners; the
[refinement specification](../spec/verification/refinement.md) owns their meaning.

## Checking boundaries

| Check | Owner | Establishes |
|---|---|---|
| Local IR formation | ODS constraints, strict property conversion, type and operation verifiers | Attribute and SSA types, symbol/call signatures, binding applicability, nested region signatures and variant payloads |
| Whole protocol | `ProtocolModuleOp::verifyRegions`, checked `protocol::exportSource`, common-source admission | Complete declarations, dependencies, participant/resource/control obligations and exact generated relation correspondence |
| Finite-table program | `PIRProgramOp`/`PlanProgramOp` root verifiers and `SourceLibraryInterface` | Installed descriptor/context/signature agreement and valid program bodies for this route |
| Relation assets and declarations | Relation IR readers and verifiers | R1CS/AIR validity and canonical representation; external relation key/revision, typed purposes and declaration conflicts |
| Stage readiness | Existing admission and lowering entry points | That the valid input meets the selected transformation's stage and representation requirements |
| Source-relative correctness | Construction and claim checkers above IR | Candidate correspondence to independently retained source, selections and caller premises |

A standalone operation can satisfy local constraints without being a complete
protocol. Whole-protocol checks apply to the `protocol.module` root. Claim operations
retain their structural ODS checks; their source-relative judgment is an explicit
client of the IR library, not something generic MLIR verification establishes.
Import/export, a pass run and a security theorem are distinct obligations.
Region-verifier hooks are private implementation details: their typed accessors
rely on MLIR having checked nested operations first. External clients use
`mlir::verify` or checked protocol export.

## Translation and complete-root admission

[`Translation/Protocol.h`](../../compiler/include/zkc/Translation/Protocol.h)
imports common or participant source and exposes checked export. Import first
admits the common model, builds IR and runs MLIR verification. Export first runs
complete MLIR verification, including profile and retained metadata checks. It
then reconstructs and admits the executable model. The core IR reader in
[`Protocol/Execution.h`](../../compiler/include/zkc/Dialect/Protocol/Execution.h)
provides that reconstruction without an export dependency. The root verifier
uses its internal implementation after nested operations have been checked;
it does not recursively invoke checked export. `readExecutionModel` alone does
not establish the mathematical profile or projection-metadata invariants.

Mathematical common and endpoint profiles use native SSA admission. They do not
need an executable source model until binding. The native execution model may
exist internally at the logical stage; the native JSON interchange tag is
physical-only. Checked export enforces this boundary.

Retained relation declarations and generated functions must still correspond
exactly. A locally well-typed edit to generated code can therefore fail root
verification. R1CS multilinear and rank-one views, both specialized and using
public matrices, and AIR arithmetic views follow that same boundary.

[`Translation/Table.h`](../../compiler/include/zkc/Translation/Table.h) owns the
separate finite-table adapter;
[`Translation/Relations.h`](../../compiler/include/zkc/Translation/Relations.h)
owns R1CS/AIR import. Attribute conversion and operation decoding belong to
[`Relation/IR/Assets.h`](../../compiler/include/zkc/Dialect/Relation/IR/Assets.h),
which IR and transformations can use without Translation. Neither API exposes
transformation passes. Projection and physical planning use
[`Transforms/Protocol.h`](../../compiler/include/zkc/Transforms/Protocol.h).
The relation deduplication pass consumes the core relation reader from its own
`Dialect/Relation/Transforms` home.

Protocol and table import require loaded dialects. At context setup, call
`registerDialects(registry)`, install any source library models (for example,
`registerTableLibrary(registry)`), construct the context with that registry, then
call `context.loadAllAvailableDialects()`. Standalone R1CS/AIR imports load their
own relation dialect; they do not initialize the complete protocol environment.

These APIs do not cache a permanent verification fact on mutable MLIR. A caller
that changes a module must verify/export the changed module again. Location
callbacks during import reference the caller's source for diagnostics; locations
are not evidence of source correspondence.

## Structured diagnostics

[`Dialect/Diagnostics.h`](../../compiler/include/zkc/Dialect/Diagnostics.h)
transports native `Refusal` fields into nonprinting MLIR diagnostic metadata.
MLIR still owns locations, severity, operation prefixes, notes and rendered text.
A handler can inspect identifiers without splitting diagnostic strings:

```cpp
mlir::ScopedDiagnosticHandler handler(&context, [&](mlir::Diagnostic &diagnostic) {
  for (const auto &refusal : zkc::diagnostics::refusals(diagnostic))
    recordRefusal(refusal.code, refusal.detail);
  diagnostic.print(llvm::errs());
  return mlir::success();
});
```

Metadata stores strings in the MLIR context; the inspection API returns owned
copies. It does not retain pointers into temporary reconstructed source or native
errors. The detail field contains the detail supplied at emission; diagnostics
whose explanation is streamed incrementally may leave it empty. Streamed context
remains in the diagnostic's text. Multiple native refusals retain
their order. Ordinary MLIR/LLVM errors receive no inferred identifier, and notes
remain separate diagnostics. Metadata is diagnostic information, not proof data
or serialized protocol identity.

## Dependency and regression controls

The fast [component check](../../compiler/test/component_dependencies.py) checks
source ownership, actual CMake edges and public/private/generated include closure.
Only declared TableGen outputs are admitted, even in reused build directories.
IR cannot include Translation, frontend, workflow or transformation headers or
MLIR pass infrastructure. Transforms also cannot depend on Translation. The
[installed IR consumer](../../tests/consumer/ir.cpp) verifies native units with
only `Zkc::IR`. The [Translation consumer](../../tests/consumer/translation.cpp)
imports and exports relation views and finite-table programs, including malformed
cases. The [Transforms consumer](../../tests/consumer/transforms.cpp) runs the
native mathematical pipeline without linking Translation. These checks do not establish that every
nested verifier runs before root verification: MLIR can run region verification
before SSA dominance checks. In particular, a use before definition can reach
source export and be reported as `implicit-capture`.
[Native controls](../../compiler/test/ir_verification.cpp) exercise exact generated
body checks across five views; separate diagnostic and property tests cover
structured refusals. These are bounded implementation checks, not native
refinement or protocol security proofs.

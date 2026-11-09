# Protocol proof core

`protocol_proof` owns fixed security meanings, complete probabilistic execution, local
component contracts, installation and property-directed root closure. Its public program
is `PIR.Process`, defined once in the shared `zkc_program` package. Generic Region syntax
lives in that same shared package; concrete dialects and readers remain in `zkc`.

```text
                 zkc_program (Std only)
                   /               \
       zkc (concrete IR)       protocol_proof
                   \               /
                       zkc_security
```

The probability interpreter uses pinned VCVio/PolyFun kernels through an internal,
failure-aware encoding. Authors write Process programs and mathematical obligations;
they do not maintain a second FreeM program. Every public execution retains its terminal
outcome, reached state and ordered events. Claims select a fixed measurable observation
of that complete law; they never condition on successful execution.

- [Architecture and responsibility boundaries](docs/DESIGN.md)
- [Public interfaces](docs/INTERFACES.md)
- [Authoring and complete model clients](docs/AUTHORING.md)
- [Fixed property meanings and receipts](docs/CLAIMS.md)
- [Package plan and remaining work](docs/PLAN.md)
- [Validation evidence](docs/VALIDATION.md)
- [Review record](docs/REVIEW.md)

Run `lake build` here for the package and its declaration/axiom audit. During development,
use a changed target, such as `lake build +ProtocolProof.Components.ServiceInstallation`.
The separate shared program package is built from `../program`.

This package includes complete mathematical model clients. Actual imported protocol
adoption and the common proof-construction/companion engine are later packages, not
inferred from those model results.

# Shared program and proof migration

The selected design and plan are
`/ethereum/wonjae/archives/zkc/unified-proof-architecture-2026-11-09/{DESIGN,PLAN}.md`.
This unit implements Package 1's Process-facing proof core. Package 2 and cross-package
wiring/integration remain separate work.

`lean/program` owns the canonical `PIR.Signature`, `PIR.Process`, `PIR.Outcome`,
`PIR.Execution`, `PIR.Stop` and generic `Zkc.Source.Region` definitions. Their declaration
namespaces are retained without compatibility aliases. `lean/proof` consumes `ZkcProgram`
through `../program`; it does not import concrete IR or generated subjects. This proof-only
unit does not change tracked shared-program sources.

## Implemented proof boundary

The public surface includes measurable complete execution, `System E I S L`, Process-indexed
operation specifications and upper/lower contracts, exact same-interface `Installation`,
contextual transports and both root evidence records. The former public connection and FreeM
contracts are retired without aliases. The checked backend remains internal implementation.

Probability execution uses `Internal.effects`/`Internal.encode` and upstream `FreeM.runKernel`
with accumulated state and ordered events. The general monadic correspondence, normalized
probability laws, complete bind equation and deterministic Dirac agreement preserve every stop.
Existing backend contract, coupling and root closure proofs are reused. Public adequacy covers
measurable complete rewards and whole initial experiments. The structural Process resource
bound is proved equal to upstream charge semantics.

Extractor and simulator access, both complete model clients and all existing property/refusal
controls use the public carrier. New execution and contract controls exercise full records,
mixed returned/stopped laws, both roots and the explicit stopped-branch obligations.
[VALIDATION.md](VALIDATION.md) records the final Lean 4.35 package build and
1,542-declaration standard-axiom audit. [REVIEW.md](REVIEW.md) distinguishes source review
from the independent review of earlier checkpoints.

## Remaining integration boundary

Package 2 owns broader composition, differing-interface decoding and security transformations.
Same-interface installation and canonical Process operation substitution do not establish
those contracts. The shared-state model's arbitrary Process inlining law uses its deterministic
component meanings; a generic differing-interface probability transport remains separate.

Cross-package wiring and concrete-subject validation belong to integration. The checked
construction/proposer path, broader family-library migration and actual protocol adoption
belong to later architecture units. No automatic constructor, production protocol security
result or runtime/PPT adequacy is claimed here.

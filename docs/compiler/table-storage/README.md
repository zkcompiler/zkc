# Independent table models

[Model.lean](Model.lean) and [Storage.lean](Storage.lean) are standalone research
models of field-table meaning and storage. They remain independent of the native
compiler and Runner. Their presence does not provide a supported table executor,
PIR source interface or native correspondence theorem.

The selected mathematical contracts live in
[polynomial semantics](../../spec/domains/polynomials.md),
[direct logical plans](../../spec/profiles/compiler/direct-plan.md) and
[complete-result representations](../../spec/realization/representations.md).
Current execution uses [mathematical MLIR](../protocol-pipeline.md) and
`zkc.program/1`.

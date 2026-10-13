# Scalar mathematical source export

`zkc-compile protocol-lean FILE --symbol=SYMBOL` exports a selected program from
retained protocol-profile MLIR as `zkc.common-source/0`. This is an optional
formal import boundary, separate from executable program serialization.
The whole supplied module must pass native verification before export.

The top-level JSON array contains, in order:

```text
[format, source-sha256, symbol, roles, input-types, input-role-sets,
 result-type, output-role-set, instructions, returned-reference]
```

The digest is `sha256:` followed by the lowercase digest of the supplied bytes.
Role indices refer to `roles`; type tags preserve nominal field, group and
service identities. Boolean, field, group and service inputs form the initial
ordered context. Each value-producing instruction prepends its result; operand
and return indices refer to that current context. Guards and statement metadata
do not add values. Pure static helpers expand using their actual operands.

The selected definition is either a scalar mathematical protocol or a private,
single-block pure function with one result. A function receives one synthetic
role, `formula`, for all inputs and its result. Protocol effects are refused in
such a function. This case imports the actual body of an authored relation.

The profile bounds source text to 16 MiB, emitted JSON to 1 MiB, strings to
512 bytes, roles to 16, inputs to 512, instructions to 1024, inspected operations
to 4096 and helper nesting to 64. Unsupported types, operations, signatures or
effects are errors. The exporter does not invent an interpretation for them.

The [formal profile](../../../lean/docs/spec/common-source.md) specifies the
consumer's independent typed admission, vocabulary and interpretation. The
[verification specification](../../../lean/docs/spec/verification.md) describes
how author-selected targets and properties become checked Lean subjects.
Matching source identities and passing native verification establish provenance
and native admission; they are not a theorem that the exporter preserves meaning.
The [bridge controls](../../../lean/bridges/common/README.md) compare an independent
native SSA interpreter with Lean execution for this bounded scalar profile.

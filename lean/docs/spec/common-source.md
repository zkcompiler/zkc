# Scalar common-source profile

The [native export contract](../../../docs/spec/formats/common-source.md) owns
the compiler boundary; this page specifies its independent formal admission.

`zkc-compile protocol-lean FILE --symbol=SYMBOL` verifies retained protocol-profile
MLIR and exports a selected scalar mathematical program. A private, single-block
pure function may also be selected to import an authored relation formula.
Formula inputs and output belong to one synthetic participant; this is a
mathematical predicate interpretation, not protocol communication.

The exact JSON array schema is `zkc.common-source/0`:

```text
[format, source-sha256, symbol, roles, input-types, input-role-sets,
 result-type, output-role-set, instructions, returned-reference]
```

References index the current context; each value-producing instruction prepends
its result. Guards and statement annotations do not. Supported sorts are Boolean,
nominal field, nominal group and nominal service references. Supported arithmetic
includes field constants/add/subtract/multiply/equality, group identity/add/scale/
equality, Boolean operations and selection. Effects are role restrictions,
exchange, owner-local scalar draws, guards and retained statement metadata.
The vocabulary and exact constructor arities live in
`Zkc.Source.Common.Vocabulary` and `Zkc.Source.Common.Format`.

The exporter admits one result, at most 16 roles, 512 inputs, 1024 instructions,
64 static helper nesting levels and 4096 inspected operations. It bounds retained
MLIR to 16 MiB and its JSON export to 1 MiB; strings are at most 512 bytes. Lean
bounds JSON nesting and integer tokens before decoding and checks exact shapes,
unique roles/sites, scopes, input arity, reference types and output availability.
Malformed dormant definitions are refused, not silently discarded. Unsupported
arrays, commitments, general control and other dialect operations require an
extension with a stated interpretation.

The source digest identifies retained native text. It does not prove semantics.
The native `language-interface` identity and chosen symbol are compared before
verification. Constructor data is freshly rendered, admitted by `Snapshot.check`,
and tied to a separately generated requested-subject theorem. The renderer,
parser and interface-name resolution remain tested software boundaries.

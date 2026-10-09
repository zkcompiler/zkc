# Relation data

These small fixtures describe mathematical constraints independently of a proof
protocol:

- [multiply.r1cs.json](multiply.r1cs.json) contains one BN254 rank-one constraint.
- [squaring.air.json](squaring.air.json) constrains an initial trace value and
  consecutive squaring transitions.

The compiler can inspect and import relation data directly:

```sh
zkc-compile relation-inspect examples/relations/multiply.r1cs.json
zkc-compile relation-import examples/relations/multiply.r1cs.json Circuit
zkc-compile relation-air-import examples/relations/squaring.air.json Trace
```

The [source language](../../docs/language/mathematical.md) also captures relation
assets with explicit `--asset=NAME=FORMAT=FILE` arguments. Supported formats are
`r1cs-json`, `r1cs-binary` and `air-json`. A captured relation does not generate a
witness, select a proof system or insert a protocol check. The authored protocol
owns the computation and acceptance decision.

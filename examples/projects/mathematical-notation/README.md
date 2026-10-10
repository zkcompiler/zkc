# Mathematical notation

[The source](main.zkc) computes a weighted interpolation with named functions
and library notation. Importing `zkc::vector` activates its public declarations:

```zkc
let blended = a * (1 - α) + b * α;
return ⟪weights, blended⟫;
```

The paired delimiters call `vec::dot`. The separate `a ⊙ b` result calls
`vec::hadamard`, the existing elementwise multiplication operation. Vector `*`
continues to scale a vector by a scalar on its right. Every notation operand is
an ordinary expression evaluated once in written order. Length checks and stop
behavior are the same as for the named calls.

For `a = [2, 3]`, `b = [5, 7]`, `weights = [11, 13]` and `α = 2`, both scalar
outputs are `231`, and the pointwise output is `[10, 21]` in BLS12-381 Fr.

```sh
cd examples/projects/mathematical-notation
zkc check --notations
zkc inputs check --operation=run
zkc run
```

The supplied [input map](inputs/example.Run/P.json) contains these values.
`run` writes named outputs to `build/zkc/example.Run.results.json`.

`α` is a source identifier with exact NFC spelling. Input and output JSON keep
those source names. Source locations count UTF-8 bytes; editor clients convert
them to their own coordinate system. The compiler accepts the characters
directly and needs no editor input plugin.

See the [library guide](../../../libraries/README.md) for named alternatives and
the [source contract](../../../docs/spec/language/definitions.md#library-defined-operators)
for visibility, precedence and local scope rules.

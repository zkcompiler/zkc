# Mathematical libraries

[The source](main.zkc) evaluates a two-element table in two ways: a formal
multilinear polynomial in `math fn`, and an ordered runtime vector fold in `fn`.
For `values = [a, b]`, both compute `(1 - point) * a + point * b`.

Compile from the repository root:

```sh
zkc compile --module=example=examples/projects/mathematics/main.zkc \
  --module=zkc::vector=libraries/zkc/vector.zkc \
  --module=zkc::symbolic=libraries/zkc/symbolic.zkc \
  --entry=example::Run --output=mathematics.entry
```

Use `zkc inspect` for the named input/output interface and `zkc run` for local
execution. Runtime values use the Entry Host codecs. See the
[library guide](../../../libraries/README.md) for the public APIs and the
[walkthrough](../../../docs/getting-started.md) for invocation.

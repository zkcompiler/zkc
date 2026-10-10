# Mathematical libraries

[The source](main.zkc) evaluates a two-element table in two ways: a formal
multilinear polynomial in `math fn`, and an ordered runtime vector fold in `fn`.
For `values = [a, b]`, both compute `(1 - point) * a + point * b`.

Compile from the repository root:

```sh
zkc compile --project=examples/projects/mathematics/zkc.toml \
  example::Run --output=mathematics.zkpkg
```

Use `zkc inspect` for the named input/output interface and `zkc run` for local
execution. Runtime values use the Entry Host codecs. See the
[library guide](../../../libraries/README.md) for the public APIs and the
[walkthrough](../../../docs/getting-started.md) for invocation.

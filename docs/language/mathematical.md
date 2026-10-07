# Author mathematical protocols

The `.zkc` language compiles concrete field and Boolean calculations, mathematical
helpers, explicit messages and selected Entries directly into mathematical MLIR.
The [source profile](../spec/profiles/source/mathematical-language.md) defines its
syntax, role semantics, checks and limits. Wider language features remain under
[frontend migration](../roadmap.md).

For a complete small example, read [algebra.zkc](../../compiler/test/fixtures/language/algebra.zkc)
and [transfer.zkc](../../compiler/test/fixtures/language/transfer.zkc). The two
helpers compute different field expressions; P sends their results to V, which
uses its own input component and the values actually received.

From the repository root, using the compiler selected by your build:

```sh
zkc-compile language-check --source-format=zkc --entry=transfer::Demo \
  --module=algebra=compiler/test/fixtures/language/algebra.zkc \
  --module=transfer=compiler/test/fixtures/language/transfer.zkc
```

Use the same options with `language-emit` to print checked original MLIR,
`language-interface` for the selected Entry's named port layout, or
`language-bundle` for an executable bundle. Every command checks source, target
admission and source correspondence. There is no implicit import discovery or
fallback to the `.pir` parser. `--no-simplify` and `--release-storage` select
existing downstream compiler options for bundle production.

A bundle uses the existing [native runtime](../runtime/bundles.md). Its entry is
the encoded protocol symbol recorded in the source interface. Runtime inputs
are supplied using the bundle's physical input layout. For the transfer example,
P supplies x and c; V supplies its own c. The
[participant execution control](../../crates/zkc-tools/examples/language_native.rs)
also demonstrates direct independent runners, changed receive values and the
existing joint host with independently supplied role inputs.
There is no protocol-specific runtime or source-facing Host generator here.

## C++ boundaries

- `Zkc::Language`: capture supplied buffers, analyze them, and close an exact
  Entry. This library depends only on Contracts and its common support.
- `Zkc::Translation`: emit unsimplified mathematical MLIR and independently
  admit and compare actual SSA with the checked source.
- `Zkc::CompilerCore`: `prepareOriginal` retains immutable bytes, interface,
  comparison and diagnostic mappings; `compileEntry` returns that retained
  original and the existing `CompiledRun` candidate through const accessors.
  Only successful compilation can construct `CompiledEntry`; downstream MLIR
  remains caller-accessible and is separate from the immutable original.
- `Zkc::Driver`: read explicit bounded files and render command results.

The public APIs are [Language/Project.h](../../compiler/include/zkc/Language/Project.h),
[Translation/Language.h](../../compiler/include/zkc/Translation/Language.h), and
[Compiler/Language.h](../../compiler/include/zkc/Compiler/Language.h).
Diagnostics retain byte spans; recovery tokens cannot be promoted into checked
state. The compiler never accepts a caller-constructed checked project.

Target failures retain their phase and generated coordinates. Admission failures
also identify a related source declaration; later compiler diagnostics use the
operation map established by source comparison when a position matches.
Unsupported planned syntax reports `source.unsupported` and is reserved.

The interface's toolchain stamp records the compiler source, installed catalog,
LLVM/MLIR release and LLVM revision when the installation provides it. An absent
revision is explicit. This is provenance, not a binary fingerprint: it cannot
distinguish local patches that preserve all recorded version information.

# A separately authored compiler domain

This contribution defines `Envelope<T, N>` and `envelope.keep` in neutral
TableGen, a native MLIR type/operation, and a typed adapter. The frontend uses
the generated `zkc::envelope` exports without parser changes. Generic multi-result
and domain-bound controls exercise declarations that deliberately have no native
implementation. This example supplies neither a runtime kernel nor a codec.

The files stay together:

- `include/envelope/Declarations.td`: logical contracts and source exports.
- `include/envelope/Native.td`: ordinary MLIR ODS and explicit native bindings.
- `lib/`: native type/operation definitions and the adapter helper.
- `include/envelope/Specialization.{td,h}` and `lib/Specialization.cpp`:
  an IR-only composite and its restoration pass.
- `contribution.cmake`: ordinary MLIR generation plus one registration with the
  compiler installation.
- `consumer/`: a separate CMake project that sees only the installed package.

From the repository root, inside the development environment:

```sh
just test-install-domain
just test-install-domain shared
```

These opt-in checks build a base and an extended installation, consume their
fresh prefixes, compile each public contribution header independently, and check
that identical library source captures different installed declarations. They
also reject unknown owned properties and uninstalled vocabulary. For a manual
extended build:

```sh
cmake -S compiler -B build/compiler-domain -G Ninja \
  -DCMAKE_BUILD_TYPE=Release -DBUILD_TESTING=OFF \
  -DZKC_CONTRIBUTION_FILES="$PWD/compiler/examples/domain/contribution.cmake"
cmake --build build/compiler-domain --target zkc-compile zkc-opt -j 4
cmake --install build/compiler-domain --prefix "$PWD/build/domain-install"
cmake -S compiler/examples/domain/consumer -B build/domain-consumer -G Ninja \
  -DZkcCompiler_DIR="$PWD/build/domain-install/lib/cmake/ZkcCompiler"
cmake --build build/domain-consumer -j 4
ctest --test-dir build/domain-consumer --output-on-failure
```

Use fresh build, install and consumer directories for a shared-library run,
adding `-DBUILD_SHARED_LIBS=ON` to the compiler configure command. Point the same
consumer at a base installation with `-DEXPECT_ENVELOPE=OFF` to test refusal of
uninstalled vocabulary. Both variants run the installed `zkc-tblgen` against
installed schemas and test addition/ownership/native-coverage failures.

A contribution is selected while **building a new installation**. It is not
linked over an installed catalog object, and source `use` cannot load code.
The consumer can be copied outside the checkout; it does not include its
source or build directories. Header declarations and TableGen inputs are
installed; generated registration definitions remain private to their owning
libraries. The public API is a same-version compiler extension mechanism, not a
binary plugin ABI or a standalone SDK for arbitrary Rust/Lean value families.
Generated public headers are declared in `PUBLIC_HEADERS` and private generated
definitions in `GENERATED_SOURCES`; the compiler checks their ownership before
generation and installs only the declared public inventory.

## Decomposition and independent execution

`Specialization.td` defines an IR-only ordered two-add composite. Its patterns
retain both admitted operations' complete dictionaries and locations. The
consumer checks exact restoration at function, common-protocol and participant
levels, refusal before decomposition, malformed-pattern controls and equality
with directly compiled physical carriers. Unused bindings remain present.
This example establishes no speedup or general rewrite theorem.

With the Rust and Lean tools built, compare the restored program independently:

```sh
python3 compiler/examples/domain/consumer/execution.py \
  --consumer build/domain-consumer/envelope-specialization \
  --runtime target/debug/zkc \
  --checker formal/.lake/build/bin/interactive-protocol
```

The check covers source admission, participant correspondence, two numeric
inputs including modular wraparound, message output and resource observations.
The `Envelope` primitive itself intentionally remains without Rust/Lean support;
the restored arithmetic program uses only already admitted field operations.

To include independent Rust/Lean execution in the installed consumer checks,
append `--runtime /path/to/zkc --checker /path/to/interactive-protocol` to
`just test-install-domain`. Both tools must already be built. The additional
CTest case checks restored source admission, candidate correspondence and two
field-arithmetic executions. It does not install a kernel for `envelope.keep`.

# HEIR arithmetic

This optional library reuses HEIR Polynomial, ModArith and RNS sources with the
same LLVM/MLIR release as zkc. The admitted transformation boundary currently
covers scalar-modulus negacyclic ring expressions and full NTT placement.
[The arithmetic profile](../../../docs/spec/realization/heir-arithmetic.md)
defines the inputs, comparison and limits. This package is not yet called by
the `.zkc` compiler or the managed native runtime.

`ZkcHeirArithmetic` contains selected upstream dialects and passes.
`ZkcHeirAdmission` independently interprets source and candidate SSA values,
compares ring expressions, and checks evaluation coordinates.
`placeTransforms` retains the source and returns only a checked candidate.
There is no second serialized arithmetic graph or execution interpreter.

Three tools expose different boundaries:

- `zkc-heir-place SOURCE.mlir` prints a candidate only after profile admission,
  transform placement and source/candidate comparison succeed.
- `zkc-heir-check SOURCE.mlir CANDIDATE.mlir` compares independently supplied IR.
- `zkc-heir-opt` exposes the selected upstream passes for development and
  regression testing. Its output has no zkc admission claim.

## Build

[pins.json](pins.json) selects HEIR `v2026.10.01`, LLVM/MLIR `23.1.3` and
OR-Tools `9.15.6755`. The [build helper](build.py) checks the archive and patch
hashes, extracts a private source tree, applies the patch without fuzzy matches,
and records prepared-source hashes and configuration. It refuses a changed
prepared source or a different pin set. It does not download dependencies.

Acquire the HEIR archive from the URL in the manifest. Provide LLVM/MLIR CMake
packages and binaries, and a compatible OR-Tools C++ installation. The manifest
also records the official Linux SDK used for qualification. That SDK and its
compression dependencies remain part of the build environment; the helper does
not establish source-to-binary correspondence for supplied packages.

```sh
python3 compiler/external/heir/build.py \
  --archive /path/to/heir-source.tar.gz --work build/heir-arithmetic \
  --llvm-dir /path/to/llvm/lib/cmake/llvm \
  --mlir-dir /path/to/mlir/lib/cmake/mlir \
  --ortools-dir /path/to/ortools/lib/cmake/ortools \
  --mlir-tblgen /path/to/mlir-tblgen \
  --cc /path/to/clang --cxx /path/to/clang++ --jobs 2
ctest --test-dir build/heir-arithmetic/build --output-on-failure
```

CMake finds `mlir-opt`, `mlir-runner` and `mlir_c_runner_utils` under the selected
MLIR installation for execution tests. They can be selected explicitly using
`ZKC_HEIR_MLIR_OPT`, `ZKC_HEIR_MLIR_RUNNER` and `ZKC_HEIR_RUNNER_UTILS` when
configuring CMake. Build outputs and downloaded sources remain outside source
control. The main compiler does not acquire a dependency by building this
optional package.

`ZKC_HEIR_ENABLE_SANITIZERS=ON` instruments the zkc readers and checking drivers
with AddressSanitizer and UndefinedBehaviorSanitizer. The externally supplied
LLVM, MLIR and OR-Tools libraries remain uninstrumented. Mixed-build runs can
disable LLVM allocator poisoning with `ASAN_OPTIONS=allow_user_poisoning=0`.

## Maintained upstream patch

[arithmetic.patch](patches/arithmetic.patch) applies to the exact HEIR revision
in the manifest. The modified files are upstream HEIR sources, distributed under
their Apache-2.0 license; zkc's modifications are kept as an explicit patch.

- Remove a newer TableGen assembly option for LLVM/MLIR 23 compatibility.
- Align constant-folded transforms with generated execution: natural evaluation
  order at the IR boundary and the inverse-root attribute on inverse transforms.
- Cancel transform pairs only for explicit inverse roots in the same ring.
  RNS cancellation remains disabled rather than assuming an unexamined basis.
- Bound the leading-term scan at coefficient zero for the zero polynomial.
- Limit the placement solver to one worker and ten seconds. A feasible solution
  is eligible for comparison; neither optimality nor deterministic scheduling
  is promised.

The patches have local regression coverage and have not been accepted upstream.
When updating the pin, review each patch against upstream behavior instead of
carrying it forward mechanically. The external source and generated headers are
not vendored into zkc.

## Validation scope

The test runs actual placement, independent expression comparison, arithmetic
lowering, tensor bufferization and LLVM execution. It compares complete results
against Python integer convolution for a four-term dot product, a 4-by-4
ML-DSA-shaped module product and Falcon-sized batched products. These are
arithmetic workloads, not full signature verification.

Mutations cover changed arithmetic and inputs, mismatched roots, centered lifts,
cyclic rings, composite or unsupported moduli, storage width and extra
attributes. Transform folding is compared with execution for both inverse-root
and noninverse-root pairs. The native allocation, failure-order and artifact
admission contracts are not covered by these standalone executions.

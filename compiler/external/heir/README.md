# HEIR arithmetic

This compiler dependency reuses HEIR Polynomial, ModArith and RNS sources with the
same LLVM/MLIR release as zkc. The admitted transformation boundary currently
covers scalar-modulus negacyclic ring expressions and full NTT placement.
[The arithmetic profile](../../../docs/spec/realization/heir-arithmetic.md)
defines the inputs, comparison and limits. The default
`.zkc` compiler uses the installed package for admitted whole quotient
calculations and emits checked operations for the managed native runtime.

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
the source-built OR-Tools `v9.15` package (CMake version `9.15.9999`).
The default Nix compiler, developer shell and installed SDK include this
qualified dependency. Build it independently with:

```sh
nix build .#heir-arithmetic
```

The derivation verifies the HEIR archive and patch hashes, applies the patch
without fuzzy matches, and runs arithmetic and relocated SDK checks. It reuses
the pinned Nixpkgs OR-Tools source hash and its matching Abseil, Protobuf and
solver dependency closure. It does not download a prebuilt vendor SDK.

For a manually provisioned toolchain, the [build helper](build.py) verifies the
archive and patch hashes, records prepared-source hashes and configuration,
and refuses changed prepared sources or pins. It does not download dependencies.
Acquire the HEIR archive from the manifest and provide the exact selected
LLVM/MLIR and OR-Tools CMake packages with their transitive dependencies:

```sh
python3 compiler/external/heir/build.py \
  --archive /path/to/heir-source.tar.gz --work build/heir-arithmetic \
  --llvm-dir /path/to/llvm/lib/cmake/llvm \
  --mlir-dir /path/to/mlir/lib/cmake/mlir \
  --ortools-dir /path/to/ortools/lib/cmake/ortools \
  --mlir-tblgen /path/to/mlir-tblgen \
  --cc /path/to/clang --cxx /path/to/clang++ --jobs 2
ctest --test-dir build/heir-arithmetic/build --output-on-failure
cmake --install build/heir-arithmetic/build --prefix /path/to/heir-sdk
```

CMake finds `mlir-opt`, `mlir-runner` and `mlir_c_runner_utils` under the selected
MLIR installation for execution tests. They can be selected explicitly using
`ZKC_HEIR_MLIR_OPT`, `ZKC_HEIR_MLIR_RUNNER` and `ZKC_HEIR_RUNNER_UTILS` when
configuring CMake. Build outputs and downloaded sources remain outside source
control. A manually provisioned compiler requires the same package:

```sh
cmake -S compiler -B build/compiler \
  -DZkcHeirArithmetic_DIR=/path/to/heir-sdk/lib/cmake/ZkcHeirArithmetic \
  -DCMAKE_PREFIX_PATH=/path/to/qualified/dependencies
cmake --build build/compiler --parallel 2
ctest --test-dir build/compiler --output-on-failure
```

The installed `ZkcHeir::Arithmetic` and `ZkcHeir::Admission` targets discover the
exact LLVM/MLIR and OR-Tools dependencies. The main compiler checks the selected
HEIR revision and patch digest against its manifest. Installed zkc SDK consumers
requesting Transforms or its dependents also need this package; lower components
do not. HEIR requires C++20 in its private compiler dependency. The public zkc
headers remain usable from C++17.

The SDK contains the transitive public dialect header closure, generated
headers, library archives, license and pin manifest. Packaging rewrites only
upstream repository-relative LLVM/MLIR include spellings to installed spellings.
It exports no experimental checkout paths or include symlinks. The installed
consumer test relocates the SDK before compiling, linking and executing an
actual placement call.

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
and noninverse-root pairs. These standalone executions do not cover native allocation or artifact
admission. The main compiler's `heir-quotients` checks exercise the separate
managed recipe reader, input/output aliases, source preservation, transform
sharing, optional capacity fallback and altered native candidates. The common
formal quotient suite exercises `.zkc` compilation and managed execution for
the large ring workloads. Coefficient execution remains the current realization
for entries outside the admitted transform profile or available optimization
capacity; no separate compiler build is needed.

Checked placement selects roots with a bounded, charged search over the admitted
prime/power-of-two profile. It then uses the upstream placement and cleanup
passes. The development optimizer continues to expose upstream root attachment
for standalone qualification; main compiler admission does not invoke an
unbounded generator search.

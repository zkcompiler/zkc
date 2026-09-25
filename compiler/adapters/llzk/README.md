# LLZK relation adapter

This standalone LLVM 20 executable imports a bounded LLZK constraint subset into
ordinary R1CS. The main compiler consumes the binary through its independently
bounded `relation-read` command. The two LLVM versions run in separate processes.
The normal compiler build neither builds nor links this adapter.

## Build and use

Use the exact source and toolchain tuple in [pins.json](pins.json).
The [Nix package](../../../nix/llzk.nix) fetches hash-checked sources, builds the
library and adapter with their separate LLVM 20 toolchain, and runs the adapter
tests. From the repository root:

```sh
nix develop
nix build .#llzk --out-link build/llzk
nix build .#compiler --out-link build/installed-compiler

python3 compiler/adapters/llzk/import_relation.py circuit.llzk \
  --adapter build/llzk/bin/zkc-llzk \
  --native build/installed-compiler/bin/zkc-compile \
  --field bls12381 --entry Main --outputs out --public-inputs a \
  --output /tmp/imported-circuit
```

The output directory must not exist. Nix binaries carry their runtime library
paths. For independently supplied builds without the runtime search path, supply
`--adapter-library-path`; this setting applies only to the LLVM20 process.
`cmake -S compiler/adapters/llzk -B OTHER_BUILD` also works with the pinned
`LLVM_DIR`, `MLIR_DIR`, and installed or build-tree `LLZK_DIR`. Direct CMake defaults
to an `unverified` revision label. The existing `build.py --study PATH --work PATH`
helper builds against a read-only, pinned external LLZK toolchain tree (`--study`)
into a separate directory (`--work`). It checks the selected source and
exported package paths, supplies the declared revision, and hashes actual linked
libraries and generated headers. Those hashes do not prove source-to-binary
provenance.

The lower-level CLI is:

```text
zkc-llzk SOURCE --field NAME --entry SYMBOL --outputs CSV --public-inputs CSV --output NEW_DIRECTORY
```

`SYMBOL` is the exact qualified source entry, for example `Transfer_5::Transfer_5`.
CSV order must match the source declarations; this is not a request to reorder
them. For an unnamed argument use `#N`, its zero-based position excluding self.
Named arguments use their exact `function.arg_name`. An explicit empty CSV is
allowed by the interface parser, but the pinned R1CS dialect requires at least
one public output signal; input-only circuits are not supported by this route.
Top-level inputs and outputs must be scalar. Internal component arrays and PODs
are supported only when normalization removes them from the constraint body.

`bls12381` is BLS12-381 Fr. `bn254` is the BN254 scalar modulus; the standalone
exporter supports it, but the current native compiler rejects it as an uninstalled
field. No numeric retargeting is performed. An exact field selection cannot
change a conflicting source type or field declaration.

## Admission sequence

1. Read at most 2 MiB of text, parse with registered MLIR/LLZK operations, and
   reject parse diagnostics. Bytecode and unregistered dialects are excluded.
   A missing BLS definition is registered using `llzk::Field::addField` with the
   exact known modulus before a fresh parsing attempt. Self-declaring sources
   are parsed first because upstream rejects even identical redeclarations.
2. Check every used field and every typed field specification. Reject effectful
   include/global/RAM/verifier dialect operations before operation verification.
   Verify the module. Then walk **every source operation before any lowering**:
   only equality constraints, the enumerated arithmetic/structural subset,
   defined component calls, and statically proven true assertions are admitted.
   In particular, containment is refused even in a dead branch. An assertion
   proof is limited to an `i1` true constant or a comparison of two felt constants.
3. Check the source main and its ordered public interface against the explicit
   configuration. Fully inline components before demoting their public members:
   component public visibility also controls access inside LLZK.
4. Print the adapter's own inlined IR and reparse it into a fresh LLVM20 context.
   Same-context normalization leaves unresolved array reads on the transfer
   fixture. Validated field registration survives at process scope. The final
   normalized BLS snapshot receives a typed, exact field declaration.
5. Run upstream full polynomial lowering with maximum degree two. Admit exactly
   one scalar constrain block: `felt.const/add/sub/mul/neg`, local scalar
   `struct.readm`, `constrain.eq`, operand-free return, known integer constants,
   and provably true `bool.assert`. Reject residual regions, arrays, calls,
   offsets, assertions, and all other operations. Recheck the public interface.
6. Run upstream R1CS lowering and the upstream binary exporter directly. Do not
   run final CSE: it can delete an unused public signal, breaking zero-equation
   interfaces. Direct binary export avoids the standalone translator's missing
   felt dialect registration; it needs no text-based field-attribute removal.
7. The Python entry point calls native `relation-read` and `relation-inspect`,
   checks public counts, and records the canonical target identity. It never
   parses MLIR. No witness execution participates in admission.

The per-process bounds are 2 GiB address space, 45 CPU seconds, 100,000 operations
at stage boundaries, region nesting at most 64, and 16 MiB per emitted artifact.
An iterative textual preflight limits nesting to 64 before recursive MLIR parsing,
including reparsing the adapter's own normalized source.
The Python entry point imposes a 60-second subprocess timeout. These bounds and
process isolation contain resource use; they are not a claim that the upstream
parser is memory-safe. Signals/timeouts refuse the import without a published
native bundle. The low-level CLI may leave partial output on an I/O failure;
callers must require exit zero. Neither entry point overwrites an existing output
directory.

## Output and claims

The standalone tool writes `normalized.llzk`, `relation.r1cs` and `receipt.json`.
The wrapper adds the exact source snapshot, canonical `relation.json`, and
`native-binding.json` with the native subject and tool hashes. The receipt records
source/main/field/public layout, demotions, pipeline choices, and artifact hashes.
`normalized_members` and `normalized_arguments` describe the normalized LLZK
stage; they are not a general final R1CS wire map when lowering adds auxiliaries.

The relation's assignment is `[ONE, public outputs, public inputs, private wires]`.
Even zero equations require `ONE = 1` and equality between the supplied statement
and the public prefix. `compute` is witness-generation code and cannot supply
acceptance constraints. The zero-equation test deliberately accepts a bound
assignment that disagrees with its compute function.

Trust still includes the pinned frontend, parser/verifier, LLZK normalization,
R1CS conversion/export, native reader and the explicit source/interface binding.
The source guard closes the demonstrated containment-erasure route; it does not
prove universal upstream preservation. Receipts do not prove source adequacy,
cryptographic soundness, zero knowledge, or proof-backend conformance. The native
identity describes the canonical target representation, not semantic equivalence
of arbitrary circuits. Different frontend runs may produce different source
bytes or private-wire order.

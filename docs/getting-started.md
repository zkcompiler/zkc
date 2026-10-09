# Compile and verify a protocol

This walkthrough compiles the [Schnorr library](../libraries/schnorr/lib.zkc)
and its [Entry](../examples/projects/schnorr/main.zkc), then produces and verifies
a proof in separate processes. The library defines the group equations, messages
and random draws. The Entry chooses participants, public inputs and a transcript
construction. The common Host supplies randomness and executes compiled programs.

## Prepare the tools

Follow the [development guide](development/README.md) to enter the pinned
environment and build the tools. Run these commands from the repository root:

```sh
nix develop
just setup
just demo
```

`just demo` builds its tools, compiles this source and reports `Proof accepted`
and an output directory. That directory contains the authenticated Entry package,
`proof.bin`, and separate producer/validator reports. The full integration suite
is separate from the demo.

The checked-in inputs contain a deliberately public witness, scalar 3, with the
standard BLS12-381 G1 generator and its scalar multiple. They demonstrate the
compiler and Host, and must not be used as secret application data. Each proof
call obtains fresh randomness from the common runtime.

## Follow each boundary

After building, the same steps are:

<!-- executable: source-proof -->
```sh
demo_dir=$(mktemp -d)
compiler="${ZKC_COMPILER_BIN:-build/compiler}/zkc-compile"
native="${ZKC_NATIVE_BIN:-${CARGO_TARGET_DIR:-target}/release}"

"$native/zkc" compile --compiler="$compiler" \
  --module=schnorr=libraries/schnorr/lib.zkc \
  --module=example=examples/projects/schnorr/main.zkc \
  --entry=example::Proof --output="$demo_dir/proof.entry" \
  > "$demo_dir/build.json"
pin=$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["package_sha256"])' "$demo_dir/build.json")
"$native/zkc" prove "$demo_dir/proof.entry" "$pin" \
  examples/projects/schnorr/prover.json "$demo_dir/proof.bin" \
  > "$demo_dir/producer.json"
"$native/zkc" verify "$demo_dir/proof.entry" "$pin" \
  examples/projects/schnorr/verifier.json "$demo_dir/proof.bin" \
  > "$demo_dir/validator.json"
cat "$demo_dir/validator.json"
printf '\nDemo files: %s\n' "$demo_dir"
```

The expected package hash comes from this trusted compilation. A deployed
application stores that authorization separately; hashing an incoming package
does not establish trust. The verifier reads public inputs and the proof without
the witness or a running prover. A produced proof is accepted only after the
verifier's actual terminal equation succeeds.

The compiler retains the mathematical original, source interface, compilation
options and participant artifact. It independently compares emitted MLIR with
the checked source. The Rust Host authenticates this publication, binds its named
interface to the native artifact, and admits the participant programs. This path
has bounded tests and compiler checks; native Lean correspondence and a security
theorem for this complete executable path remain separate work.

## Write and run another Entry

| Task | Continue with |
|---|---|
| Understand types, helpers, roles, services and control | [Mathematical source guide](language/mathematical.md) |
| Compile reusable libraries with separate clients | [Source projects](../examples/projects/README.md) |
| Inspect a repeated protocol with a real terminal check | [Public Sumcheck](../examples/projects/sumcheck/README.md) |
| Supply named inputs, setup authority, limits or Rust bindings | [Entry execution](runtime/entries.md) |
| Read exact source semantics | [Source profile](spec/language/README.md) |
| Extend the compiler or runtime | [Extension guide](development/extensions.md) |

`zkc --help`, `zkc COMMAND --help`, `zkc-compile --help` and `zkc-opt --help`
describe installed commands. `--version` reports manifest versions; record the
source revision separately when comparing builds. Help/version do not read
protocol inputs. Unknown commands exit 2; execution refusals return structured
JSON and exit 1. Inspect the reported outcome and acceptance, not just proof
production.

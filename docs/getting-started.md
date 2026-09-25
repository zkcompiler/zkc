# Compile and verify a protocol

This walkthrough runs the [committed two-factor argument](../examples/protocols/committed-two-factor.pir).
It proves a product-sum claim about two selected polynomial commitments. The
source commits both tables, compares the commitments with the verifier's public
inputs, runs Sumcheck, opens each original polynomial at the derived point, and
checks the terminal product. Those steps are authored protocol code, not a call
to an opaque whole-protocol prover.

## Prepare the tools

Use the [development guide](development/README.md) to enter the pinned environment and
build the compiler, Rust tools/examples and Lean checkers. Run commands below
from the repository root. The first setup downloads dependencies; a prepared
checkout needs no dependency update to run the demo.

```sh
nix develop
just doctor
just setup
just build
just demo
```

The final line reports `Proof accepted: 1514 bytes` for this rank-three example
and prints the output directory. `producer.json` reports `produced`,
`validator.json` reports `accepted`, and `proof.bin` contains the proof. Each
invocation has a fresh report directory. The full test suite is separate from
this first run; its resource requirements are in the development guide.

The demo explicitly generates development keys and known-witness inputs using
the maintained `artifact_fixture` example. The PCS is nonhiding. This is a
working compiler/execution example, not a production setup, a zero-knowledge
claim or a general Fiat–Shamir security proof.

## Follow each boundary

The source's [construction descriptor](../examples/protocols/committed-two-factor.construction.pir)
selects producer and validator roles, the public inputs, the challenge site,
the acceptance result and the installed Merlin suite. The compiler constructs
the transcript-based common program and compiles its participants. The host
rechecks construction with the compiler and checks the participants with Lean
before execution. See [artifact assurance](compiler/artifact-execution.md#what-is-checked-tested-and-proved)
for the exact distinction between these checks and a security theorem.

To run the same path explicitly, after building the tools:

<!-- executable: committed-proof -->
```sh
demo_dir=$(mktemp -d)
compiler="${ZKC_COMPILER_BIN:-build/compiler}/zkc-compile"
native="${ZKC_NATIVE_BIN:-${CARGO_TARGET_DIR:-target}/release}"
checker="${ZKC_LEAN_BIN:-formal/.lake/build/bin}/interactive-protocol"
source=examples/protocols/committed-two-factor.pir
descriptor=examples/protocols/committed-two-factor.construction.pir

"$native/examples/artifact_fixture" "$demo_dir/inputs"
"$compiler" protocol-source "$source" > "$demo_dir/source.json"
"$compiler" protocol-source "$descriptor" > "$demo_dir/descriptor.json"
"$compiler" protocol-construct "$source" "$descriptor" > "$demo_dir/construction.json"
python3 -c 'import json, sys; print(json.dumps(json.load(open(sys.argv[1]))[2]))' \
  "$demo_dir/construction.json" > "$demo_dir/common.json"
"$compiler" protocol-compile "$demo_dir/common.json" > "$demo_dir/participants.json"

"$native/zkc" produce-artifact \
  "$demo_dir/source.json" "$demo_dir/descriptor.json" \
  "$demo_dir/construction.json" "$demo_dir/participants.json" \
  "$demo_dir/inputs/committed-two-factor.producer.json" \
  "$compiler" "$checker" "$demo_dir/proof.bin" 10000 --trace=none \
  > "$demo_dir/producer.json"
"$native/zkc" validate-artifact \
  "$demo_dir/source.json" "$demo_dir/descriptor.json" \
  "$demo_dir/construction.json" "$demo_dir/participants.json" \
  "$demo_dir/inputs/committed-two-factor.validator.json" \
  "$compiler" "$checker" "$demo_dir/proof.bin" 10000 --trace=none \
  > "$demo_dir/validator.json"
cat "$demo_dir/validator.json"
printf '\nDemo files: %s\n' "$demo_dir"
```

`protocol-source` emits explicit JSON for current host/checker consumers; authors
write `.pir`. The third construction-array entry is the constructed common
program. The descriptor, original source and construction are retained so that
the host can check the actual transformation inputs. `10000` is a transcript
transition budget, not a security parameter. `--trace=none` omits observations
from the report without skipping verification.

The two host commands are separate processes. The validator uses public inputs,
verification material and candidate proof bytes; its input file contains no
private polynomial tables or proving key. A wrong selected commitment or
truncated proof is refused. Proof production alone is not verifier acceptance.

## Find the next path

| Task | Continue with |
|---|---|
| Understand or change the protocol source | [Source notation](language/reference.md), then [protocol examples](../examples/protocols/README.md) |
| Separate reusable code from its caller | [Source projects](language/projects.md) and [library clients](../examples/projects/README.md) |
| Inspect elaboration, types and requirements | [Source analysis](compiler/frontend.md) |
| Run a contrasting AIR/FRI family | [AIR and oracle examples](../examples/protocols/air-oracle/README.md) |
| Use an external R1CS and Groth16 | [Relation authoring](language/relations.md) and [pinned interoperability reproduction](../tests/groth16/README.md) |
| Extend the compiler or backend | [Extension guide](development/extensions.md) |
| Use definitions and proofs independently | [Formal library](../formal/README.md) and [support map](../formal/SUPPORT.md) |

## Discover commands

`zkc --help`, `zkc COMMAND --help`, `zkc-compile --help` and `zkc-opt --help`
describe their installed commands. Each tool supports `--version`; the compiler
tools also identify their LLVM version. The compiler and Rust tools have separate
package versions (`0.1` and `0.1.0` respectively); they are not synchronized release
identifiers. Versions come from package manifests, not Git history, so record the
source revision separately when comparing runs.

Help/version requests return zero without reading protocol inputs. Running
`zkc` without a command, or with an unknown command, reports usage on stderr and
exits 2. Execution commands
retain their JSON reports and failure classification; inspect their status and
acceptance result, not only a successful process exit. See the
[host guide](../crates/zkc-tools/README.md) for execution outcomes.

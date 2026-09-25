# Protocol examples

Start with the [committed proof walkthrough](../../docs/getting-started.md).
`just demo` runs that source through construction, proof production and independent
validation using explicit development fixtures. The interactive commands below
are a smaller example of participant execution.

Author and read the `.pir` files. They use `let` bindings, qualified operation paths,
`::<...>` static arguments and logical types such as `F::Element`. The compiler
resolves and elaborates them before common-source admission.
The adjacent JSON files contain the elaborated explicit source for current consumers and
regression checks; the frontend test detects disagreement between each pair.
See the [notation guide](../../docs/language/reference.md) for grammar,
diagnostics, formatting and construction descriptors.

| Source | Use |
|---|---|
| [inferred-calls.pir](inferred-calls.pir) | Domain inference and ordinary helper-call syntax |
| [execution-proof.pir](execution-proof.pir) | Bounded execution argument with R1CS reduction, nested Sumchecks and original-polynomial openings; not a complete production zkVM |
| [confidential-transaction.pir](confidential-transaction.pir) | Composed range/IPA, balance and owner-knowledge argument; application and ledger assumptions remain explicit |
| [checked-variants.pir](checked-variants.pir) | Checked finite variants and matching through source lowering |
| [checked-components.pir](checked-components.pir) | One interface-checked client linked with empty affine and Boolean state representations; normal execution and stopped guards through Lean and Rust |
| [committed-two-factor.pir](committed-two-factor.pir) | Complete composition: commitments pinned by the validator, product Sumcheck, two opening calls and a terminal check |
| [linear-relation.pir](linear-relation.pir) | Repeated committed-vector linear constraints, with generic group/field algorithms and every matrix coordinate checked |
| [dleq.pir](dleq.pir) | Complete group-based composition: repeated two-base discrete-log equality with distinct private nonces |
| [groth16.pir](groth16.pir) | Groth16 over a compiled R1CS with snarkjs-compatible keys, written with a constraint bundle, operators, key and proof structs, and checked bound and satisfied assignments; [expanded twin](../../tests/fixtures/groth16-expanded.pir) |
| [two-factor.pir](two-factor.pir) | Earlier executable product argument over prover-selected tables; no expected-root pinning |
| [group-exchange.pir](group-exchange.pir) | Small executable BLS G1 exchange, without a cryptographic security claim |
| [folded-contraction.pir](folded-contraction.pir) | Generic numerical folding and weighted contraction instantiated at Plonky3 KoalaBear; no proof-system claim |
| [domain-family.pir](domain-family.pir) | Whole-protocol domain selection and named static constants; small field echo client |
| [folded-contraction-family.pir](folded-contraction-family.pir) | One polynomial interaction family selected at KoalaBear or BLS scalar field |
| [group-agreement-family.pir](group-agreement-family.pir) | One group-valued message family selected at supported BLS/BN254 groups; no proof-system claim |

The `*.construction.pir` files specify public-artifact construction for the
matching source. Runtime inputs use the [host input contract](../../docs/runtime/inputs.md#input-format), `zkc.run/2`; `supplied-participant.json` uses explicit physical
bindings.

## Compile and run an interactive source

Build the [compiler, Rust host and Lean checker](../../compiler/README.md#interactive-protocol).
From the repository root:

```sh
build/compiler/zkc-compile protocol-admit examples/protocols/two-factor.pir
build/compiler/zkc-compile protocol-compile examples/protocols/two-factor.pir > /tmp/two-factor-participants.json
build/compiler/zkc-compile protocol-source examples/protocols/two-factor.pir > /tmp/two-factor-source.json
target/release/zkc run-protocol /tmp/two-factor-source.json \
  /tmp/two-factor-participants.json examples/protocols/two-factor.inputs.json \
  formal/.lake/build/bin/interactive-protocol
```

`protocol-parse` is tagged syntax inspection, not the host input format.
The host still reads admitted common JSON. `protocol-source` generates its input; no manual JSON
authoring is required. This example uses the existing development setup policy.
For a real G1/nonce smoke test, substitute `group-exchange` in the commands.

For the numerical Plonky3 example, substitute `folded-contraction`. Its input
fixture folds `[1,2,3,4]` and `[5,6,7,8]` at 2, producing `[5,6]` and `[9,10]`.
The weighted contraction is `2*5*9 + 3*6*10 = 270`. The checker supplies that
expected result. The generic functions retain their actual algorithms; the
configuration selects `koala-bear`, and physical planning selects installed
implementations. This is an executable interaction testing the numerical path,
not a cryptographic argument that the worker computed correctly. There is no
KoalaBear transcript or PCS installation in this example.

## Construct a proof producer and validator

```sh
build/compiler/zkc-compile protocol-construct \
  examples/protocols/dleq.pir examples/protocols/dleq.construction.pir \
  > /tmp/dleq-construction.json
build/compiler/zkc-compile protocol-check-construction \
  examples/protocols/dleq.pir examples/protocols/dleq.construction.pir \
  /tmp/dleq-construction.json
```

Continue with the [artifact execution guide](../../docs/compiler/artifact-execution.md#running-the-path)
to compile the constructed common program and run the independent processes.
Normalize the original `.pir` source and descriptor with `protocol-source` for
the Rust host's original-source inputs.

## Composable components

[`arithmetic-trace.pir`](arithmetic-trace.pir) contains a commitment, outer and
inner Sumchecks, and original-assignment openings. Its dense public matrices are
application-owned. [`aggregated-range.pir`](aggregated-range.pir) contains the
range equation and a reusable IPA dependency with its complete message/terminal
sequence.

Both examples have construction descriptors and run with actual Arkworks/Dalek
kernels.

## Local algorithm control

[`polynomial-fold.pir`](polynomial-fold.pir) is an executable local algorithm
example, not a proof system. It demonstrates input-length iteration, nested
helper calls, checked indexing and conditional state updates. The Groth16
verifier uses vector literals to assemble its pairing equation. See the
[local-control design and validation](../../docs/compiler/local-control.md).

## Editing and checking

```sh
build/compiler/zkc-compile protocol-format examples/protocols/dleq.pir > /tmp/dleq-formatted.pir
build/compiler/zkc-compile protocol-format-check examples/protocols/dleq.pir
ctest --test-dir build/compiler -R '^frontend-' --no-tests=error --output-on-failure
```

Formatting preserves comments and all explicit identifiers. Review a formatted
temporary file before replacing the original. If intentionally changing a maintained
example's meaning, regenerate its JSON counterpart with `protocol-source` and
update the corresponding expectations; do not retune a frozen evidence fixture
to hide a disagreement. For new protocol development, a single `.pir` file is
sufficient; the paired files here check text-to-explicit normalization.

## External construction and attempts

[external-constructions.pir](external-constructions.pir) exercises the installed
Monero hash-chain and OpenVM duplex transitions. The
[Monero schedule](external-monero-schedule.pir) and
[OpenVM schedule](external-openvm-schedule.pir) retain caller-authored event
loops and run archived upstream checkpoints.
[external-family.pir](external-family.pir) composes the duplex transitions with
input-selected protocol counts in one compact compiled body. The state is checked immutable
data, with no automatic prefix or proof-container observation. See the
[transition contract](../../docs/spec/realization/external-constructions.md).

[attempt-control.pir](attempt-control.pir) is a compiled retry-driver fixture:
it consumes real issued randomness and returns an explicit retry flag. The host
buffers its typed messages, discards failed-attempt output, and applies a codec
to the completed attempt. It is not a cryptographic proof system. Input-selected
protocol counts are demonstrated in the
[input-family fixtures](../../tests/fixtures/input-families/private-inputs.pir).

# Native relations and composition

[Static composition](../spec/profiles/compiler/protocol-composition.md) owns the
implemented semantics and limits. This page records the design and how to run it.

## Use

Run from the repository root after the
[native build](../development/README.md). These commands assume
`build/compiler` is on `PATH` and the named input files are supplied by the caller.

```sh
zkc-compile relation-protocol circuit.json > circuit.mlir
zkc-compile relation-requirements circuit.json > requirements.json
zkc-compile protocol-checked-bundle circuit.mlir \
  --requirements=requirements.json --entry=main > checked.json
```

The input also accepts the existing bounded R1CS v1 binary container. Its exact
modulus selects the field. The native client currently requires BLS12-381 Fr;
it refuses a BN254 asset rather than reinterpreting its constants.

C++ users link `Zkc::Translation` and include `zkc/Translation/Relations.h`.
`authorR1CSSumcheck` consumes an immutable canonical `R1CS` and an MLIR context
with the registered mathematical interfaces. It creates `recipe`, `reduction`,
`terminal`, `evaluate` and composed `main` definitions. The separate
`r1csSumcheckRequirements` consumes the external relation, never candidate IR.
Use the existing native compiler API to check and compile the chosen entry.
The `evaluate` entry uses ordinary unchecked native compilation: its exact
arithmetic is validated against independent relation evaluation in tests.

The generated source is intentionally a bounded reference client. Matrices are
specialized into existing field operations and arrays. No new relation opcode,
polynomial representation or runtime protocol scheduler is needed. A later bulk
matrix kernel requires workloads that distinguish it from this reference path.

## Why static application

`protocol.apply` has an explicit interaction interface. Pure `func.call` remains
restricted to total mathematics; it cannot hide queries, communication or stops.
Both use standard MLIR symbols and SSA. A protocol application additionally
substitutes roles and preserves the declared availability boundary.

Separately executing reduction and terminal bundles would require another
contract for entry selection, role mapping, actual value handoff, service state
and failure propagation. This adapter has a static caller, so expanding its
calls preserves all of those through the existing participant/runtime route.
The public-table and imported R1CS clients both use the same mechanism.
Dynamic composition and separately deployed participants remain different future
requirements, rather than implicit properties of this implementation.

The checker extends independent requirements with an actual application binding.
It checks exact composition against the retained source. For R1CS it additionally
requires source produced for the independently supplied relation. This keeps the
adapter trust boundary visible and avoids a new proof-obligation language whose
laws have no additional consumer yet. Algebraically equivalent source or
composed candidates can refuse; general transfer certificates remain open.

## Mathematical choice and controls

The weighted residual construction follows the R1CS reduction in
[Spartan, section 4](https://eprint.iacr.org/2019/550.pdf). The weight prevents an
unweighted cancellation test from being mistaken for relation satisfaction.
The formal product of MLEs differs from the MLE of rowwise products outside the
Boolean cube, so the terminal and prover use the same formal recipe. Independent
transcript tests use non-Boolean, asymmetric weights and round challenges.

The main assignment is constructed from ONE, statement and witness coordinates.
This removes redundant binding guards from that entry. The exact evaluator keeps
explicit assignment binding so invalid ONE and public-prefix cases remain
independently testable. The witness is available to Checker in this client; the
terminal can therefore evaluate the relation data itself. Private PCS and
sublinear verification are not implemented by this adapter.

`compiler/test/relation_composition.py` generates checked bundles and independent
arithmetic expectations. `crates/zkc-tools/examples/relation_composition.rs`
executes those bundles with the real native backend. The cross-language test
selects both together. After the
[test prerequisites](../../tests/README.md#selecting-checks), run that joined case
from the repository root:

```sh
uv run pytest tests/protocol/test_native_mathematical.py -k relation_composition
```

The generator emits `execution.json` and its bundles. The Rust example accepts
that generated directory and checks every recorded execution and refusal.
Mutation controls change same-typed residuals, the composed
decision, source coefficients, weight sites and relation layout. Runtime controls
cover accepted/rejected weighted claims, known bad events, returned false,
malformed coefficient frames, service exhaustion and driver limits.

## Reopen when

- A real consumer needs separately deployed or dynamically selected components:
  design a runtime composition contract, including services and failure cleanup.
- A required source or candidate transformation changes the exact recognized
  structure: compare a typed semantic adapter or checked transfer record with a
  narrower structural extension. Do not broaden acceptance by trusting metadata.
- A larger relation exceeds scalar work limits: compare sparse/bulk kernels and
  array construction costs against this independent reference.
- A private witness client is selected: design commitments, terminal evidence and
  the challenge experiment before claiming a private argument.
- The native interface is stable enough for formalization: connect application,
  role substitution and polynomial reduction to Lean; existing tests do not
  supply that theorem.

MLIR references: [symbols and symbol tables](https://mlir.llvm.org/docs/SymbolsAndSymbolTables/)
and [inlining interfaces](https://mlir.llvm.org/docs/Interfaces/). Generic pure
inlining does not by itself establish the role substitution contract.

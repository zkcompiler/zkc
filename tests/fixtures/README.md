# Shared test fixtures

Fixed inputs and expected results shared by the C++ compiler, Rust runtime,
Lean reference and cross-language tests. Benchmarks may reuse them too.
[Examples](../../examples/) show how to use zkc; this corpus includes valid
programs, deliberately invalid inputs and independent known-answer vectors.
Generated run outputs belong under ignored `build/` directories.

## Contents and consumers

| Files | Purpose and principal consumers |
|---|---|
| Top-level `.pir`, source JSON and descriptors | Local algorithms, generic bindings, composition, construction and storage; [compiler tests](../../compiler/test/), [protocol tests](../protocol/) and [execution tests](../execution/) |
| `preservation-baseline.json` | Frozen canonical source and constructed-artifact hashes, checked by [frontend preservation](../../compiler/test/frontend_preservation.py) |
| `air/` | Finite AIR relations and traces, including invalid degree, field and boundary cases; [AIR controls](../../compiler/test/air_ir.py) |
| `blocks/` | Block-checker inputs and expected outcomes; [formal tool checks](../../formal/checks/check_tools.py) |
| [`identity-vectors/`](identity-vectors/README.md) | Handwritten expected identities and their source/descriptor inputs; [Rust/Lean comparison](../identity/test_identity_reference.py) |
| [`input-families/`](input-families/README.md) | Bounded input-selected protocols and shared refusal names; [family controls](../protocol/test_input_families.py) and runtime admission |
| `refusal-agreement/` | Source mutations and agreed refusal identifiers; [three-implementation comparison](../protocol/test_refusal_agreement.py) |
| `variants/` | Descriptor cases and history-transition inventory, independently checked by C++, Rust and Lean |
| `transcript-kat.json`, `transcript-vectors.json` | Frozen transcript encodings and challenge expectations; native primitive tests |
| `external-transcript/`, `external-constructions.json` | Archived upstream proofs and transcript checkpoints, plus primitive reply tables for Lean replay; [native controls](../../crates/zkc-backends/tests/external_transcript.rs) and [cross-language controls](../protocol/test_external_constructions.py) |
| [`archived-shapes/`](archived-shapes/README.md) | Archived OpenVM proofs, decoded metadata, keys and pinned provenance; [shape controls](../protocol/test_archived_families.py) |

The compiler's `support/tools.py` and Rust's `zkc_test_support::corpus()`
resolve this shared directory. Component-specific inputs stay beside their
tests, such as `crates/zkc-tools/tests/fixtures/artifact/`.

## Maintaining the corpus

- Identify a consumer when adding a fixture. Check dynamic filename selection
  and all three languages before treating a file as unused.
- Preserve independent expected values and deliberately invalid cases. Equal
  bytes do not make two separately named cases redundant.
- A file move may update paths in `preservation-baseline.json`; its expected
  hashes must remain unchanged. A semantic change needs separate justification.
- Preserve archived proof bytes and provenance hashes. The
  [transcript generators](../external-transcripts/README.md) rebuild replay
  schedules and primitive reply tables; the
  [shape archive guide](archived-shapes/README.md) records extraction limits.
  Neither supplies a general security or conformance claim.

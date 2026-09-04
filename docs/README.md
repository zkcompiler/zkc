# zkc documentation

This directory is the public reading map. Authority is separated by kind so
that implementation evidence, future plans, and normative semantics are not
mistaken for one another.

## Start here

| Question | Document |
|---|---|
| What is zkc, and what direction does it pursue? | [Project Overview](overview.md) |
| What does the current checkout claim? | [Current Status](status.md); the [Repository README](../README.md) is a summary |
| How does the target architecture fit together? | [Architecture](architecture.md) |
| How does zkc relate to relation compilers, formal systems, backends, and zkVMs? | [Ecosystem](ecosystem.md) |
| How do I build it? | [Getting Started](getting-started.md) |
| Where does the build fall short of the specification? | [Gap Ledger](gap-ledger.md) |
| What comes next? | [Roadmap](roadmap.md) |
| What are the exact artifact and judgment semantics? | [Specification Overview](spec/overview.md) |
| What formal evidence is currently recorded? | [Formalization Evidence](formalization.md) |

[Project Overview](overview.md) explains the stable project model and target
direction without reporting current implementation support.
[Architecture](architecture.md) is the non-normative target guide to system
layers, artifact lifecycle, and trust boundaries; it intentionally includes
unimplemented parts of the target design. [Ecosystem](ecosystem.md) applies
those generic boundaries to concrete external projects without making a
compatibility claim. [Current Status](status.md) owns the public capability and
evidence dashboard. The setup guide owns the normal development workflow, while
the roadmap owns dependency order; neither overrides the specification.

## Normative specification

The current specification corpus is:

- [Protocol Kernel](spec/kernel.md)
- [Soundness Kernel](spec/soundness.md)
- [Compiler Core](spec/compiler.md)
- [Vocabularies](spec/vocabularies.md)
- [Relations](spec/relations.md)
- [Boundaries](spec/boundaries.md)
- [Endpoints](spec/endpoints.md)
- [Carrier](spec/carrier.md)
- [Versioning and diagnostic allocation](spec/versioning.md)

[Specification Overview](spec/overview.md) is the compact reading map. The
individual specifications own intended semantics. Implementations and tests
are conformance evidence; registry JSON and encoded artifacts remain subject
to the validation and identity rules those specifications define.

## Formalization evidence

[Formalization Evidence](formalization.md) explains the receipt and drift
checks attached to Soundness Kernel rules, the pinned formalization readings,
and the conditions for theorem-backed admission. The
machine-readable annotations and pin files remain authoritative for their own
contents; the document does not override the specification.

## Evaluation and evidence records

- [Evaluation overview](../evaluation/README.md) — active integration evidence
  and the provenance of source-derived regression fixtures.
- [Pinned Plonky3 replay/prover harness](../evaluation/upstream/plonky3-replay/README.md)
  — current fixture-scoped upstream evidence.
- [FRI generation benchmark record](../evaluation/fri-bench/RECORD.md) —
  measured wall-clock and allocation evidence for one emitted prover against
  the pinned upstream prover, scoped to its named machine, revision, and
  instance.

These records preserve the exact scope and residual trust of experiments. They
do not override [Current Status](status.md), mint general backend conformance,
or define protocol semantics.

## Documentation rules

1. Current public capability and evidence claims belong in `status.md`; future
   direction belongs in `roadmap.md`.
2. Exact schemas, judgments, identities, and refusal rules belong in `spec/`.
3. A demonstrated run establishes only the facets and fixed inputs it records.
4. Soundness, completeness, zero knowledge, relation satisfaction, backend
   conformance, and implementation correctness are separate claims.
5. A placeholder, proposal, citation, receipt, or passing test does not acquire
   stronger authority through proximity or detail.

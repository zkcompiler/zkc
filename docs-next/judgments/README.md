# Property judgments

> **Document kind:** Domain index
> **Document state:** Scaffold
> **Provisional owner:** `judgments`
> **Authority:** None during the transition. Current property calculus remains
> governed principally by the [Soundness Kernel specification](../../docs/spec/soundness.md).

## Purpose

`judgments/` owns reusable post-seal analysis of properties of exact,
authenticated subjects. Its center is a typed calculus of subjects, indices,
rules, hypotheses, derivations, and exact results—not a generic home for every
check or inference rule in zkc.

The directory may later be renamed `analysis/` or `property-judgments/` if the
short name continues to imply broader ownership.

## Owns

- exact property subjects and analysis sites;
- security tracks and notions, including soundness and knowledge variants;
- completeness as a separate property track over shared typed machinery;
- future zero-knowledge or correspondence tracks only if they fit the same
  subject and derivation model;
- typed result schemas, exact quantities, bounds, and resource variables;
- hypotheses, assumptions, external propositions, and inherited obligations;
- rule and signature schemas, premise bindings, catalogs, and application;
- explicit derivation plans and independently re-checkable results; and
- authenticated projection from admitted domain objects into property facts.

## Does not own

- PIR formation, `WF`, linearity, binding, closure, seal, or link;
- relation interface correspondence merely because it is written as a
  judgment;
- compiler `DOMAIN`, legality, scoring, selection, or decision checking;
- endpoint validity, projection coverage, or execution verdicts;
- the truth of an external theorem or hypothesis named by a rule;
- formalization receipts, tests, or conformance observations; or
- a universal “verified” state that collapses distinct properties.

## Dependencies

- `foundation/` for exact identity, authority, and admission mechanics;
- `pir/` for authenticated protocol subjects, structural facts, claims,
  reductions, rounds, and obligations; and
- `relations/` for any exact relation facts admitted into a property subject.

The calculus must not read mutable or producer-asserted mirrors where its
contract requires facts reconstructed from an authenticated subject.

## Consumers and outputs

- `compiler/` consumes typed results and derivation capabilities in constraints
  and objectives without reimplementing their meaning;
- `project/` may summarize supported property tracks through global status;
- `evidence/` records receipts, source readings, parity, and checks supporting
  implementation or theorem-correspondence claims; and
- guides explain how to request and interpret a result.

A property result remains conditional on its stated hypotheses and exact
subject. Consumers cannot widen the subject or erase inherited obligations.

## Bridge ownership

`judgments/` owns admitted-subject-to-property-view projection and the
derivation result it enables. The producing domain owns each exported fact's
definition. Judgment consumption in compiler constraints belongs to
`compiler/`, which must cite result meaning rather than restate it.

## Candidate internal topics

- common typed property calculus;
- subjects, sites, and authenticated fact adapters;
- security and knowledge judgments;
- completeness judgments;
- hypotheses and external propositions;
- exact bound algebra;
- rules, signatures, and catalogs; and
- derivations and result interpretation.

## Open boundary questions

- Is one common calculus genuinely adequate for soundness, knowledge,
  completeness, and future zero knowledge without hiding their differences?
- Which Fiat–Shamir obligations are PIR structure, which are cryptographic
  judgment premises, and which are endpoint conformance evidence?
- Should theorem-correspondence admission remain part of rule semantics while
  receipts and drift checks move entirely to evidence?
- Does the term `judgments` remain usable once domain-local judgments are
  explicitly excluded?

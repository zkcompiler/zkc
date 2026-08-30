# Oracle and Polynomial-Commitment Semantics

> **Kind:** Temporary semantic research-package charter, decision, and
> inventory
> **State:** Complete at T2; source reconstruction, architecture selection,
> durable promotion, and bounded closure checks are complete
> **Authority:** None. This package records comparative research. It cannot
> define PIR, establish a cryptographic property, authenticate a setup, or
> report implementation support.
> **Entry baseline:** The retained native FRI/IOR case fixes one bounded
> logical-Oracle-to-Merkle construction, exact public replay, and one-run
> validation. It is a regression anchor, not a universal PCS interface.
> **Deletion trigger:** Delete this package after every accepted definition,
> source caveat, nonclaim, and deferred question has one durable owner.

## 1. Question and result

This package asks whether the retained Oracle-commitment construction, the
zero-knowledge binary-field IOPCS of ePrint 2025/1015, and KZG single and
batched openings should inhabit one universal construction.

The answer is **no**. They share a small verifier-side typed shell:

```text
exact public setup assignment
                |
                v
explicit evaluation claim = (commitment, query, answer)
                |
                v
profile-local public evidence and verification coverage
                |
                v
independently admitted verifier Core and public replay
```

They do not share one opening algebra. The selected target keeps five
operations distinct:

1. Oracle authentication, including Merkle evidence packing and identical-
   answer sharing;
2. single-point KZG opening of one explicit evaluation claim;
3. one-polynomial, many-point KZG opening by a remainder polynomial;
4. same-point, many-polynomial KZG proof aggregation after a batching
   challenge; and
5. random-linear-combination verification of already formed opening
   equations after their proofs are fixed.

The binary-field IOPCS remains a complete interactive logical-Oracle Core. A
BCS/Merkle construction authenticates that Core; it does not manufacture its
Sumcheck, FRI, masking Oracle, or verifier challenges. KZG instead requires a
public commitment, explicit evaluation claim, proof evidence, and explicit SRS
assignment at the verifier boundary. Its private polynomial and producer
algorithm remain with Plan and Relations; they are not forced into a finite
enumerated Oracle or a new generic Core object.

## 2. Retained and reopened boundaries

Retain:

- `InteractiveCore` as the verifier-observable protocol subject;
- distinct source and independently admitted target Cores for Oracle
  authentication;
- exact profile and construction identity;
- process-local checked authority, public replay, and one-run receipts;
- PIR/Relations/Analysis/Evidence ownership separation; and
- Fresh versus Fiat--Shamir as challenge interpretations of an unchanged
  target Core.

Repair or reject:

- treating finite logical-Oracle authentication as a universal commitment
  interface;
- commitment algorithms with no explicit public-setup input;
- an opening proof as the source of its claimed answer;
- equality deduplication as the only evidence-coverage relation; and
- the phrase “batch opening” as though it named one construction.

## 3. Scope and non-goals

In scope are exact source reconstruction, setup and lifecycle ownership,
query/answer semantics, explicit claim and evidence separation, challenge
order, opening coverage, identity locality, public replay, and durable PIR
selection.

Out of scope are proofs of binding, hiding, extraction, zero knowledge,
soundness, knowledge, ROM/EPROM/QROM transport, ceremony integrity, toxic-
waste destruction, pairing implementation correctness, production suites,
OIR, backend realization, and current compiler migration.

## 4. Why the package remains T2

The assigned depth is architecture-level constructive validation. Exact source
traces and negative mutations distinguish the candidates without executing a
cryptographic implementation. A new toy evaluator would currently restate
the selected taxonomy rather than adjudicate an execution-sensitive
ambiguity. The retained `evaluation/native-fri-ior/` packet remains the
executable Oracle-authentication anchor.

Executable promotion becomes justified only if two candidate coverage laws
remain observationally indistinguishable, an admission algorithm has a
disputed first-failure boundary, or a later implementation claims concrete
correspondence.

## 5. Inventory

| Page | Role |
|---|---|
| [Source reconstruction](source-reconstruction.md) | Pinned primary sources, literal protocol anatomy, source inconsistencies, and current-model pressure. |
| [Architecture selection](architecture-selection.md) | Equal-resolution candidates, selected shared shell, family-specific constructions, identities, failures, and reversal conditions. |
| [Convergence and promotion](convergence-and-promotion.md) | Durable absorption map, closure evidence, residual obligations, classification, and next-package contract. |

## 6. Exit gate

The package closes only when:

1. the binary-field and KZG constructions are reconstructible from pinned
   primary sources, with inconsistencies recorded rather than normalized;
2. a public setup instance reaches every algorithm that needs it without
   becoming ambient state or private advice;
3. query answers, claims, and proof evidence have distinct typed roles;
4. Oracle authentication, claim aggregation, and verification aggregation
   cannot substitute for one another;
5. KZG is not forced through finite domain enumeration;
6. the binary-field construction creates no fictitious commitment for its
   virtual initial word and keeps its three randomness authorities distinct;
7. security and theorem conclusions remain Analysis questions;
8. accepted definitions are absorbed by durable owners; and
9. bounded regression and one independent architecture review find no package
   blocker.

All nine conditions pass at the stated T2 depth. This establishes only a
non-normative target model; it does not activate a cryptographic theorem or
claim implementation support.

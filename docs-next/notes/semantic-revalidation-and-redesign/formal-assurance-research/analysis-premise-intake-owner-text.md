# Analysis named-premise intake: the owner text

> **Kind:** owner-text record (formal-assurance research, Analysis pass)
> **State:** Authored 2026-09-03 on a branch stacked on the migration branch;
> both publication compilers agree; publication remains the user's gate.
> **Inputs:** the migration decisions on the sampling law and the outcome
> partition (`f0-v2c-decision-inputs.md`, Sections 4, 5, and 10) and the
> intake design of `analysis-named-premise-intake.md`.

## 1. Outcome

The two decisions that moved assumptions out of PIR now have their Analysis
side. A question names every assumption it consumes as a premise with an
identity; a missing premise makes the question `CannotAnswer`; two questions
over the same subjects with different premises have different identities down
to the judgment. Nothing in the pass proves a premise.

| Page | Change |
|---|---|
| `analysis-model.md`, Section 4.1 | the named-premise grammar (kinds, coordinates, bound values, sources, evidence depths, model scopes, body, requirement), the fields that carry premise identities through question, goal, hypothesis node and context, support, and judgment, the intake operation, the identity constructor, the dispatch row, and the binding-map law's new key class |
| `cryptographic-properties.md`, Section 3.2 | the Fresh public-coin distribution premise, the provider outcome-carrier premise over the abstract outcome partition, and the seven premise requirements of the relation-bound Fresh question over the Schnorr subject tuple |
| `cryptographic-properties.md`, Section 7.3 | the Fiat--Shamir family sampler-adequacy and oracle-process premises, scoped to one exact oracle model |
| `profile-publication.md` and the kernel, property, and transport manifests | the kernel owns grammar and intake; the property and transport profiles support `analysis.named-premise` and own the concrete bodies |

Both publication compilers reconstruct the same table; the Analysis kernel and
its five dependents rotate, on top of the migration's seventeen.

## 2. What was changed from the design

- Evidence depths are written out (source-grounded mapping, typed constructive
  binding, frozen executable falsification) instead of the research labels.
- The transport field is a model scope over defined vocabulary: a Fresh
  challenge, one exact distribution profile (the classical random-oracle
  profile of the adaptive experiment is one), exact subjects, or rebind
  required. The design's regime identifiers did not exist in the pages.
- The provider is an exact profile law declaration of the property profile,
  not a new declaration kind; no provider is declared yet, so no provider-map
  premise can be formed until one is published.
- The Plan coordinates carry ordinals into the Plan body rather than a
  strategy-step coordinate the pages do not define.
- The Schnorr entries are constructors over the subject tuple of Section 3,
  not literal digests.

## 3. What remains

- Publication, with the migration: the Analysis profiles rotate through the
  kernel.
- Migration of existing question, goal, context, proposition, support, and
  judgment bodies in the Analysis packages to the new fields, at the refreeze.
- A provider declaration for the first external formal system, which the
  provider-interpretation work supplies.
- An independent review of this text, as for the migration.

## 4. Non-claims

No distribution, sampler adequacy, oracle process, relation, honesty,
theorem applicability, completeness, security, or provider correspondence is
established; no identity is published.

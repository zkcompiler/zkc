# Candidate Comparison

## Candidate A: direct derivation at every use

Each protocol author could spell every source read and pure computation
directly in the Core.

This is executable and introduces no new authority, but it loses a reusable
logical identity, an exact logical-to-leaf map, and a stable coordinate for
Relations, Analysis, composition, and resource accounting. Equivalent source
formulas can also be elaborated inconsistently at separate sites without a
shared check.

**Disposition:** valid fallback, rejected as the common architectural answer.

## Candidate B: a virtual Oracle inside the Core

The Core could add a third Oracle origin whose answers are verifier-computed
from other Oracles.

This gives logical words a convenient nominal home, but it also forces new
answers, publication and observation rules, commitment treatment, lifecycle,
causality, replay, and potentially nested runtime effects into the only
executable protocol object. It obscures whether a paper's “virtual oracle” is
actually a protocol event or merely notation for verifier computation.

**Disposition:** rejected. The source families do not require that authority
or observation change.

## Candidate C: checked finite static query plan

Word programs and logical uses are identified separately. A bounded checker
recursively expands every finite route into ordinary guarded source-query,
answer, derived-value, and terminal atoms. The independently admitted flat
Core remains the sole runtime object. A total exact map retains the logical
coordinate and every ordered source leaf.

Benefits:

- reusable logical identity without a new executable authority;
- static causality, visibility, replay, and work bounds;
- distinct logical and source-leaf accounting;
- no change to Core authentication or Fiat--Shamir observations;
- commitment compilation remains rooted in actual source Oracles; and
- source correspondence can be checked later without repairing structure.

Costs:

- the complete branch expansion may be larger than one runtime path;
- answer-adaptive plans are intentionally excluded;
- compilers must preserve exact maps and cannot silently deduplicate reads; and
- paper-specific collision and fill semantics still require correspondence
  judgments.

**Disposition:** selected as the smallest shared boundary.

## Why the result is not generic composition

The plan expands one closed logical read language into Core atoms. It neither
executes child Cores nor retains child protocol handles. General protocol
composition therefore remains a separate question and cannot cite this result
as a complete composition law.

# R1 Independent Validation Request

> **Document kind:** Temporary falsifier brief
> **Document state:** Retired
> **Owner:** `project`
> **Authority:** None. A validator is asked to rebut the R1 reconstruction, not
> to approve a repair or score document quality.
> **Disposition:** Record material corrections in the adjudication, then delete
> this brief with the package after final validation.

This brief was executed as the first cold pass. Its hashes intentionally refer
to the pre-amendment inputs and must not be refreshed in place. The failed gate,
material corrections, amended hashes, and follow-up condition are recorded in
the [R1 Cold Validation Outcome](validation-outcome.md).

## Frozen inputs

Read these three pages first:

1. [R0 live baseline](baseline.md)
2. [R1 review adjudication](review-adjudication.md)
3. [R1 invariant ledger](invariant-ledger.md)

| Frozen input | SHA-256 |
|---|---|
| R0 baseline | `a779e5a9153cdbddb16efc6e188e6f660fd4387481656082765166cc5a29df72` |
| R1 adjudication | `e50e804af28b073a1458779369949378ca9dcede92c88d225b2be14b91fe0d75` |
| R1 invariant ledger | `f65ab53f22478c111937b9a1c8f08b50a222d69733644703a43f92d2b5ef4ac4` |

Then inspect only the live owners and code needed to test a claim. Treat
`docs/` as current authority and `docs-next` as a non-authoritative target.
Stage 4B is inactive. Do not assume compatibility with the current
implementation is a target requirement.

## Required challenges

1. **Find a faithful Statement path.** Exhibit a first-class, complete,
   Core-preserving way for the current target to bind every declared Statement
   occurrence before every applicable FS challenge, without a synthetic wire
   message or duplicated Context value. If it exists, identify the exact
   coverage, order, codec, and rejection laws.
2. **Ground causal adversaries.** Exhibit the exact live relation from a
   history-dependent prover strategy to `ProverTrace` and `ExecuteProtocol`, or
   show why the ledger's causal-strategy invariant is unnecessary for the
   target's claimed Analysis boundary.
3. **Implement the identity bottom.** Starting only from durable pages, derive
   bytes, equality, support, evaluation, and admission for one regime, one
   `ClosedFiniteTerm`, one `CanonicalSemanticValue`, and one sampler. Identify
   any supposedly missing contract that is actually defined.
4. **Execute Relations.** Produce the exact typed predicate for committed-object
   grounding and the formation/evaluation rules for artifact facts/selectors.
   Show whether an admitted `CorrespondenceRegime` is constructible.
5. **Resolve the projection distinction.** Either exhibit a target lane that
   represents the current directional 256-to-216-bit anchor projection and its
   quantitative collision loss, or show why v0 can deliberately eliminate that
   requirement without weakening a claimed relation.
6. **Attack the rebuttals.** Prioritize the R1 corrections: public-coin
   constructibility, PublicPorts reachability, manifest exactness, cost
   ownership, `PlanRealizes`, `ApplicationBinding`, and historical audit hashes.
   A single live counterexample is more valuable than agreement.
7. **Attack the invariant ledger.** Identify any requirement that secretly
   selects a representation, assigns authority to the wrong domain, conflates
   semantics with security, or excludes a demonstrably better architecture.

## Response format

For every material challenge, return:

- `Confirmed`, `PartiallyConfirmed`, `Rebutted`, or `Open`;
- exact file/line or primary-source evidence;
- the smallest counterexample or falsifier;
- whether the correction changes an invariant, an open fork, severity, or only
  wording; and
- no repair proposal unless it is needed to demonstrate the counterexample.

Do not copy private review prose into public-ready output. Do not treat line
count, reviewer agreement, or passing Markdown checks as semantic evidence.

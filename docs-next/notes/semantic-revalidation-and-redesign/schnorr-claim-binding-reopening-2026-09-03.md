# Schnorr Claim Binding Reopening Record

> **Kind:** Temporary reopening record under the v0 design program's change
> control (Section 14 of `../../project/v0-design-program.md`)
> **State:** Opened 2026-09-03; two candidate repairs named, the fixture-side
> repair recommended; the decision is taken with the fixture refreeze that
> follows the migration's publication; target pages unchanged
> **Authority:** None. Opening a reopening record changes no owner page,
> profile identity, evaluator, or judgment. Only the decision gate named in
> Section 6 can change an owner page.

## 1. Affected conclusion

The Relations and Plan candidates for the finite additive Schnorr subject
(`f0v2b2c1b5b1`'s successor line, package
`evaluation/formal-schnorr-relations-plan-f2p1/`) bind on two independent
paths: the relation definition, semantic model, and public instance; the
Protocol-relation binding's statement and phase edges; the Plan with its
nonce state and honest recipes; fifteen identities; all five property
premises with coordinates; 27 honest accepts and 27 plus-one rejects; five
refused mutations. One operand is missing: `ClaimMeaningBinding` requires an
`InitialClaim(BindingRef)`, and the admitted subject
(`evaluation/formal-source-target-core-f1r1b/`) declares no claim. The F2
applicability question therefore has no claim-meaning operand for this
subject, and the package's aggregate is `CannotAnswer` with the single
blocker `F2P1-C-INITIAL-CLAIM-ABSENT`.

## 2. Reason

The Schnorr fixture was authored as a verifier of one Check and two terminals
before the Relations attachment contract
(`docs-next/relations/relation-model.md`, Sections 7.2 and 7.3) fixed that a
Protocol-relation binding gives the initial claim its meaning. A verifier of
that shape needs no Claim for its own execution, so the fixture omitted
claims, and every package since then admitted it as it is. The contract and
the fixture are each consistent alone; together they leave the statement's
meaning without a carrier.

## 3. Candidate repairs

- **Fixture-side (recommended).** The fixture gains one initial claim,
  created at the statement binding's scope opening and consumed by the
  accepting terminal, with the rejecting terminal discharging it. The Core
  and Protocol identities of the fixture rotate; the migration rotates them
  regardless, and every package that re-admits the fixture at the refreeze
  re-admits the amended body at no additional cost. The Relations contract
  keeps its single attachment form.
- **Contract-side.** Relations admits a claim-free Protocol-relation binding
  whose statement meaning attaches to the public binding occurrence directly.
  This adds a second attachment form with weaker discipline and changes an
  owner page. It is warranted only if a selected protocol genuinely has no
  claim that can carry the statement's meaning, which the portfolio has not
  shown.

## 4. Identity effect and dependent packages

Under the fixture-side repair only the fixture's identities and the packages
that pin them move (`formal-source-target-core-f1r1b`, `formal-source-owner-views-f1r1c`,
`formal-provider-observables-f2o0` and `-f2o1`, `formal-schnorr-relations-plan-f2p0`
and `-f2p1`, and the mechanization vectors that decode the fixture), all of
which the migration's refreeze set already contains. No owner page changes.

## 5. Evidence

`research.schnorr-relations-plan-candidates` (`CannotAnswer`, sole blocker
`F2P1-C-INITIAL-CLAIM-ABSENT`) and `research.schnorr-relations-plan-coupling`
(the audit that found the five premises without operands).

## 6. Decision gate

The fixture refreeze that follows the identity-rotating publication of the
migrated owner text. Main proposes the fixture-side repair; the user decides
it with the publication gate. Until then the package stays `CannotAnswer`
and no page changes.

## 7. Reversal triggers

Adopt the contract-side repair instead if a selected protocol's verifier has
no claim to carry the statement's meaning, or if the Relations kernel adopts
statement-only bindings for another recorded reason.

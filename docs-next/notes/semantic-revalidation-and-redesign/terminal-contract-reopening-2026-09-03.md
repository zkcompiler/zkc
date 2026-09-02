# Terminal Contract Reopening Record

> **Kind:** Temporary reopening record under the v0 design program's change
> control (Section 14 of `../../project/v0-design-program.md`)
> **State:** Opened 2026-09-03; candidate repair selected at bounded research
> resolution; publication decision pending
> **Authority:** None. Opening a reopening record changes no owner page,
> profile identity, evaluator, or judgment. Only the decision gate named in
> Section 6 may do that.

## 1. Affected conclusion

The K2 Terminal law in `../../pir/interactive-core.md` Section 6.4, its use in
Core admission step 9 of Section 10, and the `TerminalDecl` and
`ClaimDisposition` bodies in Appendix A. The formal-assurance program's
provisional architecture also recorded, in
`formal-assurance-research/f0-provisional-architecture-and-entry-contracts.md`
Section 5.2, that `InteractiveCore` fields and occurrence order needed no
change; that non-change statement is what this record reopens.

## 2. Reason

Three defects in the written contract, found while deriving exact owner views
for the Terminal constructor family:

1. **Guard and required Checks are not connected.** Section 6.4 says every
   required check "has occurred and is true" at an active terminal, while
   terminal selection is by guard alone with first-active stopping. The state
   in which a terminal's guard is true and one of its required checks is
   false is unspecified: it is neither a Core outcome nor a refusal. The
   exhaustive oracle in `formal-assurance-research/f0v2b2c1b5a-terminal-path-algebra.md`
   exhibits it on a four-input carrier.
2. **"Accepting-path required reduction" has no owner field.** `TerminalDecl`
   carries no Reduction reference, so admission cannot distinguish a
   Reduction that must have applied before an Accept from an optional guarded
   one that did not occur.
3. **`Consume` and `Discharge` split identity without a discriminator.** The
   two tags have the same path-liveness effect and no defined mixed use, so
   two Core bodies can differ in identity while every written execution and
   closure rule treats them identically.

These are semantic gaps in the target text, independent of any formal
consumer. Their discovery route was the owner-view derivation program, but a
compiler or runtime implementing the page as written would meet the same
undefined state.

## 3. Candidate repair (selected at bounded research resolution)

Recorded in
`formal-assurance-research/f0v2b2c1b5b1-terminal-owner-contracts.md` and
realized in exact bytes in
`formal-assurance-research/f0v2b2c1b5b2-terminal-owner-projections.md`:

- keep first-active selection by guard exactly as written;
- require each Check named in `required_true_checks` to occur before the
  terminal and its output to be a positive must-fact of the terminal Guard's
  authenticated Foundation term, under a PIR-owned use predicate computed
  directly from the term;
- add `required_applied_reductions` as a sorted-unique set of Reduction
  references whose application regions the terminal region must imply;
- replace the authored `(ClaimRef, ClaimDisposition)` sequence with a
  sorted-unique `terminal_claims` set, deriving `Consume` for `Accept` and
  `Discharge` for `Reject` and `Abort`.

Alternatives refused with reasons in the same records: conjoining required
Checks into terminal selection (changes hidden control dependencies and
admits a double-consume path), reintroducing a `CheckFalse` failure
transition, deleting `required_true_checks`, admitting an external theorem or
certificate into admission, and keeping the unconstrained disposition tags.

## 4. Identity effect and dependent packages

The repair changes the Core body grammar. Every Core with a terminal rotates
its `CoreId`; every Protocol over such a Core rotates; the Interaction profile
and its fifteen transitive dependents rotate, as measured in
`formal-assurance-research/f0v-owner-view-publication-repair-design.md`
Section 6. Consumers that must move in the same change: the OIR endpoint
Terminal obligations, Analysis acceptance closures, the K2 witness instrument,
the F1-R1B fixture and its profile-bound controls, and the D1 integrated
carriers. The candidate profile digests recorded in the B5B2 note describe
that experiment only and must be recomputed from the authoritative source at
migration.

## 5. Evidence

| Gate | Result | What it establishes |
|---|---|---|
| `research.owner-view-terminal-path-algebra` | 38 findings, `CannotAnswer` | the gap, on a branch-complete carrier with an exhaustive oracle |
| `research.owner-view-terminal-owner-contracts` | 58 findings, affirmative selection | the candidate's must-fact analysis is sound against 320 valuations and rejects 25 mutations |
| `research.owner-view-terminal-projections` | 62 findings, affirmative | exact bytes admit, six views project through two paths, 17 semantic and six owner-view substitutions refuse |
| `research.owner-view-integrated-pcgraph` | 42 findings, affirmative | the repaired Terminal family composes with all other graph families on five carriers |

All four are finite executable evidence, not proofs. None publishes a profile.

## 6. Decision gate

Publication of the repair is the F0-V2C migration, to be run once together
with the normalized owner-view grammar and the two Section 11 wording fixes,
after the provider-observable audit and the mechanized-kernel feasibility
package report, and followed by a holdout rerun and the independent freeze
review. Until that gate, the target text stands as written and every
dependent identity remains unchanged.

## 7. Reversal triggers

Reverse the selection if a selected protocol needs one terminal to
distinguish a positive Claim use from an abandoned Claim under the same
verdict with a downstream consumer of that distinction; if a fixture cannot
express its required Check as a direct Guard input and the direct-input
boundary must widen; or if integration exposes an owner coordinate the
candidate omits. Each trigger reopens B5B1's selection, not first-active
control.

# F0-V2B2C1B5B2 exact Terminal owner projections

This package applies the B5B1 Terminal contract selection to exact candidate
Core bytes and all six normalized owner views. It is the final
constructor-isolation package in B2C1B; it does not publish the candidate into
the target PIR specification.

Run from the repository root:

```sh
python3 -B evaluation/formal-source-terminal-owner-projections-f0v2b2c1b5b2/run.py --check
```

The frozen bounded result is
`Affirmative/F0V2B2C1B5B2-A-EXACT-TERMINAL-OWNER-PROJECTIONS`.

## Candidate carried by the experiment

The experiment constructs a synthetic revision-3 Interaction profile over the
already checked F0-V1 publication topology. It adds reachable body, view, and
admission declarations for this candidate:

```text
TerminalDeclCandidate = {
  verdict: TerminalVerdict,
  public_outputs: CanonicalSeq<ValueRef>,
  required_true_checks: CanonicalSortedUniqueSeq<CheckRef>,
  required_applied_reductions:
    CanonicalSortedUniqueSeq<ReductionRef>,
  terminal_claims: CanonicalSortedUniqueSeq<ClaimRef>
}
```

The view grammar removes authored `ClaimDispositionEntry`, expands
`TerminalEntry`, and adds one `TerminalReductionRequirementEntry` to
`ClaimReductionView`. The disposition is derived: an `Accept` consumes each
terminal Claim, while `Reject` and `Abort` discharge each terminal Claim.

The owner-free normalized grammar is hashed before the candidate profile is
attached, avoiding a profile/schema identity cycle. The synthetic Interaction
profile then names that grammar digest, and the final schema source names the
resulting profile:

- Interaction profile digest:
  `0af785eb8159ca2182843c62f72898e3c17266c5a7d9b317cfe2ae463d840474`;
- owner-free grammar SHA-256:
  `f88b5a5e48046cf4e9079410dbb6ea572316aa51de175d2ed009f18ec6e48292`;
- attached schema-source SHA-256:
  `c87b09d89ddbe92f8a6cdad8eae6bb0dbcfea6ed69e65e335e551efba0f6e03d`.

Both publication compilers agree on all 18 profiles. Interaction and its 15
transitive dependents rotate; `analysis-kernel` and `oir-endpoint-graph` remain
stable. These are synthetic candidate identities, not current target IDs.

## Branch-complete witness

The exact Core has three public Booleans, one identity Check, two reductions,
three Claims, and three first-active terminals:

```text
Check(always, q) -> checked_q
Reduction 0(checked_q AND g)
Accept(checked_q AND g)
  requires Check 0, Reduction 0, and live Claim 1
Reduction 1(always after the failed Accept branch)
Abort(h)
  requires Reduction 1 and live Claim 2
Reject(always fallback)
  requires Reduction 1 and live Claim 2
```

The initial Claim is linear. Both reductions consume it, but their active
regions are disjoint. Each reduction creates one reusable output Claim. Across
all eight Boolean assignments, first-active execution reaches `Accept` twice,
`Abort` three times, and `Reject` three times.

## Independent evidence paths

The typed path authenticates the synthetic profile, exact Core and dependency
closure, invokes the B5B1 non-enumerating must-fact analysis, admits a
process-local immutable Core handle, pairs a Fresh Protocol, and projects the
six owner views.

The cold path imports neither that typed owner nor the B5B1 analyzer. It:

1. independently applies and compiles the pinned schema delta;
2. authenticates complete profiled Core and Protocol bytes;
3. parses plain records and authenticates the exact portable-algorithm
   preimages;
4. exhaustively executes all eight Boolean assignments, including linear Claim
   consumption and first-active termination; and
5. derives and encodes all six views through separate module instances.

The paths agree on six exact bodies totaling 32,796 bytes. Every body decodes
and re-encodes byte-identically, reprojection is deterministic, and all 17
target `sorted-unique` sequences are in target-byte order.

The expanded public-causality graph has 28 nodes and 49 edges. A terminal
effect explicitly depends on its public outputs, required Check outputs,
required Reduction states, and terminal Claims. Abort and Reject do not acquire
an implicit edge from the accepting Check.

## Negative controls

The gate freezes 62 findings. Seventeen freshly encoded semantic mutations are
rejected by both paths, including absent, duplicate, late, or noncanonical
Check/Reduction requirements; wrong or incomplete terminal Claim closure;
guard weakening; nontermination; linear-consumer overlap; ABI drift; Claim
output aliasing; and missing or duplicate backlinks.

Six schema-valid owner-view substitutions alter a Check requirement, Reduction
requirement, terminal Claim, derived disposition, requirement row, or graph
edge. Each remains encodable but has bytes different from the unique
owner-derived view. The old authored-disposition Terminal row is no longer a
value of the candidate schema. Core ID, cross-Core Protocol, truncated-byte,
algorithm-closure, algorithm-preimage, and process-local authority
substitutions also fail closed.

## Result and boundary

At constructor-isolation resolution, this closes the last of the 21 B2C
pressure families. It provides concrete evidence that the B5B1 design can be
made identity-bearing and projected without adding a new kernel, transcript
state, semantic SSA token, or external theorem authority.

It does not establish:

- B2D integrated multi-family graph or mutation closure;
- publication of the target Interaction profile or migration of dependents;
- correspondence with the live compiler, runtime, generated verifier, or
  backend;
- a mechanized refinement proof or proof of the must-fact analyzer;
- reduction truth, protocol soundness, Fiat--Shamir security, concrete hash or
  sponge assumptions, or a QROM result; or
- F1 Q1 source correspondence.

The next gate is B2D. F0-V2C migration should use the B2D result rather than
promoting this temporary package wholesale.

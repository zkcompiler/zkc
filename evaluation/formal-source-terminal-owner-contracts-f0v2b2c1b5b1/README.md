# F0-V2B2C1B5B1 Terminal owner contracts

This package selects and falsifies a candidate repair for the three Terminal
owner gaps exposed by B5A. It does not change the target specification or
complete the expanded-Terminal B2C projection family.

Run from the repository root:

```sh
python3 -B evaluation/formal-source-terminal-owner-contracts-f0v2b2c1b5b1/run.py --check
```

The frozen aggregate is
`Affirmative/F0V2B2C1B5B1-A-TERMINAL-CONTRACT-SELECTION` at bounded research
resolution.

## Selected candidate

The candidate Terminal body is:

```text
TerminalDeclCandidate = {
  verdict: TerminalVerdict,
  public_outputs: CanonicalSeq<ValueRef>,
  required_true_checks: CanonicalSortedUniqueSeq<CheckRef>,
  required_applied_reductions:
    CanonicalSortedUniqueSeq<ReductionRef>,
  terminal_claims: CanonicalSortedUniqueSeq<ClaimRef>
}

DerivedClaimDisposition(t,c) =
  Consume    if t.verdict = Accept
  Discharge  if t.verdict in {Reject,Abort}
```

`public_outputs` remains ordered because it is an output ABI. The other three
collections are semantic sets, so arbitrary order and duplicate identity
spellings are refused.

For every required Check, admission requires its unique occurrence to precede
the Terminal and to be active whenever the Terminal is active. It additionally
requires the Terminal Guard's exact Foundation Boolean term to establish the
Check output as a positive must-fact whenever that Guard returns true. The
base rule recognizes structural `Literal`, `Variable`, `Let`, and
`Conditional` reasoning. An admitted `PrimitiveCall` is opaque to this rule;
an implication that depends on its denotation is refused rather than guessed.

For every required Reduction, its unique `ApplyReduction` occurrence must
precede the Terminal and the Terminal's active region must imply the
Reduction's active region. This asserts only that the structural transition
was applied. It proves neither the reduction theorem nor a cryptographic
property.

Claim dispositions are derived from the verdict. The current unrestricted
`Consume | Discharge` field creates two identity-bearing spellings without a
defined operational distinction. The candidate makes an accepting terminal
consume every live Claim and a Reject/Abort terminal discharge every live
Claim. A future mixed-disposition use case would require a new exact semantic
role and consumer, not an unconstrained tag.

## Why the Guard carries the Check

The selected authoring pattern is explicit:

```text
Check(always) -> Boolean q
Reduction 0(q AND g)
Accept(q AND g), requiring Check 0 and Reduction 0
Reduction 1(always after the failed Accept decision)
Abort(h), requiring Reduction 1
Reject(always fallback), requiring Reduction 1
```

The same exact `q AND g` Guard protects the branch Reduction and Accept. A
false Check therefore follows the authored fallback path. It is not converted
into an implicit failure or operational noncompletion.

Silently redefining terminal selection as `guard AND required checks` is not
equivalent. With Reduction 0 guarded only by `g`, the valuation `g=true` and
`q=false` applies Reduction 0, suppresses Accept through the hidden conjunct,
then attempts the fallback Reduction 1 on the already consumed linear Claim.
The independent oracle freezes this minimal counterexample.

## Evidence

The candidate analyzer does not enumerate assignments. Its must-fact
abstraction is compared with an independently structured exhaustive evaluator
over 40 Boolean terms and 320 valuations. It is exact on 39 terms; the sole
intentional precision loss is an opaque primitive call.

The complete Terminal carrier then covers eight valuations and partitions
them as:

| Verdict | Valuations |
|---|---:|
| `Accept` | 2 |
| `Abort` | 3 |
| `Reject` | 3 |

The package freezes 58 findings:

| Outcome | Count |
|---|---:|
| `Affirmative` | 20 |
| `Refused` | 28 |
| `Malformed` | 2 |
| `Unsupported` | 1 |
| `CannotAnswer` | 7 |

Twenty-five mutations are rejected by both candidate and oracle. They cover
missing, disjunctive, negated, unconditional, late, inactive, absent,
duplicated, and noncanonical Check/Reduction/Claim requirements; hidden
terminal gating; claim-flow overlap; old disposition syntax; malformed terms;
ABI drift; and unsupported effects. A structurally opaque primitive
conjunction is extensionally valid in the oracle but intentionally refused by
the base candidate, demonstrating fail-closed incompleteness.

## Ownership and limits

Foundation continues to own portable-term identity, typing, and denotation.
PIR owns the narrower question “may this term be used as a Terminal Guard for
this exact required Check?” No Foundation result object, Analysis judgment,
external theorem, solver certificate, transcript token, semantic SSA token, or
new kernel is introduced.

This result does not establish:

- the exact target `InteractiveCoreBody` or any migrated profile ID;
- full Foundation-term coverage;
- six-view exact projection or PCGraph edge migration;
- runtime execution/receipt correspondence;
- a mechanized soundness proof for the abstract interpreter;
- a reduction theorem, protocol theorem, Fiat--Shamir theorem, hash or sponge
  property, QROM result, implementation correspondence, or Q1.

B5B2 must apply this candidate to exact Core bytes and all six normalized owner
views through typed and cold byte-derived paths. B2C remains at 20/21 until
that gate succeeds.

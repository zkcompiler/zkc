# F0-V2B2C1B5A terminal path algebra

This package tests the missing path-sensitive prerequisite for the final B2C
Terminal pressure family. It does not claim that B2C1B5 is complete.

Run from the repository root:

```sh
python3 -B evaluation/formal-source-terminal-path-algebra-f0v2b2c1b5a/run.py --check
```

The frozen aggregate is
`CannotAnswer/F0V2B2C1B5A-C-TERMINAL-CONTRACT-INCOMPLETE`. That is a
successful fail-closed research result: one compact claim-flow method works,
but two sentences in the candidate Terminal contract do not yet have enough
owner data or transition semantics to admit the full family.

## What the positive carrier establishes

The carrier has one Check, two Reductions, three Claims, and all three Terminal
verdicts. Its schedule is:

```text
Check(always)
Reduction 0(g): consume linear claim 0, create reusable claim 1
Accept(g): Consume claim 1
Reduction 1(always, but only after Accept(g) did not stop):
  consume linear claim 0, create reusable claim 2
Abort(h): Discharge claim 2
Reject(always fallback): Discharge claim 2
```

The two Reductions are both syntactic consumers of one linear Claim, but their
active regions are disjoint:

```text
Reduction 0   g
Accept        g
Reduction 1  not g
Abort         not g and h
Reject        not g and not h
```

This is the case the B2C1B3 global-live-set approximation could not validate.
The new analyzer derives these regions without a transcript state, semantic
SSA token, MLIR token, Boolean-assignment enumeration, or ROBDD. Claim
coordinates remain SSA-like: each Claim has one exact source and all uses are
scheduled owner coordinates.

An independently structured oracle enumerates the four assignments of `g` and
`h`. It reaches Accept twice, Abort once, and Reject once, agreeing with the
compact analyzer's live-Claim sets `(1)`, `(2)`, and `(2)` at those Terminals.
The exhaustive path is test evidence only; it is not the proposed target
algorithm.

## Compact method

For the current closed syntactic guard fragment, every occurrence has either
`Always` or one exact opaque guard atom. Define:

```text
LiveBefore(i) = conjunction of not guard(t)
                for every earlier Terminal occurrence t

Active(i) = LiveBefore(i) and guard(i)
```

An active region is therefore a conjunction of positive and negative exact
guard atoms. Implication is literal-set inclusion; disjointness is a literal
conflict. Both are deterministic set operations.

For each Claim and queried active region, the analyzer classifies liveness as
`Live`, `Dead`, or `Unknown` from:

- the exact initial or Reduction-output source region;
- every earlier scheduled Reduction use;
- `Linear` versus `Reusable`; and
- first-active-Terminal preemption already present in each active region.

An active Reduction requires every input definitely `Live`. Two Reduction
uses of a linear Claim must have disjoint active regions. Every reachable
Terminal must dispose every and only definitely live Claim; `Unknown` refuses
admission instead of guessing. The bounded positive carrier takes 24 abstract
operations.

The 21 mutations cover fallback and backlink errors, source/output mismatch,
empty or absent Reduction inputs, overlapping linear consumers, dead inputs,
missing or spurious Terminal dispositions, an ambiguous third guard, required
Check order/activity, malformed verdicts, and unsupported effects. The compact
and exhaustive paths reject every mutation.

## Gap 1: required Check truth is not derivable

The current occurrence rule says that an occurrence is active when execution
is live, its scope is open, and its Guard evaluates true. The Terminal rule
also says every `required_true_check` is true at an active Terminal. No written
rule currently connects those propositions.

The package adds Check 0 to the guarded Accept's required list. Structural
order and activity are valid, but the independent oracle finds this concrete
execution:

```text
g = true
h = false
Check 0 = false
Accept guard = true
```

Under the written occurrence rule, Accept is active; under the Terminal rule,
it is invalid because its required Check is false. There is no typed Protocol
failure or noncompletion branch for this case. Treating a required Check as
silently true would be unsound, while treating it as an implicit extra Guard
would change first-active-Terminal semantics and the PCGraph control law.

B2C1B5B must choose and encode one rule. The preferred direction is to retain
the current first-active semantics and require an exact, checked entailment
from the Terminal Guard to every required Check result. The base profile can
support a closed structural subset; richer implications need an authenticated,
locally checked guard-law witness. A caller assertion or successful sample run
is not evidence. A qualified Foundation result can check the exact portable
algorithm proposition, while PIR retains authority over its use in Core
admission; this does not require a `TerminalKernel`.

## Gap 2: “required reduction” has no owner field

The Terminal prose requires every accepting-path required Reduction to be
saturated and rejects an unapplied required Reduction. The exact Terminal body
contains only verdict, public outputs, required Checks, and Claim dispositions.
No declaration identifies which scheduled Reductions are required for one
Terminal.

Because `ApplyReduction` is already an explicit Core occurrence, there are two
coherent repairs:

1. remove the undefined saturation language and let path-sensitive Claim
   closure be the complete K2 structural rule; or
2. add an exact `required_applied_reductions` sequence to `TerminalDecl`, then
   require the Terminal active region to imply every named Reduction's active
   region.

The second is preferable when K2 intends acceptance to assert Reduction
application independently of residual Claim liveness. K3 must still establish
what that Reduction means; the field cannot prove a theorem by existing.

## Why B2C1B5 remains open

The compact region law is strong enough to replace B3's static shortcut for
the closed guard fragment. It is not yet integrated into:

- exact canonical InteractiveCore bytes and admission handles;
- the four Terminal-relevant normalized owner views;
- PCGraph transfer/class/sink projection;
- the Fresh runtime schema or completed-record replay; or
- the unresolved Check-entailment and required-Reduction contracts above.

B2C1B5B should settle those two owner contracts first, then apply the existing
B2C1A codec and typed/cold projection pattern. B2D should remain separate: it
combines all PCGraph classes and validates actual occurrence/Claim/Reduction/
Terminal receipts.

This package does not publish a target profile, establish compiler/runtime
correspondence, prove the compact algorithm correct for an unbounded or richer
guard language, prove a refinement theorem, establish Fiat--Shamir security,
or close Q1.

# F0-V2B2C1B5B1 Terminal Owner Contracts

> **Kind:** Temporary F0 design-selection and bounded falsification record
> **State:** `Affirmative/F0V2B2C1B5B1-A-TERMINAL-CONTRACT-SELECTION` at
> bounded research resolution; exact target carrier/view migration remains
> `CannotAnswer`
> **Authority:** None. This note changes no current or target semantics,
> profile identity, implementation claim, theorem status, or roadmap priority.
> **Evidence:**
> [`evaluation/formal-source-terminal-owner-contracts-f0v2b2c1b5b1`](../../../../evaluation/formal-source-terminal-owner-contracts-f0v2b2c1b5b1/README.md)

## 1. Decision

B5B1 selects one candidate for exact B5B2 falsification:

1. Terminal selection remains exactly the existing first-active Guard rule.
2. A required Check must occur first and its exact output must be a positive
   must-fact of the Terminal Guard's authenticated Foundation term.
3. A Terminal carries an explicit sorted-unique set of required applied
   Reductions; its active region must imply each named application region.
4. The Terminal carries a sorted-unique live-Claim set. `Consume` is derived
   for `Accept`; `Discharge` is derived for `Reject` and `Abort`. The
   unconstrained identity-bearing disposition tag is removed.
5. Foundation still owns term denotation. PIR owns this Terminal-specific use
   predicate. Analysis, a theorem prover, or an exporter does not participate
   in Core admission.

This is a provisional F0 selection, not a target edit. B5B2 must reproduce the
candidate through exact Core bytes, immutable admission, all six static views,
and a separately structured cold projector before publication is considered.

## 2. Correcting B5A's owner hypothesis

B5A correctly selected “Guard implies required Check result” as the preferred
shape, but suggested that a richer case could consume a qualified
Foundation-owned result. The live Foundation contract rules that out:
Foundation owns the common term mechanisms and explicitly does not define a
universal judgment engine or resource policy. The qualified use question is
PIR-local:

```text
Foundation:  exact admitted term and its denotation
PIR:         exact TerminalCheckEntailed use predicate
Analysis:    later property proposition, never Core-admission authority
```

The base predicate is computed directly from the already authenticated term.
It creates no new content-addressed theorem object and no ambient proof lookup.
A future richer implication satellite would need an exact proposition,
validator, bounds, identity, and explicit PIR admission integration; it cannot
appear as a generic Foundation judgment.

## 3. Required-Check contract

Let `o_t` be the unique occurrence of Terminal `t`, `o_c` the unique
`InvokeCheck(c)` occurrence, and `Region(o)` the compact first-active region
selected by B5A. The candidate rule is:

```text
TerminalCheckEntailed(t,c) iff
  c in t.required_true_checks
  and o_c < o_t
  and Region(o_t) implies Region(o_c)
  and either Region(o_t) is impossible
      or exists input ordinal i such that
           GuardInputs(o_t)[i] = OccurrenceOutput(o_c,0)
           and Positive(i) is in MustWhenTrue(GuardAlgorithm(o_t))
```

An `Always` Terminal therefore cannot require a runtime Check. A Check may be
false; the rule proves only that this Terminal cannot be selected in that
case. A normal verifier shape is:

```text
q := InvokeCheck(...)
ReachTerminal(Accept) guard = q AND branch_condition
ReachTerminal(Reject) guard = Always  // later fallback
```

This retains the distinction among semantic false, unsupported evaluation,
and operational noncompletion. A false `q` takes an authored nonaccepting
branch. Missing primitive support remains `Unsupported`; it is not false.

### 3.1 Must-fact abstraction

For each Boolean term `e`, compute:

```text
Must(e) = {
  when_true:  Impossible | finite set of signed input literals,
  when_false: Impossible | finite set of signed input literals
}
```

A literal in `when_true` is required on every execution where `e` returns
true. The selected structural rules are:

- a Boolean input variable contributes its positive literal on true and its
  negative literal on false;
- a Boolean constant makes one result possible with no required literal and
  the other impossible;
- `let` prepends the bound abstract value to the de Bruijn environment;
- for a conditional, each result has two path alternatives; conjoin facts
  within each path and intersect facts across feasible alternatives; and
- a primitive call returns no must-literal facts in the base analysis.

Dropping information is safe: the analysis may refuse a valid implication but
must never admit an invalid one. This is the standard sound-but-incomplete use
of an abstract semantics, following the fixed-point/abstraction discipline of
[Cousot and Cousot's original abstract-interpretation account](https://www.di.ens.fr/~cousot/COUSOTpapers/POPL77.shtml),
specialized here to a finite acyclic term rather than a general program
analysis.

The executable candidate is non-enumerating. An independent truth-table oracle
checks all 40 selected terms over 320 valuations. Thirty-nine summaries are
extensionally exact. The deliberate exception is an exact primitive `AND`:
the oracle proves the implication, while base PIR refuses because it imports
no primitive-specific theorem.

### 3.2 Why direct Check-output inputs

B5B1 requires the exact Check output to appear directly among Guard inputs.
Following a chain of `DerivedValueDecl` algorithms would require a second
compositional value-fact analysis and a larger dependency/complexity proof.
The direct form is expressive enough for the base compiler: it may build any
structural Boolean combination in the Guard term itself. B5B2 should retain
this direct boundary unless a selected protocol fixture cannot inhabit it.

## 4. Required-Reduction contract

The current phrase “accepting-path required reduction” has no owner field. It
cannot be reconstructed from Claim liveness: a Reduction may consume a
reusable Claim, produce no live terminal Claim, or be semantically required
despite no dataflow-visible effect.

The selected field is:

```text
required_applied_reductions:
  CanonicalSortedUniqueSeq<ReductionRef>
```

For every named Reduction `r`, admission requires its unique
`ApplyReduction(r)` occurrence before the Terminal and:

```text
Region(TerminalOccurrence(t)) implies Region(ApplyOccurrence(r))
```

This is an authored semantic obligation, not a mirror of runtime state.
Execution still derives whether the occurrence applied. Removing a reference
changes the Core body and weakens the authored terminal contract; it is not an
equivalent spelling. K3/Analysis continues to own the proposition denoted by
the Reduction contract and whether any theorem applies.

The field is available on all verdicts. Restricting it to Accept would add a
needless verdict-dependent body grammar and would prevent a protocol from
requiring an exact cleanup or audit transition before Abort/Reject.

## 5. Claim closure and disposition

The current target carries `ClaimDisposition = Consume | Discharge`, but gives
the two tags the same path-liveness effect and does not define a mixed
Terminal use. Two Core bodies can therefore differ only in this tag while all
written execution and closure rules remain identical. That is an unexplained
identity split.

The candidate replaces the pair sequence with:

```text
terminal_claims: CanonicalSortedUniqueSeq<ClaimRef>
```

At every possible active Terminal, this set equals every live Claim, including
Reusable Claims. The runtime/history disposition is derived:

```text
Accept       -> Consume each terminal Claim
Reject/Abort -> Discharge each terminal Claim
```

This makes “unresolved initial claim” precise: an initial Claim is either
already consumed by a path Reduction or belongs to the active Terminal's exact
closure set. An accepting path cannot silently abandon one. The selected
meaning also avoids confusing the current system's check-backed
`pir.discharge` operation with this target resource-close tag.

### 5.1 Reversal trigger

Reverse this simplification only if a concrete selected protocol requires one
Terminal to distinguish a positive Claim use from an abandoned Claim under the
same verdict and a downstream owner consumes that distinction. The repair
would then need an exact typed role linking each use to its semantic consumer.
Restoring a free `Consume | Discharge` bit would not be sufficient.

## 6. Alternatives at equal resolution

| Candidate | Result | Decisive reason |
|---|---|---|
| Explicit Guard plus PIR must-facts | Selected for B5B2 | Preserves first-active control, gives false Checks an authored fallback, remains bounded and fail closed |
| Implicitly conjoin required Checks during terminal selection | Refused | Changes hidden control dependencies; `g=true, check=false` can apply a guarded Reduction, suppress Accept, then double-consume on fallback |
| Reintroduce a `CheckFalse` failure transition | Refused | Restores the pre-K2 failure graph and changes Core outcomes/control instead of repairing the current model |
| Delete `required_true_checks` | Refused | Re-admits B5A's exact false-Check counterexample and weakens explicit verifier acceptance structure |
| Admit an external theorem/certificate directly | Refused | Makes an unowned result part of PIR admission and leaves proposition, checker, bounds, and identity unspecified |
| Keep unrestricted Claim disposition tags | Refused | Distinct identity bytes have no defined semantic discriminator |
| Derive Claim disposition from verdict | Selected for B5B2 | One owner fact, no alias spelling, exact fail/accept meaning, smaller downstream contract |

The hidden-gating counterexample is concrete:

```text
authored Reduction 0 guard = g
hidden Accept selector      = g AND check
fallback Reduction 1       = Always after no Accept

g = true, check = false
  -> Reduction 0 consumes linear Claim
  -> hidden selector suppresses Accept
  -> Reduction 1 attempts the same dead Claim
```

The selected candidate instead gives Reduction 0 and Accept the same exact
authored `g AND check` Guard.

## 7. Proposed exact body delta

B5B2 should test this candidate body before target publication:

```text
TerminalBodyCandidate(x) = R {
  0: TerminalVerdictBody(x.verdict),
  1: S[ ValueRefBody(output) ... ],
  2: S[ N(check_ref) ... ascending unique ],
  3: S[ N(reduction_ref) ... ascending unique ],
  4: S[ N(claim_ref) ... ascending unique ]
}
```

The delta is identity-bearing. It removes `ClaimDispositionBody` from this
Core grammar, adds one Reduction-reference field, and changes three collections
to semantic sets. Publication therefore rotates the Interaction profile, every
importing PIR profile, every affected Core/Protocol, and downstream subjects
that embed those identities. B5B1 computes no rotated ID and authorizes no
migration.

## 8. Downstream cone for B5B2 and F0-V2C

B5B2 must update the candidate normalized schema source and prove, without
editing target authority yet, that all of these can be derived exactly:

- `EffectView.TerminalEntry`: add required Reductions and terminal Claims;
- `ClaimReductionView`: retain per-Terminal required Reductions and derived
  disposition histories;
- `PublicCoinView.PCGraph`: each Terminal effect receives every named
  `ReductionStateNode` in addition to Guard, Check, Claim, and output sources;
- `ExecutionView`: retain the revised static Terminal schema while runtime
  results continue to report reached verdict and public outputs;
- OIR endpoint Terminal obligations: add required Reduction spine references
  and derive Claim disposition from verdict; and
- Analysis acceptance closures: include the new owner leaves and remove the
  authored disposition leaf.

Canonical PIR prose, profile sources, constructor census, schemas, all typed
models, cold decoders, fixtures, and dependent expected identities move only
at F0-V2C after B5B2 and B2D succeed.

## 9. Evidence and nonclaims

The frozen package has 58 findings: 20 `Affirmative`, 28 `Refused`, two
`Malformed`, one `Unsupported`, and seven `CannotAnswer`. Twenty-five
mutations are rejected by both implementations. The complete carrier covers
eight assignments with two Accept, three Abort, and three Reject outcomes.

This supports the candidate contract only for the bounded B5B1 carrier and
Boolean fragment. It does not establish exact Core admission, six-view
projection, full Foundation-term traversal, PCGraph migration, runtime
correspondence, a mechanized abstract-interpreter proof, target publication,
implementation correspondence, Q1, any reduction theorem, or any
Fiat--Shamir/security property.

## 10. Next checkpoint

F0-V2B2C1B5B2 should:

1. bind the analysis to exact authenticated Foundation term bodies and direct
   Check-output `ValueRef` coordinates;
2. compile the candidate `TerminalBody` into strict Core bytes and immutable
   owner admission;
3. derive all six normalized views through independent typed and cold paths;
4. add the exact Terminal-to-Reduction PCGraph edges and transfers;
5. reject schema-valid Check, Reduction, Claim, Guard, edge, and owner-view
   substitutions; and
6. report the exact migration cone without publishing the target profile.

Only an affirmative B5B2 result may move B2C from 20/21 to 21/21. B2D remains
separate and must integrate the revised Terminal family with every other graph
and runtime family.

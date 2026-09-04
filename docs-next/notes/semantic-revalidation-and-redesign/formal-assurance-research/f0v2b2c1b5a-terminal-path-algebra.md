# F0-V2B2C1B5A Terminal Path Algebra

> **Kind:** Temporary reopened-F0 semantic-gap and method-selection result
> **State:** `CannotAnswer/F0V2B2C1B5A-C-TERMINAL-CONTRACT-INCOMPLETE`;
> compact path-sensitive Claim flow is supported at bounded research
> resolution, but the complete Terminal projection family remains open
> **Authority:** None. This note and executable package do not change PIR,
> owner-view schemas, admission, compiler/runtime behavior, or any theorem
> **Predecessor:**
> [`F0-V2B2C1B4 Module Owner Projections`](f0v2b2c1b4-module-owner-projections.md)
> **Executable gate:**
> [`evaluation/formal-source-terminal-path-algebra-f0v2b2c1b5a`](../../../../evaluation/formal-source-terminal-path-algebra-f0v2b2c1b5a/README.md)

## 1. Decision

Do not complete B2C1B5 by extending the B2C1B3 global-live-set shortcut. That
shortcut rejects safe first-active-Terminal programs and cannot establish the
written path-sensitive claim.

For the existing closed syntactic guard fragment, use exact **guard regions**:

```text
LiveBefore(i) = all earlier Terminal guard atoms are false
Active(i)     = LiveBefore(i) and guard(i)
```

Each region is one conjunction of exact positive and negative guard atoms.
Implication and disjointness reduce to literal-set inclusion and conflict.
This is sufficient to validate conditional Claim creation, mutually exclusive
linear uses, first-active-Terminal preemption, and exact per-Terminal Claim
closure without enumerating assignments or building a canonical decision
diagram.

This method is selected only as the B5A candidate for the current syntactic
fragment. B2C1B5 remains open because the candidate target text does not define
how a Terminal Guard establishes that every `required_true_check` is true and
does not identify an “accepting-path required reduction.” Those are semantic
owner gaps, not implementation details.

## 2. Why the B3 abstraction is insufficient

B2C1B3 computes one global set: a linear Claim used by any Reduction is removed
before every Terminal is checked. That is sound for its unconditional final-
fallback fixtures, but not for guarded alternatives.

The B5A carrier has this resource flow:

```text
                         g
claim 0 (Linear) ------> R0 ------> claim 1 (Reusable) --> Accept(g)
        |
        | execution continues only if Accept(g) did not stop
        v                 not g
        +---------------> R1 ------> claim 2 (Reusable)
                                      |             |
                                      v             v
                                  Abort(h)       Reject(fallback)
```

Both `R0` and `R1` name Claim 0, but they cannot execute on the same path:

| Coordinate | Exact active region | Live Claim at completion |
|---|---|---|
| `R0` | `g` | Claim 1 |
| `Accept` | `g` | Claim 1, then `Consume` |
| `R1` | `not g` | Claim 2 |
| `Abort` | `not g and h` | Claim 2, then `Discharge` |
| `Reject` | `not g and not h` | Claim 2, then `Discharge` |

The global-use rule rejects two consumers. The region rule accepts because the
two consumer regions are disjoint. This is not a relaxation of linearity:
the independent execution oracle confirms that Claim 0 is consumed exactly
once on every complete path.

## 3. Compact structural method

### 3.1 Region algebra

For one exact `EvaluateGuard` body, use its structurally identified body as an
opaque atom. `Always` contributes no positive atom. A region is:

```text
GuardRegion = {
  required_true: finite set of exact guard atoms,
  required_false: finite set of exact guard atoms
}
```

A region is impossible when an atom occurs in both sets. For possible regions:

```text
Implies(A,B) =
  B.required_true  subset A.required_true
  and B.required_false subset A.required_false

Disjoint(A,B) =
  A.required_true intersects B.required_false
  or B.required_true intersects A.required_false
```

The method deliberately does not infer equivalence or implication between
different guard algorithms. A richer fact requires an identified and checked
law; host-language equality, an SMT answer without a bound proposition, or one
sample execution cannot widen the relation.

### 3.2 Claim state

At each active Reduction or Terminal region, one Claim is classified:

- `Live` when the region implies the exact source region and is disjoint from
  every earlier linear consumer region;
- `Dead` when it is disjoint from the source or implies one earlier consumer;
  or
- `Unknown` otherwise.

An active Reduction requires every input `Live`. Linear consumer regions are
pairwise disjoint. Reusable uses do not kill a Claim. Every reachable Terminal
must dispose every and only `Live` Claims; `Unknown` refuses admission. This
last rule is important: an authored disposition cannot adapt to an unrecorded
branch on which its Claim does not exist.

This remains owner-derived state. Claim source, usage, Reduction inputs and
outputs, occurrence Guard, schedule position, Terminal disposition, and first-
active control already belong to the Core. There is no need for a
`TerminalKernel`, transcript root, semantic SSA token, or MLIR token.

### 3.3 Complexity boundary

The candidate performs finite set operations over occurrence regions, Claim
sources, Reduction uses, and Terminal closures. It does not enumerate Boolean
assignments. The independent path enumerator is deliberately a test oracle
only. The positive carrier takes 24 candidate operations and four oracle
assignments.

This is not yet a theorem that the implementation is polynomial for every
future guard extension. B2C1B5B must freeze the exact bounds and prove or test
the selected implementation against them.

## 4. Semantic gap: required Check truth

The candidate target currently states both:

1. an occurrence is active when execution is live, its scope is open, and its
   Guard evaluates true; and
2. every `required_true_check` is true at an active Terminal.

The body has the required Check references, but there is no rule requiring the
Terminal Guard to imply their Boolean results. The B5A oracle exhibits:

```text
g = true
h = false
Check 0 = false
Accept guard = true
```

The occurrence rule selects Accept; the Terminal rule says that state is
invalid. No current Core outcome covers it. Therefore none of these shortcuts
is acceptable:

- assuming a prior Check is true because it occurred;
- treating `required_true_checks` as implicit Guard conjuncts without changing
  the first-active and PCGraph definitions; or
- converting the contradiction into Reject, Abort, interpretation failure, or
  operational noncompletion without an authored rule.

The preferred repair preserves the current first-active definition and adds a
checked entailment obligation:

```text
TerminalCheckEntailed(t,c) =
  CheckOccurrence(c) precedes TerminalOccurrence(t)
  and Active(t) implies Active(CheckOccurrence(c))
  and Guard(t) = true implies CheckResult(c) = true
```

The first two clauses are PIR structural facts. For the third, a small base
profile may accept only exact recognized Boolean combinators. A richer case
should consume a qualified Foundation-owned result over the exact portable
Guard algorithm, evaluation contract, and Check-output input coordinate. PIR
still owns the use of that result in Core admission. This follows the existing
`profile -> qualified judgment -> owner policy` architecture and avoids making
an external theorem prover or caller the semantic authority.

An alternative is to redefine Terminal selection as Guard **and** all required
Checks. That is coherent, but it changes the terminal-preemption predicate and
turns the negation of an earlier selection into a disjunction. It should not be
adopted implicitly; it requires a different path algebra and fresh PCGraph/FS
falsification.

## 5. Semantic gap: required Reduction

The target text also requires every accepting-path required Reduction to be
saturated and rejects an unapplied required Reduction. Yet `TerminalDecl` and
`TerminalBody` carry no Reduction reference or policy, while Reductions are
already explicit scheduled `ApplyReduction` effects.

The current bytes cannot distinguish:

- a Reduction that must have applied before this Accept;
- an optional guarded Reduction whose branch did not occur; and
- a declared Reduction whose residual Claim is intentionally discharged.

The recommended decision is explicit:

- if Claim closure is meant to be the complete K2 obligation, delete the
  undefined “required Reduction” language; or
- if acceptance independently asserts application, add
  `required_applied_reductions: CanonicalSeq<ReductionRef>` to `TerminalDecl`
  and require the Terminal region to imply each named Reduction's active
  region.

The second choice is stronger and more auditable, and is provisionally favored.
It does not prove the Reduction theorem: K3/Analysis still interprets the exact
Reduction contract. It merely prevents K2 acceptance from asserting an
application that the schedule did not perform.

## 6. Evidence and limits

The frozen gate contains 38 findings:

| Outcome | Count |
|---|---:|
| `Affirmative` | 7 |
| `Refused` | 19 |
| `Malformed` | 1 |
| `Unsupported` | 1 |
| `CannotAnswer` | 10 |

Twenty-one mutations are rejected by both candidate and oracle. They cover
fallback, backlinks, effect/reference kinds, Claim output SSA, Reduction
inputs, overlapping linear uses, dead and ambiguous Claim states, exact
Terminal closure, required-Check occurrence, verdict, and fragment closure.

The affirmative portion supports only:

- the guard-region method for this closed fragment;
- path-sensitive alternative linear consumers;
- exact first-active Accept/Abort/Reject closure; and
- agreement with a bounded independent assignment oracle.

It does not support:

- full B2C1B5 exact Core admission or normalized owner projections;
- a general guard implication or Boolean-program theorem;
- required-Check truth or required-Reduction semantics;
- B2D runtime history or receipt replay;
- target publication or profile migration;
- live compiler/runtime correspondence;
- a formal refinement proof; or
- any Fiat--Shamir, random-oracle, hash, sponge, or QROM claim.

## 7. Next checkpoint

F0-V2B2C1B5B should first settle and encode the two missing Terminal owner
contracts. It can then extend the existing exact-byte admission, typed/cold
projection, schema-valid substitution, and six-view comparison pattern. Only
that result may move B2C coverage from 20/21 to 21/21.

Successor correction: B5B1 found that Foundation does not own a generic
qualified-result judgment. The B5A phrase suggesting a qualified
Foundation-owned implication result is superseded by a PIR-owned
Terminal-use predicate over the denotation of an authenticated Foundation
term. See
[`F0-V2B2C1B5B1 Terminal Owner Contracts`](f0v2b2c1b5b1-terminal-owner-contracts.md).

B2D remains a separate integration gate: it must combine all PCGraph classes,
first-active control, actual Check results, Claim/Reduction state transitions,
and completed Fresh records. F0-V2C publication still waits on those results.

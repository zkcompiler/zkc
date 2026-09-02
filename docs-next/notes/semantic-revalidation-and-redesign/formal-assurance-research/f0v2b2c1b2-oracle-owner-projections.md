# F0-V2B2C1B2 Oracle Owner Projections

> **Kind:** Temporary reopened-F0 constructor-isolation research result
> **State:** Complete for eight Oracle B2C families at bounded research
> resolution with
> `Affirmative/F0V2B2C1B2-A-ORACLE-OWNER-PROJECTIONS`; nine B2C families and
> both B2D integration families remain open
> **Authority:** None. This note and executable package do not change PIR, the
> Interaction profile, a semantic identity, evaluator, compiler, runtime,
> formal theorem, or Analysis judgment
> **Predecessor:**
> [`F0-V2B2C1B1 Foundation owner projections`](f0v2b2c1b1-foundation-owner-projections.md)
> **Executable gate:**
> [`evaluation/formal-source-oracle-owner-projections-f0v2b2c1b2`](../../../../evaluation/formal-source-oracle-owner-projections-f0v2b2c1b2/README.md)

## 1. Decision

The existing owner topology can represent all eight standard Oracle isolation
families without an Oracle-specific authority or transcript object:

```text
exact canonical Core candidate
  -> strict Oracle-aware admission
  -> immutable Core owner snapshot
  -> five owner-local Core views

exact paired Fresh candidate
  -> same-evaluator Protocol snapshot
  -> owner-local ExecutionView

same Core and Protocol bytes + exact references
  -> separate cold parser, graph, and projector
  -> independently derived six views

all values
  -> exact B2C1A encoding
  -> byte-for-byte comparison
```

The architecture remains `profile -> admitted owner -> purpose-bound view ->
qualified consumer judgment`. Oracle facts belong to the existing Interactive
Core and Protocol owners. A new `OracleKernel`, `FSKernel`, transcript-root
authority, semantic MLIR token, or proof-assistant-owned source would duplicate
ownership rather than strengthen it.

## 2. Executable scope and result

Eight minimal positive carriers cover the complete B2A Oracle partition:

| Family | Distinguishing owner fact |
|---|---|
| `oracle-initial-full` | Invocation-supplied origin and one full-carrier publication output. |
| `oracle-initial-binding` | Authenticated total binding algorithm with exact carrier-to-binding ABI. |
| `oracle-initial-logical` | Zero-output fixation and a finite authenticated domain law. |
| `oracle-prover-full` | One `SupplyOracle` strategy decision with full-carrier schema. |
| `oracle-prover-binding` | Prover carrier remains distinct from its public binding output. |
| `oracle-prover-logical` | Prover supplies a carrier while publication exposes no carrier-derived bytes. |
| `oracle-query-public` | Publication, Query, and Answer become exact guaranteed reads at a later decision. |
| `oracle-query-verifier-only` | Query and Answer remain VerifierPrivate and poison a dependent public sink. |

Both derivations form all six views for every carrier, producing 48 distinct
exact bodies. Every body round-trips, every sorted-unique collection follows
encoded child-body order, and repeated projection from the immutable owner
bearers is byte-identical.

A ninth carrier is a negative structural discriminator, not a ninth inventory
family. It is an admitted Interactive Core paired with a valid Fresh Protocol;
the Core has a Public logical-Oracle Answer used by an accepting Terminal. Both
projectors retain the nonempty publication influence intersection and derive
`PublicCoinEligible = false`. This separates two judgments that must not be
collapsed:

```text
Core admission + Fresh pairing          = true
same-Core Fiat--Shamir structural fit   = false
```

## 3. Design corrections exposed by the slice

### 3.1 Causal edges are not implicit transfer operands

Every Query has a publication edge and an index edge. The publication edge is
needed for lifecycle causality and for logical-access influence reachability,
but the target transfer for a Public Query is exactly
`Join(activity,index)`. Treating every incoming edge as an implicit transfer
operand changes a static Public Query into `PublicHistory` merely because it
follows publication.

Likewise, a Public Answer uses `Publish(activity)`; it does not inherit the
class of every causal predecessor. The gate now checks the edge set and the
node-local transfer law separately. F0-V2C should publish transfer rules as an
explicit function of node constructor and selected operands so an
implementation cannot infer taint by blindly joining adjacency.

### 3.2 Answer visibility is derived, not authored twice

`AnswerOracle` contains only a Query occurrence reference. Its scope and
visibility are determined by that Query. An early prototype contained a
comparison between the Query visibility and the same Query visibility reached
through its occurrence, which was tautological and provided no protection.
The corrected evaluator checks the exact earlier unmatched Query, exact scope,
guard implication, one-to-one use, and terminal ordering. Receipt visibility
is then derived once from that authenticated backlink.

The target publication should keep this single-source rule. Adding an Answer
visibility field would create an avoidable consistency obligation and a new
substitution surface.

### 3.3 An extension must preserve predecessor admission invariants

Adding Oracle constructors cannot weaken the already selected Foundation
subset. The Oracle evaluator therefore retains child-scope depth and first-
member rules, public-binding availability and uniqueness, complete public-input
binding coverage, exact direct-module ownership, terminal backlinks, and the
public-binding PCClass restriction. This is a general implementation rule for
future slices: extend one constructor family while replaying every applicable
predecessor invariant; do not replace a mature validator with a smaller local
one.

### 3.4 Query completion precedes terminal completion

One publication and one later Answer are not sufficient lifecycle checks. An
unconditional terminal between an active Query and its Answer stops execution,
so the later Answer cannot retroactively make that path total. The new
`R-ANSWER-TERMINAL-ORDER` control rejects this shape before projection. B2D
must generalize it to guarded path-sensitive totality rather than weakening it
to final table cardinality.

### 3.5 Static receipt schemas are not runtime evidence

The Protocol-owned `ExecutionView` can derive exact `Published`, `Queried`, and
`Answered` schema branches, including arity, value type, coordinate, and
visibility, from an admitted Core. It contains no carrier or observed result.
Actual carrier admission, binding evaluation, lookup, output equality,
receipt cardinality, execution order, and replay remain B2D obligations.

## 4. Mutation closure

The 44 frozen findings comprise:

| Outcome | Count |
|---|---:|
| `Affirmative` | 21 |
| `Refused` | 13 |
| `KindMismatch` | 2 |
| `CannotAnswer` | 8 |

Freshly authenticated Core mutations reject duplicate publication and Answer,
Answer scope mismatch, noncanonical domain-law order, Answer after a terminal,
wrong binding ABI, and wrong declaration kind. Schema-valid but owner-wrong
substitutions reject origin, Prover move kind, logical publication arity, and
receipt visibility. Cold projection rejects truncation, Core body/reference
substitution, cross-Core Protocol substitution, and genuine predecessor
authority issued under another evaluator fingerprint.

These tests distinguish three questions:

```text
schema validity       -> can these bytes inhabit the candidate view grammar?
owner equality        -> are these exactly the bytes determined by this owner?
runtime validity      -> did one execution produce a matching record?
```

Only the first two are in B2C1B2.

## 5. Program accounting and next gates

The B2A census assigns 21 families to B2C and two to B2D. B2C1B1 closed four
foundation families; this checkpoint closes the next eight Oracle families at
bounded research resolution. Nine B2C families remain:

| Remaining B2C slice | Families |
|---|---:|
| Claims, reductions, publication order, and challenge sharing | 5 |
| Module decision and publication classes | 3 |
| Abort plus claim Consume/Discharge terminal behavior | 1 |
| **Total** | **9** |

The recommended sequence is B2C1B3 for the five claim/reduction/challenge
families, B2C1B4 for the three module families, B2C1B5 for expanded terminal
behavior, and then B2D for integrated PCGraph and actual Fresh Oracle receipt
validation. Each slice should reuse the same immutable bearer and exact codec,
use one minimal positive plus its named negative discriminator, and carry
forward all applicable prior invariants.

B2D must explicitly pressure the distinction between graph adjacency and
transfer operands, path-sensitive Oracle completion, all four PC classes,
terminal-preemption edges, logical influence, and completed-record replay.
Only after B2C and B2D should F0-V2C decide whether to publish and rotate the
Interaction profile.

## 6. Non-claims

This checkpoint does not:

- execute, bind, query, replay, or reveal any Oracle carrier;
- validate a completed record or runtime receipt;
- close the remaining nine B2C or either B2D family;
- publish or migrate a target profile;
- establish correspondence with the current zkc compiler or runtime;
- prove the candidate projection or target semantics;
- establish binding, hiding, soundness, random-oracle, or Fiat--Shamir
  security; or
- close F1 Q1 correspondence.

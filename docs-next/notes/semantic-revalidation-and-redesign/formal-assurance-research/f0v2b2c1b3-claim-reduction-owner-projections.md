# F0-V2B2C1B3 Claim and Reduction Owner Projections

> **Kind:** Temporary reopened-F0 constructor-isolation research result
> **State:** Complete for five claim/reduction/challenge B2C families at
> bounded research resolution with
> `Affirmative/F0V2B2C1B3-A-CLAIM-REDUCTION-OWNER-PROJECTIONS`; four B2C
> families and both B2D integration families remain open
> **Authority:** None. This note and executable package do not change PIR, the
> Interaction profile, a semantic identity, evaluator, compiler, runtime,
> formal theorem, or Analysis judgment
> **Predecessor:**
> [`F0-V2B2C1B2 Oracle owner projections`](f0v2b2c1b2-oracle-owner-projections.md)
> **Executable gate:**
> [`evaluation/formal-source-claim-reduction-owner-projections-f0v2b2c1b3`](../../../../evaluation/formal-source-claim-reduction-owner-projections-f0v2b2c1b3/README.md)

## 1. Decision

The existing owner topology can represent the five Claim, Reduction,
publication-order, joint-Challenge, and shared-Challenge isolation families.
The selected shape remains:

```text
exact canonical Core bytes
  -> strict owner-local admission
  -> immutable admitted Core snapshot
  -> derived claim/reduction/challenge facts
  -> five Core-owned normalized views

same Core + exact Fresh Protocol bytes
  -> same-evaluator Fresh pairing
  -> Protocol-owned ExecutionView

same authenticated bytes + exact references
  -> separate cold parser and explicit-worklist graph/projector
  -> independently derived six view bodies
```

No new `ClaimKernel`, `ReductionKernel`, `FSKernel`, transcript-root authority,
or semantic MLIR token is justified. The declarations and schedule already
have the necessary identity and lifecycle owner. Assurance is strengthened by
making the owner-to-view derivation total, exact, and independently
checkable—not by copying the same facts into another authoritative object.

## 2. Executable scope and result

Five minimal positive carriers instantiate the complete B2A partition for
this slice:

| Family | Distinguishing owner fact |
|---|---|
| `claim-initial-linear` | An ancestor `Statement` binding creates one linear Claim, followed by one exact Terminal Consume. |
| `claim-reduction-output-reusable` | One Reduction consumes the linear input and creates one reusable output Claim at its exact occurrence and output ordinal. |
| `reduction-publication-before-after` | Guarded Prover publications before and after one required Challenge carry `Some(challenge)` and `None`, respectively. |
| `joint-challenge-group` | Two compatible joint members have dense indices and complete prior-member closure. |
| `shared-challenge-consumers` | One Shared Challenge has exactly two derived reduction-role consumers. |

The typed and cold paths form all six views for every carrier and agree on 30
distinct exact bodies. Every body round-trips, every sorted-unique sequence is
ordered by encoded child body, and repeated projection from immutable owner
bearers is byte-identical.

The frozen gate has 61 findings:

| Outcome | Count |
|---|---:|
| `Affirmative` | 18 |
| `Refused` | 30 |
| `KindMismatch` | 3 |
| `CannotAnswer` | 10 |

## 3. Design consequences

### 3.1 Claim history is derived and SSA-like, but it is not an SSA token

Each admitted Claim has exactly one creation source:

```text
InitialClaim(binding)
  -> creation at the binding's scope opening

ReductionOutput(reduction, output_ordinal)
  -> creation at the unique ApplyReduction occurrence
```

Reduction input lists and Terminal dispositions then determine the Claim's
ordered uses. This resembles SSA in one useful respect: a Claim reference has
one definition coordinate and an explicit use graph. It differs in the
important respect that a Claim is a protocol resource with linear or reusable
liveness rules, not a pure value. A linear Reduction use consumes it; a
reusable use does not eliminate the terminal obligation.

The resulting history should be a derived `ClaimReductionView`, not a second
authored use list and not a token threaded through every operation. An MLIR
token may later be a lowering device for effect ordering, but it must not
become source semantic authority or stand in for the exact Core Claim graph.

### 3.2 Last-Challenge is the reduction-to-Fiat--Shamir bridge

For every Reduction-owned publication `p`, admission computes the least
required Challenge after `p`:

```text
next(p) = least c in reduction.required_challenges
          with position(p) < position(c)
```

The authored `next_challenge` must equal that value, using `None` exactly when
the set is empty. The first publication in the positive carrier therefore
maps to its later Challenge, while the response publication after that
Challenge maps to `None`.

This is more than local schedule hygiene. A Fiat--Shamir construction can add
`p` to `RequiredInfluence(c)` mechanically. It prevents a prover publication
that occurs before a later batching or reduction Challenge from being
misclassified as post-challenge material and omitted from that Challenge's
hash dependence. Later cumulative transcript state then carries the influence
forward. The Core owns the reduction-round fact; the FS construction owns how
that required influence is encoded and checked.

### 3.3 Challenge consumers must not be authored twice

`ReductionConsumers(c)` is the sorted-unique sequence of Reduction references
whose exact `required_challenges` sequence contains `c`, ordered by the unique
`ApplyReduction` occurrence. `Exclusive` requires at most one such consumer;
`Shared(contract)` requires at least two.

Equal Challenge values, matching domains, ordinary dataflow uses, or two
declarations with similar metadata do not create a reduction-role consumer.
This distinction prevents accidental sharing from being inferred by value
equality and prevents a stale authored consumer table from disagreeing with
the Reduction declarations.

### 3.4 Graph adjacency and node-local transfer remain separate

The Claim/Reduction PCGraph contains causal edges for Claim creation, Claim
use, side inputs, required Challenges, required publications, Reduction state,
joint prior members, and terminal disposition. Challenge effects nevertheless
use an explicit public-coin transfer over their selected operands. As in the
Oracle slice, the implementation must not infer a class transfer by blindly
joining every causal predecessor.

The cold path reconstructs this graph with its own heap/worklist traversal and
agrees on all encoded nodes, edges, topological order, classes, sinks, and
acceptance coordinates for the five carriers.

### 3.5 Four judgments remain distinct

The slice preserves the following separation:

```text
Core admission
  != Fresh Protocol pairing
  != same-Core FS structural eligibility
  != a Fiat--Shamir security theorem
```

All five positive carriers pass the first three bounded checks. That fact does
not select BCS, RBR, duplex-sponge, concrete-instantiation, or QROM hypotheses,
and it proves no theorem in any of those regimes.

### 3.6 Static closure is not path-sensitive liveness

The bounded evaluator uses one unconditional final Terminal fallback and a
static live-Claim calculation adequate for these isolation carriers. It does
not solve guarded execution paths, first-active-terminal preemption, per-path
Claim consumption, or accepting-path Reduction saturation. Weakening the
target semantics to this finite model would be unsound. B2C1B5 must isolate
expanded Terminal behavior, and B2D must integrate path-sensitive run and
receipt validation.

## 4. Mutation closure

Twenty-five freshly authenticated Core mutations cover invalid initial Claim
sources, declaration-kind and output-contract mismatches, missing or duplicate
output Claims, empty Reduction inputs, missing or duplicate backlinks, output
cycles, publication closure/kind/order errors, wrong Last-Challenge labels,
duplicate required Challenges, guard weakening, broken joint index/prior/type
closure, invalid Shared or Exclusive consumer cardinality, linear double use,
and incomplete or duplicate Terminal dispositions.

Four additional values deliberately remain valid instances of the candidate
view schemas while substituting the wrong owner-derived Claim usage, creation
coordinate, Last-Challenge mapping, or Shared-consumer list. This preserves the
three-level distinction:

```text
schema validity   -> can the bytes inhabit the candidate grammar?
owner equality    -> are they the unique bytes derived from this owner?
runtime validity  -> did a concrete execution produce a matching record?
```

B2C1B3 establishes bounded evidence for the first two only. Cold controls also
reject truncated Core bytes, Core body/reference substitution, cross-Core
Protocol substitution, and a genuine B2C1B2 authority bearer used under the
B2C1B3 projection law.

## 5. Program accounting and next gates

B2C1B1, B2C1B2, and this slice now cover 17 of the 21 B2C pressure families at
bounded research resolution:

| B2C slice | Families | State |
|---|---:|---|
| Foundation | 4 | Complete, bounded |
| Oracle | 8 | Complete, bounded |
| Claim/Reduction/Challenge | 5 | Complete, bounded |
| Module decision/publication | 3 | Open as B2C1B4 |
| Expanded Terminal behavior | 1 | Open as B2C1B5 |
| **Total** | **21** | **17 covered, 4 open** |

B2C1B4 should test `NoDecision`, `ProverDecision`, and
`ProverPublication` module effects without adding module-specific ownership.
B2C1B5 should then isolate Reject/Abort, Consume/Discharge, guarded terminal
preemption, and path-sensitive Claim/Reduction closure. B2D follows with
integrated all-class PCGraph pressure and completed Fresh run/receipt
validation. F0-V2C may decide publication and profile rotation only after
those gates expose no unresolved owner-body contradiction.

## 6. Non-claims

This checkpoint does not:

- execute a Reduction, sample a Challenge, mutate a runtime Claim, or validate
  a completed run history;
- close path-sensitive liveness or accepting-path Reduction saturation;
- close the remaining four B2C or either B2D family;
- publish or migrate a target profile;
- establish correspondence with the current zkc compiler or runtime;
- prove the candidate projection, a compiler refinement, or target semantics;
- establish soundness, a random-oracle theorem, Fiat--Shamir security, or a
  concrete hash/sponge claim; or
- close F1 Q1 correspondence.

## 7. Successor checkpoint

The planned B2C1B4 module slice is now complete at bounded research resolution:
[`F0-V2B2C1B4 Module Owner Projections`](f0v2b2c1b4-module-owner-projections.md)
adds the three semantic-module families without changing this checkpoint's
historical 17-of-21 accounting. The successor makes exact used-module
preimage availability part of the projection source contract and leaves only
the expanded-terminal B2C family open.

# F0-V2B2C1B1 Foundation Owner Projections

> **Kind:** Temporary reopened-F0 constructor-isolation research result
> **State:** Complete for four foundation families at bounded research
> resolution with
> `Affirmative/F0V2B2C1B1-A-FOUNDATION-OWNER-PROJECTIONS`; seventeen B2C1B
> families and both B2D integration families remain open
> **Authority:** None. This note and executable package do not change PIR,
> the Interaction profile, a semantic identity, evaluator, compiler, runtime,
> formal theorem, or Analysis judgment
> **Predecessor:**
> [`F0-V2B2C1A exact view-value codec`](f0v2b2c1a-exact-view-value-codec.md)
> **Executable gate:**
> [`evaluation/formal-source-owner-projections-f0v2b2c1b1`](../../../../evaluation/formal-source-owner-projections-f0v2b2c1b1/README.md)

## 1. Decision

B2C1B should proceed as several constructor-isolation slices, not as one large
Core whose interactions can conceal compensating errors. The first slice is
now executable for four foundation families:

```text
exact canonical Core candidate
  -> strict decode, authentication, and supported admission
  -> immutable Core owner snapshot
  -> reference derivation of five Core views

same Core bytes + exact Core reference
  -> separate cold parser, graph, and projector
  -> independently derived five Core views

exact paired Fresh candidate
  -> same-evaluator Fresh admission
  -> reference and cold ExecutionView

all six values
  -> exact B2C1A target encoding
  -> byte-for-byte equality
```

The result is affirmative only for this bounded slice. It shows that the
selected B2B schemas, B2C0 authority substrate, and B2C1A exact codec can be
composed into owner-derived bodies without introducing a new semantic owner.
It does not yet justify target publication.

## 2. Executable scope and result

Six minimal fixtures distinguish the four families:

| Fixture | Boundary exercised |
|---|---|
| `verifier-private-dead` | An unused private source reaches no public sink and does not poison eligibility. |
| `verifier-private-sink` | Private influence reaching an accepting terminal is retained by source and makes eligibility false. |
| `public-history-binding-observation` | A child binding observes an earlier unconditional Prover output and retains the exact `PublicHistory` binding sink. |
| `constant-and-derived-value` | Constant and derived producers, direct predecessors, static reads, and terminal use are owner-derived. |
| `child-scope-and-nontrivial-guard` | Complete scope paths, before-opening visibility, a nontrivial guard, and guarded dependency are retained. |
| `deterministic-verifier-message` | A total deterministic Verifier output is public, typed, graph-retained, and visible to a later Prover decision. |

For each fixture, both projectors produce all six views. The gate therefore
compares 36 exact bodies; all 36 are distinct, fully decode and re-encode,
obey exact target-byte collection order, and remain stable under reprojection.
The cold projector does not import the reference projector. It starts from
complete profiled Core and Protocol bodies plus their exact references. It
independently reconstructs both identities, checks the selected profile, Fresh
interpretation, and exact Protocol-to-Core dependency, and then loads separate
Foundation, schema, and codec module instances.

This boundary is mutation-tested in both directions: a valid body paired with
another reference refuses, and a self-authenticating Fresh Protocol paired
with another admitted Core also refuses. Agreement therefore does not rely on
the harness silently preserving body/reference or Protocol/Core pairing.

The frozen 39 findings are:

| Outcome | Count |
|---|---:|
| `Affirmative` | 15 |
| `CannotAnswer` | 8 |
| `KindMismatch` | 3 |
| `Malformed` | 1 |
| `Refused` | 11 |
| `Unsupported` | 1 |

Schema validity is deliberately not treated as owner equality. One negative
control changes only the derived eligibility Boolean. Both exact codecs accept
the alternate value as schema-valid, but owner rederivation produces different
bytes and rejects the substitution. This is the intended division:

```text
schema + codec       -> is this a well-formed value?
owner projection     -> is this the value determined by this owner?
```

## 3. Design corrections exposed by the slice

### 3.1 Keep source predecessors separate from taint closure

The B0 normalized contract defines
`verifier_private_predecessors` as exactly the
`VerifierPrivateInputNode(i)` sources that reach a sink. An early B2C1B1
prototype incorrectly placed every private-tainted descendant in that field.
The corrected split is:

```text
PCGraph.classes
  = classification for every node, including private-tainted descendants

PublicCoinView.verifier_private_predecessors
  = private input source nodes from which some sink is reachable
```

The dead and terminal fixtures make this distinction executable. An unused
source yields an empty predecessor set. A private source reaching the terminal
observation yields exactly that source node, while descendant classifications
remain in the retained graph.

### 3.2 Sinks retain the exact public observation coordinate

The owner graph retains a binding's exact `BindingObservationNode` as the
public observation coordinate. The positive fixture binds an earlier
unconditional Prover output, so its dependency class is `PublicHistory` and
the Core remains structurally public-coin eligible. Section 4.3 of the target
source separately forbids a public binding whose dependency class is
`VerifierPrivate` or `Invalid`; a negative private-derived binding candidate
is therefore refused during Core admission rather than projected as an
ineligible binding. By contrast, a private-derived terminal output remains a
valid general Interactive Core and makes public-coin eligibility false.

The same rule prevents an effect coordinate from standing in for a produced
public value. A deterministic Verifier message contributes its exact
`OccurrenceOutputNode`; a terminal public output contributes its exact value-
producer node; and the terminal decision remains a separate sink. Public
outputs of an accepting terminal also appear in `AcceptanceSinks`. The gate
checks these coordinates directly, even though several alternatives would
produce the same final Boolean on the small fixtures.

### 3.3 Availability is checked at the binding boundary

A child scope opened immediately before occurrence `o` cannot bind an output
created by `o`. Merely checking that a referenced output exists in the whole
Core is insufficient. The admission slice now rejects this mutation before
projection.

### 3.4 Core and Fresh authority share one evaluator extension

B2C1B1 extends the supported Core carrier beyond B2C0. Its Fresh Protocol
handle must therefore be issued by the same extended evaluator fingerprint.
Reusing a genuine B2C0 Fresh capability would authenticate the wrong
evaluator/projection law. The package forms the Fresh bearer under the same
owner lifecycle and rejects a foreign predecessor bearer. Projection also
rechecks the Protocol issuer, evaluator, profile, identical Core bearer, and
closure fingerprint rather than relying only on construction-time checks. It
does not add a new top-level stage or authority.

## 4. Program accounting

The B2A census assigns 21 families to B2C and two to B2D. This checkpoint
closes four B2C families at bounded research resolution and leaves seventeen:

| Remaining B2C1B slice | Families |
|---|---:|
| Oracle origin, publication, query, and visibility | 8 |
| Claim, reduction, publication order, and challenge sharing | 5 |
| Module decision and publication classes | 3 |
| Abort plus claim Consume/Discharge terminal behavior | 1 |
| **Total** | **17** |

B2D still owns the two integrated families: all-class invalid-private/logical
PCGraph interaction and Fresh runtime Oracle receipts. Facts needed to admit a
minimal B2C carrier may be tested locally, but no per-family result substitutes
for those integrated gates.

## 5. Main-design consequence

The present evidence continues to favor the existing ownership topology:

```text
Interaction profile
  -> exact admitted Core/Protocol owner
  -> purpose-bound six-view projection law
  -> qualified Analysis source question
```

No `FormalKernel`, view registry, transcript-root authority, semantic MLIR
token, or proof-assistant-owned source is needed for this slice. F0-V2C should
instead publish the exact schema/value interpretation and projection laws with
the existing PIR owners, including the four corrections above, so a cold
implementation can derive the same bodies from authenticated source.

This remains provisional. In particular, exact projection into the selected
normalized `PIRValueEntry` schema does not prove that direct value predecessors
are sufficient for every whole-subject Analysis question. F1-R1C must still
test question-relative read closure after publication; a counterexample may
reopen the source schema rather than being hidden in an exporter.

## 6. Next gates and non-claims

The next B2C1B slice should cover the eight Oracle lifecycle families using the
same pattern: one minimal positive carrier and named discriminator per family,
strict owner admission, reference and cold projection, exact six-body
comparison, and fail-closed deferral of runtime receipts to B2D.

This checkpoint does not:

- close the remaining seventeen B2C families or either B2D family;
- execute Oracle runtime behavior or validate runtime receipts;
- publish or migrate an Interaction profile;
- establish correspondence with the current zkc compiler or runtime;
- prove the candidate projection, schema sufficiency, or theorem truth;
- establish a Fiat--Shamir or other cryptographic property; or
- close F1 Q1 correspondence.

## 7. Successor status

[`F0-V2B2C1B2`](f0v2b2c1b2-oracle-owner-projections.md) subsequently closes
the eight Oracle isolation families at bounded research resolution and leaves
nine B2C families plus both B2D families open. It also sharpens one graph-law
point for future publication: causal edges are retained independently of the
constructor-selected operands used by a node's `PCClass` transfer.

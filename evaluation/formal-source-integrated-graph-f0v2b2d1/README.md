# F0-V2B2D1 integrated PublicCoin graph closure

This package integrates every `PCNode` and `PCClass` branch into one bounded
candidate-Core family and derives the complete `PublicCoinView`. It closes the
`pcgraph-invalid-private-logical` B2D pressure family at research resolution.
It deliberately leaves `fresh-runtime-oracle-receipts` to the separately named
F0-V2B2D2 checkpoint.

Run from the repository root:

```sh
python3 -B evaluation/formal-source-integrated-graph-f0v2b2d1/run.py --check
```

The frozen result is
`Affirmative/F0V2B2D1-A-INTEGRATED-PCGRAPH-CLOSURE`: 42 findings over five
exact candidate bodies.

## Integrated carrier

Each carrier has the same complete table census:

| Core table | Count |
|---|---:|
| public / Verifier-private inputs | 4 / 1 |
| constants / derived values | 2 / 3 |
| scopes / public bindings | 2 / 5 |
| Challenges / Oracles | 3 / 3 |
| Checks / Claims / Reductions | 1 / 3 / 2 |
| Terminals / occurrences | 3 / 23 |

The occurrences integrate guarded deterministic Verifier and Prover messages;
all three semantic-module decision classes; FullCanonical, PublicBinding, and
LogicalAccess Oracles; public and Verifier-only queries and answers;
independent and joint Challenges; shared and exclusive reduction use; a Check;
two Reductions; and first-active Accept, Abort, and Reject terminals. Every one
of the fourteen `PCNode` tags and all four classes is inhabited.

The baseline graph has 91 nodes and 151 edges. Its class distribution is 55
`StaticPublic`, 28 `PublicHistory`, five `VerifierPrivate`, and three `Invalid`.
Only the 49 derived sinks matter to eligibility; all are public, the private
input reaches no sink, each Challenge passes its specialized transfer and
observation-order check, and the LogicalAccess influence cone has empty
intersection with the nine acceptance sinks.

## Independent evidence paths

The typed path authenticates complete candidate Core and Fresh Protocol bytes,
the exact profile/module/algorithm/contract closure, and an immutable
process-local Core authority. From that authority it derives nodes, edges,
canonical Kahn order, lattice classes, sinks, Challenge checks, LogicalAccess
cones, and the final view.

The cold path does not import the typed D1 model. It separately:

1. compiles the pinned B5B2 owner-view grammar;
2. authenticates full Core and Protocol body/reference pairs;
3. parses all fourteen Core tables into ordinary records;
4. authenticates every used semantic-module body and portable-algorithm
   preimage;
5. reconstructs module-owned dependency and transfer declarations; and
6. independently derives and encodes the complete graph and Challenge rows.

The paths agree on every evidence table and on five exact `PublicCoinView`
bodies totaling 237,299 bytes. Every body round-trips, reprojection is
deterministic, and all target `sorted-unique` sequences use target-byte order.

## Negative discriminators

Four exact neighboring carriers isolate structurally important failures:

| Carrier | Decisive reason for refusal |
|---|---|
| `private-verifier-output-sink` | a Verifier-private input reaches a public Verifier-message output sink |
| `invalid-module-control-sink` | an acceptance-relevant module control depends on a prover-internal output |
| `history-challenge-condition` | a Challenge condition is `PublicHistory`, not `StaticPublic` |
| `logical-reject-preemption` | a logical answer guards an early Reject whose terminal decision controls a later fallback Accept |

The last case is deliberately control-aware. The graph contains the exact
terminal-preemption edges and therefore finds one node in the logical
influence/acceptance intersection; inspecting only the fallback Accept's direct
operands would miss it.

Five schema-valid substitutions remove an ordinary edge, alter a class, remove
a sink, remove a terminal-preemption edge, or invent a logical intersection.
All still encode under the structural schema, but the owner rejects each as a
non-equal claim. Further controls reject an unknown but authenticated Core,
Core-ID/body and cross-Core Fresh substitutions, truncated bytes, incomplete
algorithm closure, a substituted module body, contract drift, and copied or
serialized admission authority.

## Design findings before target migration

Integration exposed two wording obligations in the target text. They are
recorded as `CannotAnswer`, not silently resolved as new authority:

- A LogicalAccess publication has no publication output, but its public
  fixation marker is the publication *effect*. The candidate classifies that
  effect as `Publish(activity)`. Section 11 should say this explicitly rather
  than only specifying "Oracle publication output."
- `PCSinks` says "public Query index." The candidate includes both the public
  Query effect/activity observation and the index producer. Target migration
  should state those exact coordinates so two conforming implementations
  cannot retain different sink sets.

These clarifications do not require a new subsystem. They belong to the
existing PIR graph and projection owner and should be resolved before profile
publication in F0-V2C.

## Result boundary

This is finite construction, differential, mutation, and canonical-byte
evidence. It supports the structure

```text
candidate profile
  -> exact Core admission
  -> owner-derived PublicCoinView
  -> structural FS eligibility
```

for five exact carriers only. It is not:

- the remaining B2D Fresh execution/Oracle-receipt/replay result;
- target-profile publication or migration;
- live compiler, runtime, generated-verifier, backend, or host-module
  correspondence;
- a mechanized refinement or analyzer proof;
- reduction truth, protocol soundness, Fiat--Shamir security, random-oracle,
  concrete hash/sponge, or QROM evidence; or
- F1 Q1 source correspondence.

F0-V2B2D2 should now test exact Fresh run records, every Oracle receipt branch,
output arity and visibility, replay equality, and terminal completion. F0-V2C
should consume both D1 and D2 rather than promoting either temporary package
wholesale.

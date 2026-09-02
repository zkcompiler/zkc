# F0-V2B2D1 Integrated PublicCoin Graph Closure

> **State:** `Affirmative/F0V2B2D1-A-INTEGRATED-PCGRAPH-CLOSURE` for the
> bounded D1 carrier; one of two B2D families closed
> **Authority:** None. The experiment neither edits nor publishes target PIR
> semantics or profile identities.
> **Executable evidence:**
> [`evaluation/formal-source-integrated-graph-f0v2b2d1`](../../../../evaluation/formal-source-integrated-graph-f0v2b2d1/README.md)

## 1. Question and answer

B2C established each owner-projection constructor in isolation. That is not
enough to show that their graph edges, transfer rules, sink selection,
first-active control, and LogicalAccess exclusion compose coherently.
F0-V2B2D therefore has two distinct obligations:

1. D1: integrated static `PCGraph` and `PublicCoinEligible` closure;
2. D2: Fresh runtime records, all Oracle receipt branches, and replay.

D1 is affirmative for five exact candidate Core bodies. The owner evaluator
and a byte-independent projector agree on the complete graph evidence and
encoded `PublicCoinView`. One positive carrier passes structural FS admission;
four minimally directed neighbors refuse for distinct private, invalid,
Challenge-transfer, and logical-control reasons.

This result closes only `pcgraph-invalid-private-logical`. The
`fresh-runtime-oracle-receipts` family remains `CannotAnswer` until D2.

## 2. Why integration matters

Constructor-local tests can all pass while a composed implementation remains
wrong. Examples include:

- omitting a dependency when two owners meet at one occurrence;
- assigning the right local transfer to the wrong graph coordinate;
- retaining a public output but omitting the activity that controls whether it
  exists;
- ignoring first-active terminal preemption because it is not an ordinary data
  edge; or
- checking a LogicalAccess answer only against direct accepting-terminal
  inputs, thereby missing its control path through an earlier Reject.

The D1 carrier makes these interactions simultaneous. Its 23 occurrences
cover messages, three extension-effect classes, all Oracle modes and both query
visibilities, three Challenge relationships, Check/Claim/Reduction flow, and
three terminal verdicts. The resulting graph contains all fourteen node cases
and all four lattice classes.

## 3. Selected owner architecture

D1 supports the existing ownership split rather than a new FS kernel:

```text
authenticated profile and dependency closure
  -> PIR Core owner admits exact bytes
  -> PIR owner derives PCGraph, classes, sinks, and Challenge facts
  -> exact PublicCoinView body
  -> Compiler or deployment policy may require structural eligibility
```

The view is evidence derived from an admitted Core. It is not authored input,
an ambient assertion, or a new semantic authority. The structural FS decision
is likewise not a theorem about the transformed protocol. A later Analysis
judgment may add a regime-specific theorem only after its proposition,
assumptions, applicability, and proof evidence are independently qualified.

Semantic-module declarations fit the same structure. Their authenticated
dependency and transfer declarations tell PIR how to project a module effect;
they do not prove that host code obeys those declarations. Realization and
Evidence retain the separate implementation-correspondence obligation.

## 4. Exact evidence design

The typed path starts from the B5B2 synthetic Interaction revision 2 and
authenticates exact Core, profile, module, algorithm, and evaluation-contract
closure. It admits one immutable process-local authority and projects the
view from retained canonical bytes.

The cold path shares no typed D1 evaluator objects. It authenticates the Core
and Fresh Protocol references, decodes all fourteen tables, authenticates all
semantic-module bodies and algorithm preimages, interprets the module-owned
edge laws, and rebuilds:

- the complete node and edge sets;
- target-byte-minimal Kahn topological order;
- the four-class lattice assignment;
- all public and acceptance sinks;
- private-input reachability;
- per-LogicalAccess influence and intersection sets;
- per-Challenge specialized transfer validity; and
- challenge-before-dependent-prover-decision order.

Equality is checked over every table and over the final canonical bytes. It is
not reduced to agreement on one eligibility Boolean.

## 5. Results

| Carrier | Nodes / edges | Class counts S/H/P/I | Private predecessors | Logical acceptance intersection | Eligible |
|---|---:|---:|---:|---:|---|
| baseline | 91 / 151 | 55 / 28 / 5 / 3 | 0 | 0 | yes |
| private Verifier-output sink | 91 / 151 | 53 / 28 / 7 / 3 | 1 | 0 | no |
| invalid module-control sink | 91 / 151 | 55 / 28 / 5 / 3 | 1 | 0 | no |
| history Challenge condition | 91 / 151 | 54 / 12 / 5 / 20 | 0 | 0 | no |
| logical Reject preemption | 91 / 146 | 54 / 29 / 5 / 3 | 0 | 1 | no |

Here S/H/P/I abbreviate `StaticPublic`, `PublicHistory`, `VerifierPrivate`, and
`Invalid`. The baseline contains 49 sinks and nine acceptance sinks. Its unused
Verifier-private input is harmless because it reaches neither set.

The four negative carriers establish different facts:

- deterministic Verifier output does not sanitize a private dependency;
- an acceptance-relevant control can make an otherwise private module branch
  structurally invalid;
- a public history value is still not a static Challenge condition; and
- terminal preemption carries logical influence into later acceptance even
  when the fallback Accept has no direct Oracle operand.

Five schema-valid owner substitutions show why structural validation is not
owner truth. Removing an edge or sink, changing a class, deleting a
terminal-preemption edge, or inventing a logical intersection all produces a
well-shaped body; exact owner comparison refuses all five.

## 6. Target clarifications exposed by D1

The experiment intentionally returns `CannotAnswer` for two target-text
details. Both must be settled before F0-V2C publishes identities.

### 6.1 LogicalAccess fixation transfer

LogicalAccess has no publication output, while its fixation marker is itself a
public history observation. The generic transfer paragraph says that an
"Oracle publication output" uses `Publish(activity)`, which does not literally
name the zero-output publication-effect node. D1 assigns
`Publish(activity)` to that effect node so the marker cannot collapse into a
static fact. The target should make this coordinate explicit.

### 6.2 Public Query sinks

`PCSinks` names a "public Query index" but can be read as naming only the index
producer. D1 retains the Query activity/effect as the public observation and
also retains the index producer. The target should enumerate these coordinates
directly. Otherwise implementations could agree on visible behavior while
serializing different sink sets and `PublicCoinView` bodies.

These are owner-local wording fixes, not evidence for introducing a
transcript-root authority, semantic token, or `FSKernel`.

## 7. D2 handoff

D2 should reuse the exact D1 admitted carriers and add runtime evidence without
changing the D1 owner boundary. Its positive matrix should include:

- Fresh Challenge receipts for all three Challenge declarations;
- FullCanonical and PublicBinding publication receipts;
- public and Verifier-only Query/Answer receipts;
- LogicalAccess fixation and public-answer branches;
- exact occurrence/output arity and value type;
- first-active terminal completion and public outputs; and
- independent replay equality against the complete record.

Negative cases should alter one receipt branch, coordinate, visibility, arity,
type, value, order, or stopping terminal at a time. Missing evidence must remain
`CannotAnswer` or refusal; D2 must not infer a successful run from the static
D1 view.

## 8. Nonclaims and migration consequence

The 42-finding D1 aggregate is finite executable evidence, not a mechanized
proof. It does not establish target publication, general Core admission,
runtime correctness, compiler or backend correspondence, host-module
conformance, relation truth, protocol soundness, Fiat--Shamir security,
random-oracle or concrete-sponge assumptions, QROM applicability, or F1 Q1.

F0-V2C should wait for D2, resolve the two wording obligations, regenerate the
candidate profile and its dependent identity cone from the authoritative
source, and migrate only the selected owner contracts. The temporary D1
package should not be merged wholesale into normative semantics.

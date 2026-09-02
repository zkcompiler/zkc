# F2-O1 integrated provider-observable audit

This package asks one exact question:

> Does the exact D1 `integrated-baseline` Core and Fresh Protocol, through the
> normalized owner-view bodies actually issued for that authority, determine
> every operational observable needed to render all 23 Core occurrences as one
> generic VCVio `OracleComp`/`ProbComp` interaction?

Run from the repository root:

```sh
python3 -B evaluation/formal-provider-observables-f2o1/run.py --check
```

The frozen result is
`CannotAnswer/F2O1-C-MISSING-OPERATIONAL-OBSERVABLE`. The exact missing list is
frozen in `expected-findings.json` and reproduced in the command output.

## Subject and source boundary

The subject is D1's exact admitted `integrated-baseline` Core
`zkcidv0:pir.interactive-core:02cb7cce9cc67a6495b078418147f6a7f50fcbc8ca643a4cd88f41660596b45f`
paired to its exact Fresh Protocol
`zkcidv0:pir.protocol:802dd782f76d9a761820fe6b45e824434eb4fe6fd9f3aab714ba9cd40f3b7328`.
It carries 23 occurrences, including all three semantic-module decision
classes, all three Oracle publication modes, Public and Verifier-only queries,
independent and joint Challenges, shared and exclusive reduction use, three
Claims, two Reductions, and first-active Accept, Abort, and Reject terminals.

The audit found an important source boundary. B5B2 supplies the six-view grammar
and derives six bodies for its own terminal fixture. D1 compiles that grammar
but, for its five integrated carriers, implements only
`project_public_coin` (`model.py:2330-2381`). It does not issue integrated
`PublicBindingView`, `StrategyDecisionView`, `EffectView`,
`ClaimReductionView`, or `ExecutionView` bodies. The target prose at
`docs-next/pir/interactive-core.md:2046-2174` describes all six target bodies,
but prose and a schema grammar are not an issued body for the D1 authority.
The generator therefore uses only D1's exact `PublicCoinView` leaves as source
coordinates. It records every would-be coordinate in the other five views as
`no_source_coordinate`; it never substitutes the B5B2 fixture's leaves.

## Generated interaction and ledger

`generator.py` emits:

- `generated/Integrated.lean`, a generic `ProbComp` do-block (`ProbComp` is
  VCVio's `OracleComp unifSpec`) with one operation per Core occurrence;
- `generated/ledger.json`, with one entry per construct mapped to exactly one
  active D1 `PublicCoinView` leaf or one typed gap.

The rendering is intentionally not Schnorr-shaped. Abstract operations cover
Verifier and Prover messages, all semantic-module effects, Oracle publication,
query, and answer events, Challenge sampling, Check invocation, Reduction
application, and terminal guards. Challenge 0 is sampled once and the same Lean
value is supplied to both Reductions. Joint Challenge 2 receives joint member 1
as its prior member. Accept and Abort guards precede the fallback Reject in one
nested first-active branch.

The ledger has 93 constructs. Thirty-two have distinct coordinates among the
906 active leaves of D1's integrated `PublicCoinView`; 61 are typed gaps. Of
those gaps, 56 are operational and five are property premises. The operational
classes are:

- `operational-owner-view`: the required integrated owner-view body was not
  issued by D1;
- `operational-distribution`: a Fresh-law reference does not denote a runtime
  distribution;
- `operational-denotation`: an algorithm, guard, Check, or Reduction reference
  does not denote a provider operation;
- `module-effect-denotation`: the authenticated semantic-module classification
  does not provide its provider transition;
- `oracle-carrier-representation`: an Oracle mode does not choose a provider
  table, binding, or logical-access carrier and lookup implementation; and
- `operational-outcome-map`: no issued view maps every completion and
  noncompletion branch to the generated verdict.

`property-premise` remains separate: structural Claim or Reduction leaves would
not prove the three Claim predicates or the two Reduction obligations. Missing
evidence is not converted into a positive or negative property claim.

## Independent checker and mutations

`checker.py` shares no code with the generator. It uses D1's cold path to
authenticate and byte-decode the complete Core and Fresh Protocol, authenticate
their module and algorithm closure, independently derive `PublicCoinView`, and
enumerate its active leaves. It checks:

- totality over the exact 23-occurrence schedule and the complete observable
  inventory;
- injection over claimed leaves and validity of claimed and naming
  coordinates;
- exact source-versus-gap classification and top-level gap enumeration;
- one marker per ledger construct, exact marker lines, and schedule order;
- the three module decision classes, three Oracle modes, both query
  visibilities, Challenge correlation and sharing, Reduction backlinks, and
  fallback-terminal preemption.

Six mutations fail with distinct stable codes:

| Mutation | Required checker failure |
|---|---|
| duplicate the shared Challenge into two draws and feed one to each Reduction | `F2O1-R-SHARED-CHALLENGE-DUPLICATED` |
| reorder an interleaved Query and Answer | `F2O1-R-SCHEDULE-ORDER` |
| drop a Reduction's required-Challenge backlink | `F2O1-R-REDUCTION-CHALLENGE-BACKLINK` |
| render LogicalAccess as FullCanonical | `F2O1-R-ORACLE-MODE-MISMATCH` |
| move the Verifier-only Query to Public | `F2O1-R-QUERY-VISIBILITY` |
| omit one fallback-Accept preemption dependency | `F2O1-R-TERMINAL-PREEMPTION` |

The checker cold-projects all four D1 neighbours as controls and confirms that
all remain ineligible. The `logical-reject-preemption` neighbour supplies the
brief's fallback-Accept mutation (the baseline's fallback is Reject). The
neighbours are not emitted as four additional interactions because none
supplies the five missing integrated view projections; they therefore cannot
close this audit's source-coordinate question.

## Elaboration receipt

`elaboration-receipt.json` records successful elaboration under VCVio revision
`de0a3108140e3e04a7ebf0075aa110b459ee6e8a` and Lean v4.33.1. The receipt is
bound to both generated artifacts by SHA-256. Ordinary `--check` verifies the
receipt without requiring `/tmp/zkc-f0-sources.b66lUO/VCVio`; use
`--elaborate` only to refresh it in that checkout.

## What a pass establishes

A pass establishes, for this exact finite subject, that the generator is
byte-reproducible; the independent checker authenticates the subject; all 23
occurrences and the integrated discriminators are represented; every claimed
coordinate is an active, non-aliased D1 `PublicCoinView` leaf; every remaining
construct is explicitly enumerated as a typed gap; all six mutations are
rejected by name; and the committed Lean file elaborated in the pinned provider
environment.

It does **not** establish that the generated operations implement PIR
denotations, that the five missing views can be reconstructed, provider/PIR
trace correspondence, runtime or replay correspondence, Claim or Reduction
truth, protocol soundness or completeness, Fiat--Shamir security, ROM/QROM
applicability, live compiler/backend correspondence, or a target owner-page
change. The generated Lean is parametric syntax, and its empty axiom closure is
only an elaboration fact.

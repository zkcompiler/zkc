# F0-V2B2D3 integrated six-owner-view projection

This package asks one exact question: do the typed owner path and an
independent cold canonical-byte path agree on all six normalized owner-view
bodies for each of the five D1 carriers, and how many F2-O1
`operational-owner-view` gaps close when its checker is rerun over that
complete leaf universe?

Run from the repository root:

```sh
python3 -B evaluation/formal-source-integrated-views-f0v2b2d3/run.py --check
```

The frozen result is
`Affirmative/F0V2B2D3-A-INTEGRATED-SIX-VIEWS`. The two paths agree byte for
byte and round-trip on all 30 carrier/view pairs. The resulting 8,402-leaf
five-carrier universe closes exactly 40 of F2-O1's gaps: all and only those in
the `operational-owner-view` class.

## Projection composition

The typed path starts with exact D1 Core and Fresh Protocol authority. It keeps
D1's `PublicCoinView` projector unchanged and composes the other five bodies
from the checked constructor-local laws:

- B1 for Core identity, scope, binding, message, value, read, and runtime
  structure;
- B2 for every Oracle mode, origin, effect, visibility, lifecycle, and
  strategy move;
- B3 for independent and joint Challenges, shared and exclusive reduction
  use, Claims, Reductions, and publication requirements;
- B4 for admitted module-effect atoms and all three module decision classes;
  and
- B5B2 for Checks, expanded Terminal rows, first-active requirements, the
  candidate profile laws, and the final six-view grammar.

The cold path does not import the typed D1 or D3 model. It authenticates exact
Core, Protocol, module-source, portable-algorithm, and evaluation-contract
bytes through D1's independent parser, then invokes the corresponding cold
B1--B5B2 encoders. B4's cold parser supplies the admitted module-effect atom;
D1's cold graph projector supplies `PublicCoinView`.

The integrated constructor census includes both message directions, all three
module decision classes, FullCanonical/PublicBinding/LogicalAccess Oracles,
public and Verifier-only Queries, Answers, independent and joint Challenges,
shared Challenge use by two Reductions, Claims, a Check, and first-active
Accept/Abort/Reject Terminals.

## Frozen body and leaf matrix

Each cell is `canonical bytes / active leaves`. Exact SHA-256 body digests are
frozen in `expected-findings.json`.

| D1 carrier | PublicBinding | StrategyDecision | PublicCoin | Effect | ClaimReduction | Execution |
|---|---:|---:|---:|---:|---:|---:|
| `integrated-baseline` | 3,079 / 35 | 39,370 / 250 | 47,403 / 906 | 47,397 / 280 | 7,781 / 93 | 22,724 / 117 |
| `private-verifier-output-sink` | 3,079 / 35 | 39,370 / 250 | 47,438 / 907 | 47,397 / 280 | 7,781 / 93 | 22,724 / 117 |
| `invalid-module-control-sink` | 3,079 / 35 | 39,370 / 250 | 47,610 / 911 | 47,397 / 280 | 7,781 / 93 | 22,724 / 117 |
| `history-challenge-condition` | 3,079 / 35 | 39,370 / 250 | 47,696 / 912 | 47,448 / 280 | 7,781 / 93 | 22,775 / 117 |
| `logical-reject-preemption` | 3,079 / 35 | 39,370 / 250 | 47,152 / 904 | 47,273 / 276 | 7,522 / 85 | 22,422 / 116 |

The baseline remains structurally PublicCoin-eligible. Each of the four D1
neighbor controls remains ineligible for its original directed reason. One
schema-valid byte-changing owner substitution per view confirms that schema
validity alone does not establish the owner-derived body.

## F2-O1 rerun

The package imports F2-O1's generator and checker source unchanged and first
reproduces its committed Lean and ledger fixtures. It then replaces only the
40 typed `operational-owner-view` gaps with active leaves from D3's typed
universe and reruns the unchanged checker against the independently projected
cold universe.

F2-O1's checker is specialized to one `PublicCoinView` path space. The tracked
`f2o1-six-view-ledger.json` therefore uses an explicit compatibility adapter:
virtual paths prefix the carrier and owner-view ordinal, while every coordinate
retains `carrier`, `owner_view`, and `owner_path`. The compatibility
`view: PublicCoinView` discriminator is not a claim that the other five bodies
are PublicCoin bodies.

| Gap class | Before | After | Result |
|---|---:|---:|---|
| `operational-owner-view` | 40 | 0 | closed |
| `operational-distribution` | 3 | 3 | `CannotAnswer` |
| `operational-denotation` | 6 | 6 | `CannotAnswer` |
| `module-effect-denotation` | 3 | 3 | `CannotAnswer` |
| `oracle-carrier-representation` | 3 | 3 | `CannotAnswer` |
| `operational-outcome-map` | 1 | 1 | `CannotAnswer` |
| `property-premise` | 5 | 5 | `CannotAnswer` |

The rerun moves from 32 sourced / 61 gaps to 72 sourced / 21 gaps. Sixteen
operational semantic/provider gaps and five property premises remain. They are
not converted into affirmative evidence merely because all six structural
views now exist.

## Result boundary

A pass establishes bounded canonical-body agreement, round-trip validity,
constructor inhabitation, six schema-valid substitution discriminators, the
four D1 controls, and the stated F2-O1 structural gap delta for five exact
carriers.

It does not establish target-profile publication, target owner authority,
arbitrary-Core projection correctness, generated-provider correspondence,
runtime execution or replay, semantic-module or Oracle denotation, Claim or
Reduction truth, a mechanized refinement theorem, protocol soundness,
Fiat--Shamir security, ROM/QROM applicability, live compiler/backend
correspondence, or production readiness.

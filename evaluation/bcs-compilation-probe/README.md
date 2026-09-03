# Oracle-proof compilation composition probe

This package asks one exact question: do the current checked owners compose,
for one exact two-round logical-oracle Core, into a concrete
commitment-opening target followed by canonical-framed Fiat--Shamir with every
premise of a chosen BCS-style soundness statement coordinated?

The frozen answer is
`CannotAnswer/BCS-C-COMPOSITION-INCOMPLETE`, with verdict `bends`. The
structural route is coherent, but the repository does not yet carry an
executable canonical-framed checker over the exact migrated target carrier,
and the chosen statement has five premise-coordinate gaps or placeholders.

## What the gate checks

The typed path and a separately structured raw-dictionary path agree on:

- one finite source with two `LogicalAccess` Oracles, two Fresh challenges,
  challenge-derived query indices, two answers consumed by one Check, an
  accepting Terminal closed over that Check, and an unconditional rejecting
  fallback Terminal;
- six source views: `PublicBindingView`, `StrategyDecisionView`,
  `PublicCoinView`, `EffectView`, `ClaimReductionView`, and `ExecutionView`;
- deterministic elaboration to two `PublicBinding` Oracles, public commitments
  before dependent challenges, opening responses and evidence after queries,
  claim-group and opening Checks, exact source/target maps, independent target
  re-admission, and six source/target view relations;
- rotation of the Core identity at the commitment step, distinct Fresh and
  Fiat--Shamir Protocol identities over one literal target Core, one
  target-bound transcript-construction identity, and commitment influence into
  acceptance without changing the Interaction profile; and
- the exact premise ledger for the candidate soundness statement.

The package also executes the retained indexed authoring layer at fold depth
two and query count two. That is a finite-repeat authoring control only; its
output is not used as compilation authority. Finally, the existing
canonical-framed executable checker passes its own exact oracle control and
issues transcript-declaration, required-influence, and challenge-transition
views. Passing the probe's independently admitted target to that checker
returns `Malformed`, because the checker accepts its older bounded carrier and
not the migrated target Core carrier.

Run from the repository root:

```sh
python3 -B evaluation/bcs-compilation-probe/run.py --check
```

## Frozen findings

| Finding | Outcome | Stable code |
|---|---|---|
| source Core admission and six views | `Affirmative` | `BCS-A-SOURCE-CORE-AND-VIEWS` |
| commitment-opening transition | `Affirmative` | `BCS-A-COMMITMENT-OPENING-TRANSITION` |
| canonical-framed check on the exact target | `CannotAnswer` | `BCS-C-CANONICAL-FRAMED-EXACT-TARGET` |
| identity and influence cone | `Affirmative` | `BCS-A-IDENTITY-AND-INFLUENCE-CONE` |
| soundness-premise coordinates | `CannotAnswer` | `BCS-C-SOUNDNESS-PREMISE-COORDINATES` |

The aggregate cannot be
`Affirmative/BCS-A-COMPILATION-IS-COMPOSITION`: the exact target does not pass
the existing executable same-Core checker, and not every premise has an exact
coordinate.

## Premise-coordinate boundary

The named-premise design provides coordinate forms for Fiat--Shamir sampler
adequacy and the oracle process, but this probe has no published exact family
to replace their `exact-family` placeholders. It provides no named kind or
owner coordinate for source round-restoration soundness or commitment binding.
It also provides no exact theorem source, applicability result, and typed
quantitative result for the Fiat--Shamir loss. The gate preserves all five as
blocking entries; it does not turn a coordinate schema into an admitted
premise.

## What a pass does and does not establish

A pass establishes reproducibility of the frozen finite result, agreement of
two package-local reconstruction paths, successful controls for the retained
indexed authoring and canonical-framed checker packages, and fail-closed
classification of the exact integration gaps.

It does not prove source soundness, state restoration, round-by-round
soundness, commitment security, any random-oracle property, Fiat--Shamir
security or loss, or a property of the compiled protocol. It does not mint PIR,
Analysis, Compiler, or deployment authority; implement the owner-page
construction; validate a backend; or establish correspondence to a paper,
library, or production system.

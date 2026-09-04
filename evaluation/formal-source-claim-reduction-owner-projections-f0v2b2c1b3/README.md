# F0-V2B2C1B3 claim/reduction owner projections

This package executes the five claim, reduction, publication-order, and
Challenge-sharing constructor-isolation families of B2C1B. It extends the
canonical-byte owner evaluator over those constructors and projects each
admitted Core and paired Fresh Protocol into the six candidate normalized B2B
owner views through the exact B2C1A codec.

Run from the repository root:

```sh
python3 -B evaluation/formal-source-claim-reduction-owner-projections-f0v2b2c1b3/run.py --check
```

The scoped result is
`Affirmative/F0V2B2C1B3-A-CLAIM-REDUCTION-OWNER-PROJECTIONS`: a typed owner
evaluator and a separately structured cold byte-derived projector agree on 30
distinct exact view bodies over five minimal carriers.

## Covered slice

The five carriers cover:

- one initial linear Claim created by an ancestor `Statement` binding and
  consumed at a Terminal;
- one linear input Claim consumed by a Reduction that creates one reusable
  output Claim with exact contract, ordinal, scope, and occurrence pairing;
- two guarded Prover publications on opposite sides of one required Challenge,
  including exact side-input publication closure and the K2 Last-Challenge
  mapping `Some(challenge)` before and `None` after;
- a dense two-member joint Challenge group with complete prior-member closure,
  compatible type/domain/law/scope, and an explicit causal dependency; and
- one Shared Challenge with two exact reduction-role consumers derived from
  the Reduction declarations, plus a reusable Claim cited by both.

The gate also checks one-to-one Challenge, Reduction, and Terminal occurrence
backlinks; exact module/declaration and guard-algorithm closure; Claim-output
bijection; occurrence, scope, availability, guard-implication, and ordering
laws; linear-use and bounded static terminal closure; explicit PCGraph edges
and Challenge class transfers; target sorted-unique order; complete body round
trips; deterministic reprojection; and same-evaluator Fresh pairing.

The cold path imports neither the typed B2C1B3 model nor its retained objects.
It authenticates complete profiled Core and Protocol bytes against exact
references, verifies the Fresh-to-Core dependency, parses plain records, and
uses separate Foundation, schema, graph, projection, and codec module
instances.

## Owner-derived facts

Claim creation coordinates and ordered Claim uses are derived from
`ClaimSource`, Reduction input lists, Terminal dispositions, and one-to-one
occurrence backlinks. Likewise, `ReductionConsumers(challenge)` is derived
from exact membership in Reduction `required_challenges`; it is not another
authored list.

This produces an SSA-like resource history—one Claim creation coordinate and
ordered uses—but introduces no semantic SSA object, transcript state, or MLIR
token. The authoritative objects remain the existing Core declarations and
occurrence schedule.

For each required publication, `next_challenge` must be the least later member
of that Reduction's exact required-Challenge sequence, or `None` exactly when
there is no later member. A Fiat--Shamir construction can therefore derive the
publication's required influence on that Challenge without guessing protocol
round roles from raw message order.

## Negative controls

The 61 frozen findings include 25 freshly authenticated semantic mutations.
They refuse invalid Claim sources and declaration kinds, missing/duplicate or
mismatched Reduction outputs, empty inputs, missing/duplicate backlinks,
cycles, publication closure/kind/order/Last-Challenge errors, guard weakening,
joint closure/compatibility errors, invalid Shared/Exclusive consumer counts,
linear double use, and incomplete or duplicate Terminal dispositions.

Four schema-valid but owner-wrong view substitutions alter Claim usage, Claim
creation, Last-Challenge, or Shared-consumer facts. Their bodies remain valid
instances of the candidate grammar but differ from the unique owner-derived
bodies. Cold controls reject truncation, body/reference substitution,
cross-Core Protocol substitution, and authority issued by the predecessor
evaluator.

## Boundary

The terminal analysis in this package is deliberately static and bounded: all
positive carriers have one unconditional final fallback, and the checker does
not establish path-sensitive Claim liveness or accepting-path Reduction
saturation. That work remains in B2C1B5 and B2D.

`ExecutionView` contains owner-derived resolver and runtime schemas only. It
does not execute a Reduction, create or consume a runtime Claim, sample a
Challenge, construct a completed run record, or replay one.

This result closes five more of the 21 B2C pressure families at bounded
research resolution. Four B2C families and both B2D integration families
remain. It does not publish a target profile, establish current compiler or
runtime correspondence, prove a projection/refinement theorem, establish a
cryptographic or Fiat--Shamir theorem in any model, or close F1 Q1.

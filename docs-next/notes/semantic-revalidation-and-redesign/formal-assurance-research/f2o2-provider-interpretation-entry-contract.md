# F2-O2: entry contract for the first provider interpretation

> **Kind:** entry contract (formal-assurance research, provider correspondence)
> **State:** Proposed 2026-09-03 for the lane that follows the Terminal-contract
> mechanization; it supersedes the operational-correspondence stage of the
> earlier architecture note (`f0-provisional-architecture-and-entry-contracts.md`,
> Section 8.1) by naming the inputs that now exist.
> **Authority:** None. A contract fixes what a lane must deliver and what a
> result may claim; it changes no owner page.

## 1. The question

Provider correspondence asks whether an artifact in an external formal system
means the same protocol as the formal source zkc publishes. The formal source
of an admitted Protocol is now exact: the Core and Protocol bodies with their
authenticated dependency closure, the six normalized owner views, the
coordinates of the nominal public-coin-law declarations, and the abstract
outcome partition (`docs-next/pir/interactive-core.md`, Section 13.2 on the
migration branch). What is not yet exact is the reading of that source into a
provider's types, and the check that the reading is faithful. This contract
fixes the first attempt at both, for the finite Schnorr subject, against
VCVio at the pinned revision.

## 2. Inputs that exist

| Input | Where | What it supplies |
|---|---|---|
| the migrated owner text | branch `docs/pir-migration-v2c` | the six view bodies, the Terminal contract, the outcome partition |
| six-view bodies for the integrated carriers | `evaluation/formal-source-integrated-views-f0v2b2d3/` | typed and cold derivations of every view a provider reads |
| the term calculus in Lean | `evaluation/formal-kernel-mechanization-m0/` (M2) | the Check and guard denotations, proved deterministic and equal to the closed form for Schnorr |
| relation and Plan candidates | `evaluation/formal-schnorr-relations-plan-f2p1/` | statement, witness, relation predicate, nonce state, honest commit and respond |
| provider observables | `evaluation/formal-provider-observables-f2o0/` and `-f2o1/` | the exact list of what a provider must be able to read and the sixteen remaining operational gaps |
| named premises | branch `docs/analysis-premise-intake` | the Fresh distribution premise, the provider outcome-carrier map, and the five relation and Plan premises with their coordinates |
| the provider | VCVio `de0a3108140e3e04a7ebf0075aa110b459ee6e8a`, Lean `v4.33.1` | `OracleComp`, the sigma-protocol structure, `Schnorr.sigma` and `Schnorr.sigma_complete` |

## 3. The provider artifact

One Lean module, generated from the formal source by an untrusted generator,
that defines the Schnorr Fresh Protocol as a VCVio interactive protocol:

- the statement and witness types from the relation candidate's semantic
  model (the finite additive group of three elements, `Y = x . G` with
  `G = 1`);
- the Prover's commit and respond steps from the Plan's two recipes, with the
  nonce as the Plan's persistent state;
- the challenge as one uniform draw over the challenge domain, which is what
  the Fresh distribution premise binds to the public-coin-law coordinate;
- the verifier from the Check's term, whose denotation M2 has proved equal to
  `z = a + c . y` in the field of three elements;
- the terminal verdict mapped into the provider carrier by the provider
  outcome-carrier premise, which for VCVio's sigma protocol is the Boolean
  the verifier returns.

The generator may be any program. Nothing it emits is trusted.

## 4. The correspondence relation

The lane defines one typed relation between the formal source and the provider
artifact and checks it independently of the generator:

1. **Schedule.** Every occurrence of the `EffectView` schedule maps to exactly
   one provider step, in occurrence order; every provider step is the image
   of an occurrence. The Prover decisions of the `StrategyDecisionView` map
   to the prover's moves and nothing else.
2. **Values.** Every message and challenge type maps to the provider type at
   that step; the challenge site is the `PublicCoinView` challenge and its
   domain is the provider's sampling type.
3. **Checks and guards.** The verifier's computation is the M2 denotation of
   the Check term applied to the provider's values; equality is checked on
   every input of the finite domain, not asserted.
4. **Terminals.** The first-active terminal of the formal source and the
   provider's accept or reject agree on every run of the finite domain, and
   every lane of the outcome partition that the Schnorr Protocol can reach
   (`Accepted`, `Rejected`, and `OperationalNoncompletion`) has an image
   under the carrier premise; a lane with no image is `CannotAnswer`.
5. **Traces.** For every run of the finite domain, the `ExecutionView`'s
   completed record and the provider's transcript agree step by step under
   the maps above.

The relation is total on both sides or the result is negative. It preserves
occurrence identity and order; it does not identify two occurrences the
formal source distinguishes.

## 5. Generator and checker

- The generator reads the six views, the algorithm preimages, and the
  candidates, and emits the Lean module plus a certificate: the occurrence to
  step map, the type map, and the lane map.
- The checker is a separate program with no shared code beyond the published
  bodies: it re-derives the views from the admitted Core, checks the
  certificate for totality and order, evaluates the Check term through M2's
  evaluator on every input, runs the provider artifact through Lean on the
  same inputs, and compares. Lean is the provider's own checker; the
  correspondence checker treats Lean's output as data.
- Both are frozen in one package with findings for every clause of Section 4.

## 6. Residual trust

The result carries, named, everything it cannot discharge: Lean's kernel and
VCVio's semantics of `OracleComp`; the equality of M2's evaluator with the
Python evaluator, which is differential evidence on the finite domain; the
Fresh distribution premise and the outcome-carrier premise, which are
premises and not facts; and the adapter code of the checker itself, which is
small and inspected but not proved.

## 7. Acceptance

`Affirmative` only when every clause of Section 4 holds on the whole finite
domain and every reachable outcome lane has an image; `CannotAnswer` with the
exact clause otherwise. The claim-binding reopening
(`../schnorr-claim-binding-reopening-2026-09-03.md`) does not block this
contract: correspondence needs no claim, and the relation premises are
consumed later by applicability. A passing result establishes operational
correspondence for one subject and one provider. It establishes no property,
no theorem applicability, and no correspondence for any other subject.

## 8. Order

After the Terminal-contract mechanization, because the terminal clause of
Section 4 reads that contract; before the first applicability attempt,
because applicability binds the theorem to this correspondence.

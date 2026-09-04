# F2-P1 exact Schnorr relation and Plan candidates

This package asks one exact question at cutoff
`1464c8be0fac7d3dd63909f41e7d5051ddd91f98`:

> Do exact finite-additive Schnorr relation, semantic-model, public-instance,
> Protocol-binding, ProverPlan, PlanRealizes, witness-surface, and
> witness-binding candidates form for the admitted F1-R1B Fresh Protocol, and
> can the requested initial-claim meaning also form without changing that
> Protocol?

The frozen answer is
`CannotAnswer/F2P1-C-SCHNORR-CANDIDATE-BINDING-INCOMPLETE`.

The relation and Plan candidates admit under the bounded package check, bind to
the exact F1-R1B Protocol, and reconstruct identically by two independently
structured paths. All five F2-O0 premises now have named candidate coordinates.
One requested edge cannot form: F1-R1B declares `claims=()`, while Relations
Section 7.3 requires an actual K2 `ClaimRef`, specifically
`InitialClaim(BindingRef)`, before an initial `ClaimMeaningBinding` can exist.
Inventing that claim would change the admitted Protocol body and identity.

Run the offline, standard-library-only gate from the repository root:

```sh
python3 -B evaluation/formal-schnorr-relations-plan-f2p1/run.py --check
```

The frozen report has 39 findings: 28 `Affirmative`, five `Refused`, one
`Negative`, and five `CannotAnswer` outcomes.

The source ledger is re-pinned to the current Interface/Plan bytes. The
inserted owner-compiler definitions move the Plan anchors without changing the
candidate bodies, their package-local identities, or any frozen finding.

## Exact additive fixture algebra

The F1-R1B fixture does not encode a multiplicative group. It has one three-
element carrier `Z3`, addition and multiplication modulo three, and checks

```text
z = A + cY mod 3.
```

This package reads the same `Z3` carrier in two roles:

- scalar carrier: `Z/3Z`;
- additive-group carrier: `(Z/3Z,+)`;
- generator: `G = 1`;
- scalar action: `s . g` is repeated addition, represented by `s*g mod 3` in
  this finite fixture; and
- intended relation: `Y = x . G`, which reduces to `Y = x mod 3` because
  `G=1` and the fixture identifies the scalar and group-element carriers.

The dot denotes an additive scalar action. It does not smuggle in a
multiplicative group, exponentiation, or a production discrete-log
instantiation.

## Exact Relations candidates

The package authors package-local candidate bodies for:

```text
RelationDefinition:
  payload = finite additive Z/3Z algebra and Y = x . G

RelationInterface:
  PublicInstance[0]  = Y : Z3
  PrivateWitness[0]  = x : Z3
  OracleStatements   = []
  PhaseInputs[0]     = c : Z3
  PhaseInputs[1]     = z : Z3

RelationSemanticModel:
  evaluator(Y,c,z,x) = (Y = x . G)
  assumptions = []

RelationInstance family:
  every (Y,c,z) in Z3^3, with representative (Y,c,z) = (1,2,1)
```

The evaluator consumes the Interface vectors in their exact role order; `c`
and `z` are transcript phase inputs but do not change truth of the witness
relation. Exhaustive comparison covers all 81 tuples `(Y,x,c,z)` and finds no
definition/model disagreement. The package also constructs all 27 typed
`(Y,c,z)` instance bodies.

Each body receives a deterministic `candidatev0:*:sha256` label so the two
paths can compare every identity. These are package-local test identities,
not canonical owner-issued `zkcidv0` identities and not publication.

## Exact Protocol binding candidate

The candidate `ProtocolRelationBinding` names the frozen F1-R1B Fresh Protocol
and has:

| Relation coordinate | Protocol coordinate | Meaning |
|---|---|---|
| `PublicInstance[0]` | Statement public binding 0 | `Y` |
| `PhaseInput[0]` | `ChallengeValue(ChallengeRef(0))`, emitted at occurrence 1 | `c` |
| `PhaseInput[1]` | public output 0 of Prover-message occurrence 2 | `z` |

Oracle edges, reduction meanings, commitment groundings, and claim meanings
are exact empty sequences. The empty claim-meaning sequence is the only exact
binding for the admitted claim-free Protocol. An attempted initial claim
meaning returns `CannotAnswer/F2P1-C-INITIAL-CLAIM-ABSENT`; it is not silently
rewritten as either a positive or negative claim.

## Exact Plan and witness candidates

The `ProverPlan` is a strategy for the same Protocol:

- private material `x : Z3`, role `WitnessIngress`;
- private randomness `r : Z3`, first available at decision 0;
- persistent state slot 0, initialized to zero and replaced with `r` after
  decision 0;
- decision 0 recipe: `A := r`, emit `A`, store `r`;
- decision 2 recipe: read state `r`, prior challenge occurrence 1, and private
  material `x`; compute and emit `z := r + c*x mod 3`; and
- no derived witness exports or accepted-terminal recipes.

The candidate `PlanRealizes` result covers every and only Prover decisions 0
and 2, checks recipe ABIs and move shapes, permits only the prior challenge
read, and checks one-shot nonce use plus total state updates.

`PlanWitnessSurface` exposes only key `x`, type `Z3`, role `WitnessIngress`,
class `SuppliedForGeneration`. Nonce randomness and persistent state are absent
from that surface. `PlanWitnessBinding` maps
`RelationInterface.PrivateWitness[0]` to the whole `x` surface entry and checks
exact type equality.

## F2-O0 premise coordinates

| F2-O0 premise | Exact candidate coordinate | Named operand |
|---|---|---|
| relation predicate | `RelationSemanticModel(...).evaluator` | finite additive `Y = x . G` evaluator |
| witness type | `RelationInterface(...).private_witness[0].value_type` plus `PlanWitnessBinding.witness_edges[0]` | `x : Z3` at witness-ingress key `x` |
| Prover private state | `ProverPlan(...).persistent_state[0]` into `PlanExecutionState[0]` | nonce `r : Z3` |
| honest commit | decision-0 recipe node 0 into `PlanStrategyStep(0)` | `A := r` algorithm |
| honest respond | decision-2 recipe node 0 into `PlanStrategyStep(2)` | `z := r + c*x mod 3` algorithm |

These are candidate coordinates, not VCVio provider operands or proofs that the
recipes are honest in a theorem-bearing sense.

## Two independent paths

[`model.py`](model.py) follows a forward typed-construction path. It admits the
F1-R1B Core and Fresh Protocol through the F1 reference checker, constructs
typed candidate records, validates the bindings and Plan dataflow, and
executes the finite evidence matrix.

[`independent.py`](independent.py) follows a reverse cold-dictionary path. It
uses the independently structured F1 owner-view implementation, authors the
bodies as ordinary dictionaries in a different order, validates them without
calling the typed candidate checker, and independently executes the matrix and
mutations. The two files do not import one another.

[`run.py`](run.py) requires equality of all candidate bodies, all 15 candidate
identities, the five-premise table, blocker, measurements, and mutation
outcomes. Their common agreement digest is frozen in
[`expected-findings.json`](expected-findings.json).

## Honest-run and mutation evidence

There are three valid statement/witness pairs, `(Y,x) = (0,0), (1,1), (2,2)`.
For every valid pair, every nonce, and every challenge, the bound Plan produces
`A=r` and `z=r+c*x`; all 27 runs satisfy the exact F1 verifier equation. Adding
one modulo three to each response makes all 27 controls reject.

Five directed mutations establish these bounded distinctions:

| Mutation | Outcome | Stable code |
|---|---|---|
| Statement edge targets nonexistent binding 1 | `Refused` | `F2P1-R-STATEMENT-EDGE` |
| challenge and response phase targets are swapped | `Refused` as the exact candidate | `F2P1-R-PHASE-ROLE-SWAP` |
| relation witness type is Boolean while Plan surface remains `Z3` | `Refused` | `F2P1-R-WITNESS-TYPE` |
| decision 2 reads its own not-yet-guaranteed response | `Negative` under `PlanRealizes` | `F2P1-N-PLAN-READ` |
| binding names another Protocol identity | `Refused` | `F2P1-R-WRONG-PROTOCOL` |

The swapped-role mutation is deliberately structurally type-correct: generic
binding shape alone cannot label two equal-typed phase roles. Exact candidate
body and identity comparison is what rejects it.

## What a pass establishes

A pass establishes only that, at the frozen source hashes and for this finite
fixture:

- the exact candidate bodies are well-formed under the bounded executable
  rendition of the cited owner contracts;
- the candidate relation, Plan, Protocol binding, Plan witness binding, and
  five premise coordinates reconstruct identically along two paths;
- the finite definition/model comparison, 27 honest executions, 27 controls,
  and five mutations have the frozen outcomes; and
- an initial claim meaning cannot be attached to the exact admitted F1-R1B
  Protocol because it owns no claim coordinate.

## What a pass does not establish

This package has candidate status only. It does not publish or modify any
Relations, PIR, Foundation, Analysis, or target-owner semantics. It does not
establish `Schnorr.sigma_complete` applicability, completeness, knowledge,
soundness, Fiat--Shamir security, discrete-log hardness, any cryptographic
property, provider-field correspondence, backend correctness, or production
validity. Finite exhaustive evidence over `Z/3Z` is not a theorem and the local
candidate IDs are not owner authority.

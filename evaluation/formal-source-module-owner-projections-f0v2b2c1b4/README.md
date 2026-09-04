# F0-V2B2C1B4 module owner projections

This package executes the three semantic-module constructor-isolation families
of B2C1B. It extends canonical-byte Core admission and Fresh Protocol pairing
over exact `ModuleEffectRef` declarations, then projects each admitted subject
into the six candidate normalized B2B owner views through the B2C1A codec.

Run from the repository root:

```sh
python3 -B evaluation/formal-source-module-owner-projections-f0v2b2c1b4/run.py --check
```

The scoped result is
`Affirmative/F0V2B2C1B4-A-MODULE-OWNER-PROJECTIONS`: a typed owner evaluator
and a separately structured cold byte-and-source projector agree on 18
distinct exact view bodies over three minimal carriers.

## Covered slice

One exact fixture semantic module publishes three `pir.core-effect`
declarations:

- `module-no-decision` has no prover move and reconstructs one deterministic
  public output through an exact total algorithm and evaluation contract;
- `module-prover-decision` has a typed prover move and a prover-only internal
  output; two occurrences exercise both `ObservedModuleValue` and
  `PriorOwnMove` guaranteed reads; and
- `module-prover-publication` has a typed prover move, one unique public
  publication output, and an exact influence-output coordinate.

The module declaration—not an ambient callback or an asserted Core flag—fixes
the payload ABI, decision class, move type, output visibility and transfer,
ordered value and control dependencies, reconstruction references, influence
output, guard behavior, replay rule, terminal interaction, and deterministic
work bound. The evaluator separately advertises support for this exact module
body and declaration set.

The gate checks canonical Core and Fresh identities, same-evaluator bearer
pairing, exact used-module and dependency closure, module/declaration owner and
coordinate equality, payload availability and typing, reconstruction closure,
terminal fallback, all six view bodies, target sorted-unique order, round
trips, deterministic reprojection, and explicit module PCGraph edges and
transfers.

## Why module preimages are part of the source contract

The Core body contains content-addressed module references, not their local
declaration bodies. A reference binds a supplied body, but it does not make
that body available to a clean-room projector. Decision class, output
visibility, reconstruction, graph transfer, and FS structural eligibility
therefore cannot be recovered from Core bytes alone.

The cold path takes:

```text
complete profiled Core bytes + exact Core reference
complete profiled Fresh Protocol bytes + exact Protocol reference
exact sorted used-module (reference, body) closure
```

It authenticates every source, requires the module-source keys to equal
`used_modules`, parses the module catalogs into plain records, and derives all
six views without importing the typed B2C1B4 model or trusting retained owner
objects. This makes missing module availability fail as a dependency error
instead of inviting a guessed or caller-asserted classification.

The eventual source/read package should carry this same content-addressed
dependency closure. This does not require a `ModuleKernel`: semantic modules
already own their declaration meaning, the Core owns occurrence coordinates,
and the owner evaluator's support fingerprint owns which exact declarations
it implements.

## Admission and Fiat--Shamir eligibility are different judgments

All three positive Cores are admitted, but their structural public-coin
eligibility results differ:

| Family | Module-output transfer | PCGraph | Structurally FS-eligible |
|---|---|---:|---:|
| `module-no-decision` | deterministic | 11 nodes / 15 edges | yes |
| `module-prover-decision` | prover-private | 16 nodes / 25 edges | no |
| `module-prover-publication` | public publication | 11 nodes / 15 edges | yes |

The private decision module is refused only at the separate eligibility
question because its prover-private module output reaches acceptance-relevant
module sinks. The publication output instead applies the explicit publication
transfer and becomes a public observation. Neither result is inferred from
the declaration name or raw occurrence order.

This preserves four non-interchangeable judgments:

```text
Core admission
  != Fresh Protocol pairing
  != same-Core structural FS eligibility
  != a Fiat--Shamir security theorem
```

The result introduces no transcript state, semantic SSA token, or MLIR token.
Occurrence outputs and module decisions retain stable coordinates; the
Strategy view derives guaranteed observed-module and prior-own-move reads from
those existing owners.

## Graph and reconstruction consequences

`ModuleControl` and `ModuleOutput` are explicit PCGraph nodes. Declaration
dependencies produce edges from activity, effect, payload-value producers,
and prior same-occurrence module outputs. A module output then connects to its
ordinary occurrence-output coordinate. Graph adjacency records causality;
the declaration's deterministic, publication, or private transfer separately
determines its class.

For a deterministic public output, the typed path authenticates the exact
algorithm, its module closure, its exact total ABI, and the evaluation
contract. The cold path independently reconstructs and pins those expected
references while authenticating the module body that names them. This package
does not generalize that fixture into a universal reconstruction language.

## Negative controls

The 69 frozen findings include 28 freshly authenticated semantic mutations.
They cover payload arity, availability, and ABI; module owner, declaration
kind and coordinate; omitted, extra, missing, or mismatched module closure;
missing, extra, or mismatched reconstruction authority; terminal placement
and backlink; unadvertised declaration bodies; duplicate, missing, or invalid
dependency edges; lifecycle bounds; output visibility; and publication
influence.

Six additional values remain valid instances of the candidate view schemas
while omitting or substituting an owner-derived supported-extension atom,
module move type, graph edge, graph class, observed-module read, or prior-own-
move read. Their valid grammar does not grant owner equality.

Cold controls reject absent, altered, and truncated module sources; truncated
Core bytes; Core body/reference substitution; and a cross-Core Fresh Protocol.
A genuine B2C1B3 authority bearer cannot authorize projection under the
B2C1B4 evaluator fingerprint.

## Boundary

This result closes three more of the 21 B2C pressure families at bounded
research resolution. B2C1B1--B2C1B4 now cover 20; the expanded-terminal family
remains B2C1B5, followed by both B2D integrated graph/runtime families.

The package does not execute a semantic module, reconstruct a concrete output,
validate a completed module event history, define a general module language,
publish or migrate a target profile, establish current compiler/runtime
correspondence, prove a projection/refinement theorem, establish a
cryptographic or Fiat--Shamir theorem in any model, or close F1 Q1.

# K3-D bounded OIR-projection instrument

This directory is an executable falsification instrument for the selected
K3-D contract. It asks whether a supported PIR endpoint view and an
independently constructed, locally admitted OIR endpoint have exactly the same
canonical static semantics.

It is not normative specification, production lowering, a final OIR syntax,
an execution model, an MLIR dialect, or a cryptographic proof. The positive
fixtures exercise one bounded profile:

- a Fiat--Shamir verifier endpoint; and
- a Fiat--Shamir prover endpoint specialized by an exact checked Plan.

Both use base, non-Oracle, non-module effects. The package imports K3-B from
`../k3-dependent-surfaces/reference_model.py` under its canonical module name;
K1 and K2 are reached only through K3-B. K3-C is never imported.

## Authoritative executable gates

The model keeps three independently implemented lanes. Before either graph
lane starts, `check_projection_owner_adapter` joins purpose-bound live owner
authority:

- K2 owner-issued static views for public binding, public coin, effects,
  claims/reductions, transcript declaration, required influence, and
  challenge transition, plus StrategyDecision for the Prover;
- the checked K2 FS construction and its owner-issued FS view;
- the K3-B owner-issued Interface correspondence view; and
- for the Prover, an affirmative `CheckedPlanRealizes` result.

Each issued K2/K3-B capability names the same typed K3-D consumer and the
source- and role-specific projection purpose. The adapter revalidates every
live issuance and checks every overlap against the candidate future-owner
facts before it can mint a process-local, noncopyable adapter.

The current K2/K3-B carriers do not yet issue every rich fact needed by the
endpoint graph. `future_owner_supplement` therefore builds an inert candidate
for only that residual surface. `issue_future_owner_supplement` validates its
closed shape and root-level overlap, assigns a source-profiled supplement ID,
and forms an exact K1 `PortableSourceAuthorityBinding` with no hidden operation
policy. That first bearer is provisional and inert. Only
`check_projection_owner_adapter`, after validating the complete live K2/K3-B
overlap and checked Plan, activates the identical supplement bearer and mints
the adapter. Duplicate or extra closed-table keys and claim re-anchoring are
refused before activation. Raw candidates, provisional bearers, and copied or
reconstructed authorities are not consumable. Missing authority is
`MissingDependency`; a stale or disagreeing authority is `Refused`.

This authenticates the selected bounded supplement law, not universal future
K2/K3-B coverage. Supplement-only facts are claim/reduction contract detail,
terminal detail, rich FS evaluators and challenge laws, structural codec and
fibre detail, public-derivation transports and completions, and rich Plan
recipe/evaluation/export detail. As owners expose those families, they must
move behind owner-issued views and leave the supplement rather than create a
second source of truth.

After that authority join, the model keeps three independently implemented
lanes:

1. `classify_support` mints one exact live `SupportedExtractionBasis`, and
   source extraction uses that basis to derive an `EndpointSemanticGraph`;
2. `project_supported_endpoint` consumes the identical basis and adapter,
   walks the owner surfaces through an independent implementation, and emits
   an unauthoritative OIR candidate, which `local_admit` validates without a
   PIR source-view object; and
3. `check_projection` compares the checked source graph and admitted OIR graph
   by exact canonical equality.

`project(request)` is only a convenience wrapper around classification and
`project_supported_endpoint`. The explicit basis-taking entry point lets the
joined K3-E witness show that both independent graph constructors consumed the
same live authority chain without adding a PIR source ID or source view to OIR
identity.

Every authority boundary in that chain is an identical, process-local,
noncopyable bearer. `CheckedEndpointSourceView` retains its exact live
`SupportedExtractionBasis` and owner adapter; the validation request retains
that same chain plus the exact locally admitted OIR and formed proposition;
and the final `CheckedProjection` retains the exact live validation request.
The instrument's profiled subject and probe-local validation identifiers are
recomputed at every consumer boundary, so a structurally equal
`dataclasses.replace` reconstruction is not authority. This says nothing about
durable MetaValue preimage parity.

Projection does not permit event fusion, splitting, reordering, optimization,
or existential witness maps in this v0 profile. A negative result is the exact
nonempty set of differing top-level graph-field tags. Local OIR validity and
source-relative projection correctness remain separate: a locally valid OIR
can still be projection-negative.

The graph has exactly eleven identity-bearing fields:

1. endpoint role;
2. exact used dependencies;
3. value types;
4. constants;
5. pure nodes;
6. role ABI;
7. the complete endpoint spine;
8. static Fiat--Shamir semantics;
9. claims;
10. anchored reduction and terminal obligations; and
11. the optional reachable Plan graph.

Owner/source labels, provenance, runtime receipts, dead Plan declarations,
Plan exports, and authored route order do not enter `OirId`. Reachable Plan
algorithms, typed private material, randomness availability, state
initialization and updates, and decision-keyed recipes do.

## Derived static endpoint contract

`derive_endpoint_contract` applies `EndpointContractLawV0` to an admitted
graph. `DerivedEndpointContract` has only:

- `static_obligations`: slot ingress, Plan decisions, exact K2 framing,
  locally owned occurrences, challenge interpretation, and presentation;
- `requirements`: exact local evaluator, counterparty action/transport,
  Plan resource, public reconstruction, and codec-use requirements; and
- `completion_interface`: verifier terminal/Fiat--Shamir-failure completion
  variants, or no source-semantic completion for the prover.

Completion tags are distinct from completion payload coordinates and consume
no codec. Counterparty action requirements are derived even when a public
value can be reconstructed locally. A prover has no invented accept verdict or
generation-completion event.

`derive_endpoint_value_access` is a transient, graph-only least fixed point.
It proves that each locally demanded endpoint value has one route through an
invocation decode, constant, pure evaluation, Plan move, local occurrence,
challenge interpretation, inbound transport, or eligible public Check
reconstruction. It is neither an OIR identity field nor part of the derived
contract. The supported prover profile rejects retained verifier-private
inputs; invocation exposure is public-only.

Construction-owned Fiat--Shamir framing is separate from Interface transport
codecs and external names. The static graph preserves every original K2
framing coordinate, the per-challenge namespace recipe, ordered challenge
conditions, and one construction-global sampling-exhaustion failure. Dynamic
draw instances are intentionally outside K3-D.

## Fixed support frontier

Support classification is fail-closed and returns the complete sorted
nonempty set of applicable reasons. The following are typed `Unsupported`
before any projection proposition is formed:

- Fresh interpretation;
- a generic prover without an exact Plan;
- Oracle occurrences;
- any admitted Core module effect.

These are exactly the four durable support-reason variants. Two earlier
boundaries are deliberately outside that classifier: a future Plan module
recipe is an owner-profile `KindMismatch`, while the current executable K2/K3-B
P01 carrier is `MissingDependency` because it does not inhabit the richer
future-owner fixture schema. The latter is an implementation/evaluation-
carrier limitation, not a claim that the target K3-B design lacks codec DAGs,
slots, fibres, Statement flow, transports, completions, or typed Plan recipes.
Positive P01 cases therefore use an explicit owner-admitted future supplement
and never synthesize missing carrier facts silently. `live_p01_request`
deliberately omits that authority and remains `MissingDependency`.

General codecs require a separate certificate at local admission. That
certificate does not enter OIR identity. The fixed owner-schema set and
purpose-specific read-manifest bodies are exposed and checked against 190
selected Python carrier paths; unknown fields fail closed.

## Deliberate non-claims and residual surrogates

The instrument does not model runtime decoder results, draw ordinals, state
versions, dynamic ports or traces, completion aggregation, concrete execution
outcomes, wire packaging, liveness, or acceptance. Those are Stage 4B work.

`pressure_probe_p01_endpoint_pair` is only a non-authoritative, observation-
only P01 duality pressure probe over two independently admitted endpoints. It
returns an ordinary mismatch tuple and mints no semantic `Negative`, pair
proposition, profile, validation request, or capability. An
authoritative source-independent endpoint-pair relation is deferred because it
needs its own exact normalization and duality language.

Canonical IDs use deterministic JSON structural bytes as a probe-local
surrogate. The 190-path reflection is a bounded Python-carrier check. Neither
claims byte parity with K1 `MetaValueV0` nor implements a recursive durable
five-root owner grammar. In particular, the checker-basis and validation-
request identifiers are bounded validation identities only: the durable target
has not selected typed portable domain bodies for them. They do not establish
durable semantic identity, authority, or exact preimage parity.

Qualified answers keep `Affirmative`, `Negative`, `Unsupported`,
`MissingDependency`, `KindMismatch`, `Malformed`, `Refused`,
`DeterministicLimitExceeded`, and `CheckerFailure` distinct. Unsupported or
unanswerable attempts never return a partial OIR target. `Negative` is emitted
only by exact comparison of a formed projection proposition. Owner-profile
inadequacy is `Refused`, while a contradiction in an already admitted
extractor or target builder is `CheckerFailure`. The convenience
`ProjectionPipelineRun` uses absent optional stage results for stages not
attempted after an earlier nonaffirmative answer; it does not fabricate
downstream refusals.

## Run

```bash
python3 -B evaluation/k3-oir-projection/run.py --check
```

The suite freezes both P01 role graphs and their static contracts, exercises
source and target derivation independently, and mutates graph structure, K2
coordinates, guards, messages, checks, conditions, static FS laws, claims,
reductions, terminal/completion closure, codecs, Plan resources and recipes,
support reasons, identity quotients, public reconstruction, and the explicit
non-authoritative pair pressure probe.

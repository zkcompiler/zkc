# Accumulation, Folding, and Recursion Architecture Selection

> **Kind:** Temporary cross-case synthesis
> **State:** Semantic target selected and durably absorbed; complete owner-
> profile publication, holdout validation, and independent identity/profile
> freeze remain separate gates
> **Authority:** None. Durable specifications own every promoted law; this page
> preserves the selection reasoning and exact achieved depths.

## 1. Result

The package does not justify an `Accumulator`, `FoldingScheme`,
`RecursiveProof`, or runtime child-Protocol root. The existing separation is
fundamentally sound:

```text
one verifier-observable interaction
  -> one flat finite InteractiveCore

challenge source and transcript interpretation
  -> Protocol

honest private construction
  -> ProverPlan

claims, relation instances, transforms, and witness evolution
  -> Relations

proof and result presentation
  -> Interface and OIR

security, induction, setup, and theorem transport
  -> Analysis, supported by Evidence
```

One narrow addition to `ProverPlan` is selected: accepted-terminal recipes for
bounded private derivation after an exact `Accept` terminal when the source
has no later prover publication. Basic Nova, HyperNova, and CycleFold's
companion fold independently force that same lifecycle law.

Typed public Plan parameters are **deferred**, not selected. Every frozen case
can already place a verifier-relevant public parameter in Core or specialize a
Plan with an admitted constant. A reusable parametric Plan may still be a good
authoring and deployment design, but convenience and identity-rotation
economy do not meet this package's promotion rule. That question needs a
separate contract whose objective explicitly includes reusable Plans.

## 2. Case results

| Case | Result | Decisive observation |
|---|---|---|
| Nova committed relaxed-R1CS fold | `ConservativeExtension`, T2 | the folded private witness depends on the final coin, after the last source prover message |
| corrected two-cycle Nova | `Native`, T1 | its fold/construct/fold/construct schedule provides later genuine decisions that can retain each folded witness; a unique full target elaboration remains open |
| HyperNova multi-fold | `ConservativeExtension`, T1 | the folded LCCCS witness is derived after the last challenge without a later publication; the recorded finite member is not yet a strict-T2 encoding |
| CycleFold | `ConservativeExtension`, T1 | the primary witness is available before later prover publications; only the companion witness depends on final `rho_star`; a unique full target elaboration remains open |
| ProtoStar public accumulation | `Native`, T1 | the updated public accumulator is genuinely published after `alpha`, so that decision can also export its private accumulator; exact hiding-opening details remain open |
| LatticeFold+ three-to-two fold | `Native`, T1 | the final decomposition is a genuine prover decision and already owns both private output witnesses; exact batching expansion remains open |
| BCTV recursive composition, checked against Fractal | `ProfileOrModule`, T1 | verifier-in-circuit recursion has a stable owner split, but exact circuit, setup, codec, Fresh-OIR, and resource profiles remain missing |

The native cases are important negative controls. The selected terminal
facility is not “work after any challenge.” It is used only when no real
decision point exists after the value's last public dependency.

## 3. Distinctions preserved

The following notions remain separate:

- **folding:** a relation transform that preserves a later obligation;
- **accumulation:** evolution of an accumulator relation and its private
  witness, without necessarily deciding all source claims immediately;
- **decision:** a separate verifier that discharges an accumulated relation;
- **IVC/NIVC:** an Analysis-level family over an ordered sequence of finite
  steps and exact recurrence edges;
- **recursive proof construction:** construction of a new proof whose private
  relation witness includes an earlier proof value; and
- **direct imported verification:** a verifier-observable check of another
  proof, represented as an exact Core `Check` when it is a pure Boolean
  operation and as a module effect only for richer observable behavior.

Shared implementation techniques do not collapse their semantic identities.
In particular, an accumulated claim is not already a proof, a recursive proof
value is not a recursive semantic ID, and a decider is not an accumulator
method.

## 4. Selected Plan lifecycle

### 4.1 Accepted-terminal recipes

`AcceptedTerminalRecipe` is attached to one exact `Accept` terminal. It may
read only constructor-wise guaranteed public coordinates, earlier own moves,
the final post-decision state snapshot, private ingress, constants, and its
own earlier local nodes. It has:

- no Prover move;
- no Core effect or verdict authority;
- no transcript mutation;
- no module-effect invocation;
- no post-terminal state update; and
- at least one atomic private witness export.

Every node must be reachable from a terminal export. Runtime finalization
evaluates exactly that export-rooted closure. Failure after Core acceptance
does not rewrite the accepted run and releases no partial export.

Decision-site exports and terminal-site exports share one continuation
contract but retain distinct source sites. For each accepting terminal, the
contract has one explicit arm containing exactly the decision exports
guaranteed on every path to that terminal plus the terminal exports owned by
that terminal. Inactive arms have no runtime value. The reached arm is issued
atomically, so a consumer never receives a misleading prefix assembled from
different paths.

The selected model closes cross-run evolution through two distinct causal
lanes and one final join:

```text
accepted terminal export in run i
  -- confidential causal Plan view + checked Relations edge -->
grounded private output occurrence in run i

grounded private output occurrence in run i
  -- IssueAcceptedPlanWitnessIngressSupply (one use) -->
fresh WitnessIngress occurrence in run i+1

affirmative public EquationGrounding(
  ExactCausallyGenerated output slot in run i,
  ExactCausallyGenerated input slot in run i+1,
  exact source/target runs and RelationInstances)

JoinCausalPlanWitnessHandoff(private source grounding,
                             private target grounding,
                             CausalPlanWitnessHandoffCapability)
  --> CheckedPlanWitnessHandoffCorrespondence + live capability

JoinCausalPlanStepRecurrence(public EquationGrounding,
                             CheckedPlanWitnessHandoffCorrespondence)
  --> CheckedCausalPlanStepRecurrence + live capability
```

The Plan-owned issue operation consumes the exact unspent accepted-continuation
output and the exact unfilled target ingress, then produces
`ReadyPlanWitnessIngressSupply` and its noncopyable
`ReadyPlanWitnessIngressSupplyCapability`. The retained
`CausalPlanWitnessHandoffCapability` is the sole authority for the private
cross-run join. All issue results, joins, and capabilities are nonidentified,
process-local runtime objects. Equal values do not equate occurrences, and a
public equation cannot substitute for the private handoff authority.

The public equation and private handoff are deliberately separate. The former
grounds the public accumulator-instance recurrence. The latter proves that the
one accepted private export supplied one exact later ingress. Their final join
requires the exact same source and target runs and relation instances. It does
not establish fold preservation, relation satisfaction, or IVC induction.
Serialized or persisted transport is also outside this claim: Realization may
record codec, storage, and delivery provenance, but such a receipt does not
mint or reconstruct the live one-use Plan capability.

### 4.2 Plan-owned strategy and causal authority

The generic Protocol executor remains unchanged. A Plan-owned generation
adapter implements the exact `StrategyStep` interface from admitted decision
recipes. At each active decision it resolves the exact view reads, consumes
only declared private/random inputs, evaluates the local DAG, constructs the
move, commits the total state transition, and retains decision-local exports
atomically. On completed generation it seals the total state after the last
active decision; terminal `StateBefore` reads exactly that immutable snapshot.

The wrapper retains the exact prepared Plan session, adapter occurrence,
returned record, retained private values, and Core causal-generation
capability in one live nonserializable authority. Continuation completion
consumes that exact join. Protocol replay never mints Plan-generation,
continuation, or private-output authority.

This preserves the Core/Protocol identity boundary while preventing a public
`RunRecord` from being treated as proof of which private Plan state generated
it.

## 5. Relations consequences

`PlanWitnessSurface` gains the occurrence class
`ProducedWhenAcceptedTerminalReached`. Static extraction still exposes only
role, type, and occurrence class; it does not disclose the private value or
insert a Plan ID into Relations.

A separate purpose-bound confidential Plan-witness view supplies exact private
occurrences from one causally generated Plan run. A new
`PlanWitnessRunGrounding` arm of the existing `CorrespondenceQuestion` checks
selected `PlanWitnessBinding` edges against an exact private relation
assignment and reuses `CheckedCorrespondence`. A separate nonidentified live
join can require that an affirmative public run-grounding result and an
affirmative private grounding result retain the identical relation instance,
Protocol, invocation object, completed-record object, and Protocol causal-generation
capability. This keeps the two propositions distinct while preventing a public
occurrence from one run from being paired with private state from another. It
adds no new Relations semantic-subject kind.

The separation is necessary because:

- a static witness surface proves shape, not possession;
- a public run record omits private state and private outputs;
- the same public run may arise from different private sessions; and
- relation satisfaction is still a separate judgment after occurrence
  correspondence succeeds.

## 6. Endpoint and OIR consequences

The ordinary Plan-specialized prover endpoint continues to cover public proof
messages and decision-state behavior only. A distinct
`PlanContinuationProverEndpoint` purpose includes the site-qualified private
outputs required to continue from an accepted run.

The private continuation is not external Protocol completion. Both prover
purposes retain `NoSourceSemanticCompletion`; the continuation purpose has a
separate accepted-terminal-indexed private output contract. Each arm records
exact decision- and terminal-source export coordinates and atomicity; an
inactive arm is absence, not an empty value tuple.

The source quotient and static OIR graph therefore gain:

- site-qualified decision and accepted-terminal recipe nodes;
- site-qualified private-export coordinates, not merely output types;
- a continuation-prover purpose; and
- a private Plan-output contract.

An old endpoint/OIR profile must reject the rotated Plan grammar. It may not
silently project away a reachable terminal recipe or continuation export.
Runtime continuation issuance remains the PIR Plan operation; OIR does not
claim a live private-output projection until a later Realization design
activates that boundary.

## 7. Recursive verification and identity

Verifier-in-circuit recursion is represented as a finite Relations predicate:

```text
previous proof value
  -> private witness occurrence of the outer relation

finite prior-verifier computation
  -> canonical relation-definition graph

new outer proof
  -> ordinary output of the outer Plan and ordinary input to the outer Core
```

The outer Core does not execute a child Core. Direct verifier-observable
imported checking remains a different source shape: pure Boolean verification
uses an exact Core `Check`, while richer stateful or multi-observation
behavior may use the module-effect seam.

BCTV's apparent setup cycle is broken by asymmetric construction order:
the first circuit receives the later verification key as witness, the second
circuit hardcodes the processed first verification key, and setup then fixes
the later key. A separate setup/key-correspondence proposition checks the
concrete result. No relation or Protocol contains its own ID, and no hash
fixed point is introduced.

The exact BCTV target inhabitant remains open. The pinned source does not close
the complete circuit payload, setup instance, proof codecs, Fresh OIR profile,
or numeric evaluator envelope. That limitation reduces the achieved depth; it
does not weaken the owner and identity conclusion, which is independently
preserved by Fractal's non-cycle construction.

## 8. Fiat--Shamir and property boundary

Every target strong-Fiat--Shamir sibling must absorb the complete ordered
input Statement and accumulator state plus every challenge-dependent prior
publication. A source theorem using a weaker prefix does not transport merely
because the target construction is formable.

This matters directly for HyperNova Construction 5, whose source random-oracle
prefix omits input Statements. The source construction remains representable,
but it is not classified as the target strong-FS sibling and supplies no
theorem for the strengthened target construction.

Folding correctness, accumulation preservation, IVC induction, recursive
composition, knowledge, zero knowledge, setup correspondence, classical-ROM
or QROM applicability, and post-quantum closure remain independent Analysis
questions. Lattice-based algebra or a transparent setup is not a protocol
security flag.

## 9. Rejected alternatives

The package rejects:

- an artificial final prover message added only to create a decision point;
- a general callback after every challenge;
- hidden post-terminal persistent-state mutation;
- a universal accumulator, folding-scheme, decider, or recursive-proof root;
- runtime child-Protocol execution for verifier-in-circuit recursion;
- treating Relations transforms as private producer authority;
- identifying proof values with proof bytes or host object occurrences; and
- deriving setup, theorem, or security facts from structural admission.

Each rejected alternative either changes the source interaction, duplicates
authority, destroys replay/identity closure, or generalizes far beyond the
cases that create pressure.

## 10. Promotion boundary

The selected shared laws were absorbed through one dependency-complete rotation
across:

1. Interface/Plan grammar, identity, admission, runtime generation,
   continuation completion, witness-surface extraction, and confidential
   Plan-witness views;
2. endpoint purposes, source graph, read manifests, exact-use closure, and
   private-output contracts;
3. OIR graph grammar, requirements, admission, projection, and validation;
4. Relations' occurrence classes and the new run-grounded Plan-witness arm of
   its existing correspondence question; and
5. the boundary that keeps Analysis properties and later
   Realization/deployment profiles separate and open.

`InteractiveCore`, `Protocol`, and Fiat--Shamir construction identities do not
rotate solely because of these Plan changes. The recursive-import result adds
only a clarification to the existing Core-versus-Relations import boundary;
its missing concrete profiles remain future owner-local work.

## 11. Reopening conditions

Reopen this selection only if an exact source-faithful case shows that:

1. terminal-private derivation must alter verifier-observable semantics;
2. the selected read grammar cannot express a required value without an
   ambient callback or future read;
3. atomic continuation exports cannot be grounded to distinct next-run witness
   occurrences;
4. a native post-challenge decision cannot own a source output attributed to
   it here;
5. verifier-in-circuit recursion cannot be represented by one finite typed
   relation graph; or
6. the proposed owner graph contains a semantic identity cycle after exact
   profile bodies are formed.

Performance inconvenience, authoring verbosity, or reuse opportunity alone is
not a reopening condition.

## 12. Nonclaims

This selection establishes no implementation support, protocol proof,
security theorem, setup trust, transcript theorem, recursive-composition
result, endpoint execution, backend conformance, performance result, semantic
freeze, or migration readiness. Its target ownership and lifecycle laws are now
stated by the durable PIR, Relations, and OIR owners. That closes only semantic-
target selection and promotion; complete profile preimages, independently
reconstructible identities, holdouts, independent identity/profile freeze,
properties, Realization, implementation, and normative cutover remain open.

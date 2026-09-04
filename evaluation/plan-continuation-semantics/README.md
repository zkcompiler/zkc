# Plan continuation semantic validation

This package is a finite executable falsifier for the selected Plan-owned
generation, accepted-terminal continuation, confidential witness, causal
handoff, Relations grounding, and static endpoint/OIR boundaries. It reuses
the existing Protocol reference executor as the only Core execution engine.
The new model supplies only the admitted Plan strategy adapter around that
unchanged executor.

It is a research instrument, not normative specification, a compiler or
endpoint implementation, a prover, a source-conformance implementation, or a
cryptographic proof.

## Model under test

```text
admitted finite Core + admitted ProverPlan
        |
        | PreparePlanExecution
        v
Plan-owned strategy adapter
        |
        | existing Protocol generation
        v
CompletedPlanRun + causal Plan-generation capability
        |
        +------ Generated confidential witness view
        |
        | CompleteAcceptedPlanContinuation
        v
atomic accepted-terminal continuation arm
        |
        +------ Finalized confidential witness view
        +------ private Relations grounding
        +------ IssueAcceptedPlanWitnessIngressSupply
                         |
                         | atomic target preparation
                         v
                  fresh WitnessIngress occurrence
                         |
                         +------ JoinCausalPlanWitnessHandoff
                         +------ JoinCausalPlanStepRecurrence
```

Public recurrence grounding remains a separate proposition. Its exhaustive
three-leg equation reads four owner-derived anchors: the exact source-run
public output, source-instance public slot, target-instance public slot, and
target-run Statement binding. Missing, extra, self, or disconnected legs are
malformed. Equal public values from an unrelated run, instance, or role cannot
join the private handoff, and cannot create the
`ReadyPlanWitnessIngressSupply` and its one-use capability, the fresh target
occurrence, or the `CausalPlanWitnessHandoffCapability`.

The static continuation endpoint/OIR contract is derived twice. The primary
model derives the source quotient; `independent_oir.py` reconstructs the same
site-qualified graph and terminal arms without calling that derivation. Both
take the exact Core and Plan. Arm membership is derived from Core order and
the closed `GuardImplies` law rather than from a Plan-authored guarantee.
Every retained recipe operand, move, state update, declaration kind/type, and
selected export participates in the finite endpoint identity. An empty
continuation purpose is unsupported before projection and malformed if
authored directly as OIR.

## Finite family shapes

| Family | Imported evidence depth | Continuation pressure |
|---|---:|---|
| Nova | T2 | final-coin folded witness requires accepted-terminal derivation |
| HyperNova | T1 | final `rho` leaves no later prover decision; complete target elaboration remains open |
| CycleFold | T1 | primary witness is decision-derived; companion witness is terminal-derived |
| ProtoStar | T1 | genuine post-`alpha` accumulator publication owns the private export |
| LatticeFold+ | T1 | genuine decomposition publication owns two distinct private exports |

The T1 records are architecture-pressure shapes, not exact paper-algorithm
implementations. Passing this gate does not upgrade their evidence depth. The
toy values in `private-generation.json` are excluded from every semantic ID.
Declassified invocation and scripted Fresh inputs live separately in
`public-inputs.json`; the mutation ledger invokes one executable outcome probe
for every row rather than merely naming a test method.
The source ledger is inert metadata and supplies no theorem or authentication
authority. Fixture construction is tested to load exactly the family shape,
private-generation, and public-input files, never the source ledger.

## What is checked

The suite covers exact decision coverage, site-local recipe DAGs, total state
updates, first-actual-demand randomness, an unforgeable Plan-owned adapter
path into Protocol generation, one-use generation and continuation rights,
atomic terminal arms, all three witness occurrence classes, generated versus
finalized confidential sources, private grounding, same-run public/private
joins, one-use output-to-ingress handoff, propagated causal handoff authority,
public recurrence separation, ordinary versus continuation endpoints, dense
private output references, source-blind OIR admission, independent static
projection, replay refusal, cross-run substitution, and representative
malformed and noncompletion mutations. Plans name the exact Fresh Protocol;
private material and randomness have exact kinds and value types. A handoff is
bound to the exact target Protocol, Core, Plan, WitnessIngress coordinate, and
identical value type, while its continuation and ready-supply capabilities are
accepted only by object identity. Confidential consumer and purpose roles are
nominally distinct and derived from the exact grounding question rather than
supplied as grounding-policy arguments.

The recurrence coordinate grammar intentionally implements a finite subset:
Prover messages, Verifier messages, and Oracle publications can be selected as
source-run public outputs. Raw challenges and terminal occurrences are
`Unsupported`; this evaluator does not claim the wider terminal-public-output
ordinal or module-observation grammar.

Qualified outcomes remain distinct. In particular, unequal well-formed
grounded values are `Negative`; missing live output is `CannotAnswer`; replay
qualification is `Unsupported`; and a different live session, capability,
consumer, purpose, or handoff is `Refused`.

## Run

From the repository root:

```sh
python3 -B -m unittest discover \
  -s evaluation/plan-continuation-semantics/tests -v
python3 -B evaluation/plan-continuation-semantics/run.py --check
```

The focused gate currently contains 52 tests, including 18 executed mutation
probes.

The package uses only the Python standard library and repository-local
reference executor. It performs no network access and writes no generated
artifact.

## Evidence boundary and residual trust

The evaluator-local canonical JSON hashes test identity locality; they are not
byte parity with the durable canonical bodies. Python object identity and
noncopyable wrappers are bounded proxies for process-local capability
identity, not a host-language security boundary. The instrument trusts the
Python runtime, the existing Protocol reference executor, its fixture-level
Core semantics, the manually reconstructed family shapes, and the two local
projection implementations.

The handoff result establishes a causal source-output-to-fresh-target-ingress
edge for one finite pair of runs. It does not prove relation satisfaction,
fold preservation, IVC induction, recursive composition, completeness,
soundness, knowledge, zero knowledge, setup trust, Fiat--Shamir applicability,
post-quantum security, production confidentiality, or implementation support.

# Weakest-precondition proof interfaces

Lean 4.35's `Std.WP` and experimental `vcgen` provide proof authoring interfaces
for existing zkc judgments. A generated verification condition is an obligation,
not evidence that the obligation holds. The ordinary kernel checks the resulting
proof. Receipt meanings, the protocol process and the three-standard-axiom policy
remain independent of the proof tactic.

## Interpretations

A `PIR.Process` does not determine one weakest precondition. The interpretation
is selected locally, alongside the handler or transcript interface. Importing a
module never installs a process-wide instance.

| Interpretation | Assertion state | Return boundary | Stop boundary |
|---|---|---|---|
| Charged rejection | Actual ordered transcript history | Selected residual or rejection predicate | `True` at the soundness boundary |
| Pathwise cost | History and remaining `ENNReal` credit | At least the continuation's reserved credit | `True` at the cost boundary |
| Concrete execution | Complete handler state and preceding event trace | Actual returned value, final state and trace | Explicit reason, final state and trace |
| Monadic execution | Complete handler state and preceding event trace | Bind-faithful postcondition on actual returned records | Explicit reason, final state and trace on stopped records |

`ZkcSecurity.ProgramLogic.WeakestPrecondition` owns the first two interpretations.
Its charged WP is definitionally equal to `Interface.Charged` at the soundness
stop boundary. `triple_iff_derivation` proves equivalence to the existence of the
existing `Derivation`; `ofTriple` retrieves that proof object. This use of choice
selects a proof of an already fixed proposition, never a knowledge extractor.

`costWP_iff` proves equivalence to `Typed.ChargedCostBound` at the trivial return
and stop predicates. `reserve` gives a continuation arbitrary returned values and
reached histories with its reserved credit. It assumes neither independent calls
nor finite costs and uses no subtraction of infinities. Query prices are assessed
at the reached history. The bound covers every admitted path, not expected cost.

The core `PIR.WeakestPrecondition` instead interprets the actual `Process.run`.
Its adequacy includes state, ordered events and all terminal reasons. Setting its
stop predicate to `False` requires an actual return. This is suitable for a
pointwise honest-completeness proof under a fixed answer table.

`MonadicWeakestPrecondition` instead uses the same `Process.runM` and
`Std.Do.Internal.Ensures`. The local `wpMonadM` selects the handler and outer
monad. `tripleM_iff_run` states its exact execution meaning; `runMWP_id_iff`
recovers the actual complete record in the deterministic instance. Bind
composition retains event order and the state of a stopped prefix. It neither
erases already performed work nor enters the skipped continuation.

For an arbitrary outer monad, this is a partial execution postcondition.
Setting the stopped predicate to `False` excludes stopped **records**, but
does not establish that a record is produced or that probability mass is one.
Universal honest termination or a support/mass theorem is still needed.
`Region.ReturnsSatisfying.iff_triple` preserves precisely the existing partial
source judgment; it does not strengthen it to completeness.

## Reusable rules and obligations

The charged and cost interfaces provide receive, send, query and halt rules,
component rules, and bounded-loop invariant rules. A receive uses the actual
recovery equation; sending updates the transcript even when it consumes no proof
message. A charged query requires a proved escape bound for a raw-answer bad
event and a continuation proof for every successful decoding outside that event.
A cost query reserves a budget for every reply. Neither rule invents a polynomial
root bound, a binding theorem or a sampling assumption.

Loop invariants remain mathematical inputs. The zero-iteration case must satisfy
the terminal invariant independently of the body. Existing Sumcheck residual and
loop-budget theorems can be installed as component specifications with
`derivation_spec` and `bound_spec`; the root proof does not unfold the loop or
repeat its mathematics. `vcgen` handles sequential composition and guards while
ordinary Lean proves the remaining residual implications and budget inequalities.

The real raw Sumcheck root rejection and cost proofs use these interfaces.
Generated applications of shared family theorems inherit their checked proof;
there is no reason to duplicate a family's verification conditions at every
source instantiation. Cross-process simulations and theorems transporting a cost
bound are relational laws, rather than programs to be reinterpreted as triples.

## Completeness and experiments

The charged reading is partial rejection reasoning. In particular, refused
absorption and failed raw decoding are rejected paths. Changing only its explicit
halt predicate to `False` does **not** establish successful execution. Honest
completeness uses the concrete execution interpretation instead.

The honest-pair bridge relates a concrete execution triple to the existing
pair-success event. Quantification over every shared answer table feeds the
existing perfect-completeness theorem. Local service assumptions and the
producer-to-validator state handoff remain explicit. Stops cannot be counted as
success, and the oracle state is not reset between the participants.

The [private-producer consumer](selected-property-adapters.md#private-producer-and-concrete-verifier-wp)
extends this route without assigning a common answer table to private draws.
It quantifies over actual supported sampled producer executions and proves the
same concrete verifier WP for each emitted proof. The canonical consumer retains
input preparation, nonvacuity and all unsuccessful probability mass. Its selected
verifier scope is a returning deterministic table run; fresh private validator
continuations require a separate support-aware proof.

The validator WP does not replace the probabilistic experiment/adversary layer.
An opaque adaptive adversary still requires its existing resource and interface
contract. Cache hits and fresh samples have different laws; distributional
couplings must preserve cache state and ordered observations. The existing
VCVio/ArkLib transport, sampling and coupling theorems retain those obligations.
No expected-cost or output-only WP is substituted for a worst-case, full-state
experiment statement.

## Lean integration

Enable `experimental.vcgen` only at proof sites that use it. The Lean 4.35
`wpTrans` and `wp_trans_monotone` fields occur only in the local instance
definitions. Their future renaming does not affect protocol statements or family
contracts. Pure program constructors have generic specs that choose no security
interpretation. Domain-specific and resource rules are supplied explicitly.

For indexed reply types, normalize local specification hypotheses and the
program before calling Lean 4.35's experimental matcher. A useful proof shape
is:

```lean
let := chargedMonad absorb escape antitone
have receiveLaw := receive_spec absorb escape antitone operation event recover absorbed
-- Give any remaining query-cut or resource parameters explicitly.
dsimp only [ChargedTriple, program] at *
vcgen [receiveLaw]
```

This exposes reply projections and instantiates local hypothesis types for the
matcher; it is definitional normalization, not an additional proof assumption.
The concrete receive/send/query controls exercise this form together with
history-dependent prices, decoding failure, stopped paths and infinite credit.

The [source assembly design](../design/source-proof-assembly.md) distinguishes
the validated local adapter from source construction. A bounded comparison
finds that a reduced dependent source restriction fails generic specification
matching on 4.35 and succeeds on 4.36-rc1. The actual Sumcheck terminal's existing
decision equation composes through `vcgen` on 4.35; complete FRI assembly through
that engine remains unvalidated. The common `derive_oracle_returns` constructor
currently selects typed rules for the actual FRI reply region and independent
new components, including deriving their ordered return layout. These are
proofs about the existing execution. Neither tactic choice establishes totality,
source/realization correspondence or a toolchain migration.

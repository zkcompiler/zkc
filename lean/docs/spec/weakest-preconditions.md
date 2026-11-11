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

`ZkcSecurity.Obligations.WeakestPrecondition` owns the first two interpretations
as proposition-valued readings. `chargedMonad absorb escape antitone` and
`costMonad absorb charge` are local `WPMonad` instances whose assertions are
`List E → Truth` and `List E → ENNReal → Truth`. There is one charged reading,
generic in its escape judgment, and one cost reading. The exact reading is the
charged reading at `exactEscape`, which excludes no reply; the bounded reading
is the charged reading at `boundedEscape charge`, which excludes a set of raw
replies whose uniform probability is at most the site's charge
(`Zkc.Protocol.Obligations.Bounded`).

The folds `chargedWP`, `costWP` and `costNode` read the process exactly as
`Interface.Charged` and `ZkcSecurity.FiatShamir.Typed.ChargedCostBound` do. The monads apply them
pointwise and wrap the result.

### The assertion carrier

`ProtocolProof.Truth` is a one-field structure around `Prop`, ordered by
implication (`Zkc.Protocol.Construction.Truth`). It is the lattice of
propositions. It is a structure because upstream VC generation gives an
assertion type that is syntactically `σ → Prop` a special treatment: it
introduces the state and turns the precondition into a hypothesis. The common
constructor instead keeps every goal in the shape `pre ⊑ wp program post
stopped` and derives intermediate bounds as lattice elements; the special
treatment removes that shape. `Truth` is opaque to it, exactly as `ENNReal`
potentials are. Statements write assertions as `⟨P⟩`:

```lean
⦃fun _ => ⟨True⟩⦄ game
⦃fun out _ => ⟨out.2 = true → Extracted out.1⟩; estack⟨fun _ _ => ⟨True⟩⟩⦄
```

`ProtocolProof.Truth.rel_iff`, `ProtocolProof.Truth.rel_fun_iff` and `ProtocolProof.Truth.mk_rel_mk_fun` state that the
order is (pointwise) implication. No coercion from `Prop` is installed: the
assertion type of a triple is an output of instance resolution, so a bare
proposition would fix it to `σ → Prop` before the reading is found.

### Adequacy

The carrier never reaches an endpoint statement. Adequacy turns triples into the
existing proposition-valued judgments:

- `wp_eq_charged`: the charged WP at the soundness stop postcondition is
  `Interface.Charged`.
- `triple_iff_derivation` and `ofTriple`: a charged triple with that stop
  postcondition is exactly a `Derivation` from every history satisfying the
  precondition. `ofTriple` uses choice to select a proof of an already fixed
  proposition, never a knowledge extractor.
- `charged_of_triple`: a triple with postcondition `fun value history =>
  ⟨Post history value⟩`, under any stop postcondition, gives
  `absorb.Charged escape Post process history` for every history satisfying its
  precondition. This is the form the endpoints consume.
- `costWP_iff`: the cost WP at the trivial return and stop predicates is
  `ZkcSecurity.FiatShamir.Typed.ChargedCostBound`. `costBound_of_triple` gives the pathwise bound from
  every state satisfying a cost triple's precondition, whatever its
  postconditions; `cost_of_triple` is its trivial-postcondition instance.
- `charged_mapEscape`: the charged reading is monotone in its escape judgment.
  `charged_of_exact` and `bounded_of_exact`: exact evidence is charged evidence
  for every antitone judgment that accepts the empty event, in particular for
  every bounded judgment.

`reserve` gives a continuation arbitrary returned values and reached histories
with its reserved credit. It assumes neither independent calls nor finite costs
and uses no subtraction of infinities. Query prices are assessed at the reached
history. The bound covers every admitted path, not expected cost.

The core `PIR.WeakestPrecondition` instead interprets the actual `PIR.Process.run`.
Its adequacy includes state, ordered events and all terminal reasons. Setting its
stop predicate to `False` requires an actual return. This is suitable for a
pointwise honest-completeness proof under a fixed answer table.

## Reusable rules and obligations

Each reading has one primitive call rule and one stop rule, registered `@[spec]`:
`call_spec` and `halt_spec` for every charged reading, `call_cost` and
`halt_cost` for the cost reading. The call rule's precondition is the node
obligation of the operation's absorption. The rules are stated for
`chargedMonad absorb escape antitone` with all three as parameters; the monads
are `instance_reducible`, so unifying a rule with a client's instance recovers the
interface, the judgment and its antitonicity proof. The exact and bounded readings
therefore need no rules of their own.

The node equations state each obligation by absorption kind. A receive
constrains every recovered message, a send continues with its value, a refusal
holds. A query under any escape judgment is that judgment of the decoded replies
whose continuation fails (`chargedNode_query`). Under the exact judgment it
constrains every decoded reply (`chargedNode_query_exact`); under a bounded
judgment it is a probability bound for the replies that escape
(`chargedNode_query_bounded`). A cost query reserves
the site's charge and a continuation budget for every reply.

`receive_spec`, `send_spec`, `query_spec` and their cost counterparts state the
same obligations from an explicit absorption equation and an explicit cut or
reservation. `derivation_spec` and `bound_spec` install existing component
derivations and budgets as specifications. Neither rule invents a polynomial
root bound, a binding theorem or a sampling assumption.

Loop invariants remain mathematical inputs. `repeat_spec` and `repeat_cost_spec`
take a remaining-iteration invariant; the zero-iteration case must satisfy the
terminal invariant independently of the body. The common constructor takes the
same invariant through `construct_region with_invariants`.

## Endpoints

The readings feed two endpoints with the same premises: the charged reading at a
bounded judgment and a pathwise charged cost bound.

- The Fiat–Shamir endpoint `ZkcSecurity.FiatShamir.Typed.soundness_charged`
  consumes `certificate accepts terminal` from `Zkc.Protocol.Obligations.Bounded`;
  `certificate_doomed` identifies its doomed pairs with the bounded charged
  reading.
- The interactive endpoint `ZkcSecurity.Interactive.soundness`
  (`Zkc.Protocol.Logic.Transcript.Interactive`) runs the process against an
  adversary strategy that sees the absorbed history and every earlier raw draw,
  answering each query with a fresh uniform sample. The probability that a run
  returns a value violating the postcondition is at most the cost, with no
  adversary-query term. `soundness_accepted`, `soundness_randomized` and
  `fresh_transform_soundness` state the acceptance form, a distribution over
  strategies, and the transform with fresh sampling as its oracle.

Cross-process simulations and theorems transporting a cost bound are relational
laws, rather than programs to be reinterpreted as triples.

## Completeness and experiments

The charged reading is partial rejection reasoning. In particular, refused
absorption and failed raw decoding are rejected paths. Changing only its explicit
halt predicate to `False` does **not** establish successful execution. Honest
completeness uses the concrete execution interpretation instead.

The readings bound acceptance; they do not show that an execution returns. A
process whose interface refuses an operation, or whose query decoder rejects every
raw answer, satisfies the charged and exact triples even with false return and stop
assertions, while its run stops `refused` or `exhausted`; neither execution
accepts. A completeness statement needs an interface that admits every operation
with total decoders, or an outcome-aware adequacy theorem. For the first,
`ZkcSecurity.Interactive.returns_of_exact` shows that over a `Total` interface an
exact triple whose stop assertion is false for every reason makes every run of the
interactive experiment return a value satisfying the postcondition. No
outcome-aware adequacy theorem for other interfaces is provided.

The interactive endpoint quantifies over strategies that see the absorbed history
and every earlier raw draw. A bound against these strategies holds for any
strategy that sees less. A statement about a secret sample is obtained by
instantiating the endpoint at a strategy that does not read that draw; the
endpoint does not make a draw secret.

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

The readings are constructed with the common constructor. Import
`Zkc.Tools.Protocol.Readings`, install the reading as a local instance and
register the concrete interface for structural normalization:

```lean
noncomputable abbrev logic := chargedMonad absorb (boundedEscape charge) (boundedEscape_antitone charge)
attribute [local instance] logic
attribute [local construction_simp] absorb

theorem round_wrong … : ⦃Wrong S (env .here)⦄ round.denote … ⦃fun out => Wrong S (out.get .here); …⦄ := by
  unfold round
  construct_region
  -- the probability bound of the challenge site
```

A request may also be stated as `ChargedTriple` or `CostTriple`; the constructor
exposes the triple through the reducible abbreviation. The remaining goals read as
plain propositions over the quantified histories, messages and replies. Plain
`vcgen` stops at a primitive call whose continuation sits under the node's
quantifier, because a `Truth` assertion is opaque to it; the constructor exposes
each continuation before applying the call rule, so it reaches every node.
The concrete receive/send/query controls exercise history-dependent prices,
decoding failure, stopped paths and infinite credit.

# Authoring against the standalone framework

The complete checked clients are [AdaptiveChecks](../ProtocolProofExamples/AdaptiveChecks.lean)
and [SharedState](../ProtocolProofExamples/SharedState.lean). These are mathematical model games,
not translations of a zkc program. The first has arbitrary nested rounds and history-dependent
strategies; the second has a persistent shared challenge, observable state, an erased audit
counter, and components containing several primitive operations.

## Fix the claim before selecting its proof

A request fixes the experiment, the admitted environments, the observation and the bound. The
soundness constructor computes acceptance of a false statement. The completeness constructor
requires unconditional accepting mass at least `1 - error`. Neither proof method chooses those
facts. For example, the adaptive client's exact requests are `soundnessRequest count width`
and `completenessRequest count width`; both use `system.experiment (game count width)`.

The examples explicitly choose the environment interface. `AdaptiveChecks.Strategy` is a
function from prior challenge history to the next bit. It cannot read the current fresh
challenge before choosing that bit. This test quantifies over all such deterministic strategies;
it does not assert a separate resource-bounded cryptographic adversary theorem.

## Write or reuse the mathematical contract

An operation specification consumes the potential of its continuation and produces a potential
on the current state. The fair-bit operation uses the exact average of the two possible
continuations. `UpperBound.bind` and `LowerBound.bind` combine local contracts without assuming
that successive operations are independent. The expected potential is evaluated at the actual
returned answer and successor state.

For arbitrary rounds, the author supplies an indexed invariant and a body contract. The
adaptive example uses a remaining-error potential of this shape:

```lean
fun round next _ =>
  reward next.2 (factor residual ^ (count - round) * value)
```

Its one-round mathematics is in `primitive_upper` and `primitive_lower`. The complete round
and batch proofs invoke the same `UpperBound.iterate` and `LowerBound.iterate` rules. A batch
is a component body for the next loop; no additional traversal theorem is authored.

The shared-state example uses the indicator that the first guess matches the hidden bit as
its potential. Its integral is one half. The second check uses the same bit, so there is no
second independent factor of one half. The theorem `multiplying_check_probabilities_invalid`
proves that the proposed product bound is false.

## Install a representation once

If the actual and mathematical states agree, reuse `Connection.reflexive`. If a representation
map changes state, prove its local joint-law meaning and the initial-law pushforward, then use
`Connection.ofMap`. This includes maps that erase irrelevant information.

The shared-state client erases an audit counter but retains the hidden challenge and the
observable check counter. Its primitive equation is:

```lean
(primitiveConcrete operation state).map
    (fun out => (out.1, represent out.2)) =
  primitiveModel operation (represent state)
```

`Representation.contractOfMap` constructs the joint coupling, both marginal equations and the
preserved graph relation from that local equation. This is a library theorem for every client
of the interface, not a fresh whole-game correspondence proof.

The high-level component performs two primitive calls per operation. Its installation is:

```lean
primitiveInstallation.freeHandler componentImplementation
```

This is the upstream generic component-substitution theorem. It preserves the same state through
both calls and through each later use of the component. `component_inlining` additionally proves
that hierarchical execution equals the upstream inlined program interpretation. Resetting the
observable counter fails the local law, as checked by `resetting_counter_invalid`.

## Assemble the fixed root

`UpperEvidence` and `LowerEvidence` contain a subject binding, the reusable connection, the
operation specification with its local validity, a composed mathematical contract, an initial
budget, and the direction of the terminal implication. The final proof is, for example:

```lean
theorem shared_soundness : soundness.Holds := soundnessEvidence.establish

theorem shared_completeness : completeness.Holds := completenessEvidence.establish
```

The generic root theorem derives the probability claim. No evidence field has the type
`soundness.Holds`, `completeness.Holds`, or a renamed copy of that final conclusion. An arbitrary
whole-game mathematical theorem can still be used as a proof method, but is never presented as
an automatically discharged local operation obligation.

## What is reusable, and what remains authored

| Input | Current treatment |
| --- | --- |
| Execution and probability interpretation | Reused upstream definitions |
| From local joint laws to every adaptive client | Reused upstream theorem and generic event corollaries |
| Bind, branch, finite and nested iteration | Common checked rules |
| Identity representation | Common constructor |
| Meaningful representation or component implementation | Library/companion supplies the map and local meaning laws |
| Degree/root/proximity algebra or a new residual invariant | Mathematical library or companion |
| Initial coverage and requested observation implication | Explicit mathematical obligations, reusable when representations agree |
| Applying contracts and selecting invariants in these examples | Ordinary Lean theorem applications and simplification |
| Source traversal, typed IR binding, generated companions | Not implemented or connected by this standalone package |

Structural theorem reuse is implemented. A proof-search tactic or source-to-proof generator is
not required to use this core and is not claimed as implemented. Such tooling must produce
these same checked judgments. It must not weaken the request, replace a missing meaning law
with a name match, or ask each new protocol author to write another structural visitor.

The shared-state soundness and honest-completeness clients intentionally have different permitted
interactions: the honest client reveals the private bit before checking; the adversarial client
only receives previous check replies. They validate contextual composition and state handling.
They are not presented as a proof of knowledge, or as Schnorr AND security.

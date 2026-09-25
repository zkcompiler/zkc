# PIR subjects, interpretation and scope

PIR gives protocol interactions, participant algorithms and their execution
plans a common interpreted meaning. Its execution calculus supports structured
representations; specialized operations, modules and providers supply their
own interpretations and premises.

This guide explains the [interaction specification](../spec/language/interaction.md),
which owns the subjects, admission and scope definitions. The
[program specification](../spec/language/programs.md) defines common control;
[assurance](../assurance.md) reports proved and implemented boundaries.

## 1. Public families and semantic environments

[INT-01](../spec/language/interaction.md#public-families-and-semantic-subjects)
distinguishes public family parameters from invocation inputs. A family may
support every public size, even though each instance executes finitely.
Testing a few sizes does not establish that family law or polynomial time.
An application relation is independent of its selected proving protocol;
an arithmetic module need not acquire a witness relation of its own.

## 2. Interaction, role algorithm and execution plan

The three subjects in INT-01 answer different questions: which interactions
are permitted, what a role computes, and how a plan realizes that computation.
They do not require three universal IRs. Interpretation can itself lower an
operation into a body over another signature.

For example, fresh interaction and a specified Fiat–Shamir construction
have different state and probability obligations even when they return the
same field type. [Formal support](../../formal/SUPPORT.md) lists the
construction connections that exist and their scopes; the
[rationale](../rationale/semantic-abstraction.md) explains why a construction is
an interpretation and not a compiler stage.

## 3. Typed operations and interaction legality

[INT-02–03](../spec/language/interaction.md#roles-and-phases) define
reply-dependent advancement and all-reply conformance. Hostile payloads belong
to the actual interface domain. A receiving type that contains only honest
messages would change the security question.

Stopping inside a call does not take a fictitious reply edge. The actual-call
instrumentation retains that invocation and its effects. Conformance checks
permission, not acceptance or honest arithmetic.

## 4. A source-bound endpoint

[INT-05](../spec/language/interaction.md#endpoint-admission)
joins source identity, actual captures, elaboration, phase conformance, a public
call bound and a returned-value/phase condition. The chosen frontend establishes
its own input-access law. Mathematical function-valued `Proc` continuations
do not make arbitrary host closures portable or inspect their hidden captures.

## 5. Honest roles, strategies and views

A participant makes decisions from its declared view and retained memory.
Interaction phase is not automatically part of that view. A hidden global
choice that requires different local actions in identical local views fails
the locality condition; adding an owner label cannot repair it.

[INT-06](../spec/language/interaction.md#atomic-sessions) also distinguishes
session roles from physical principals and shared resources. Virtual-party
records do not create additional network participants. Joint randomness and
admissible adversaries belong to the [property experiment](security-properties.md).

## 6. Completion, claims and implementation choices

A returned value is not automatically verifier acceptance. Consider the
retained control in `F₅`: the false claim that the Boolean sum of zero is
`1` passes a deliberately incomplete round boundary with constant polynomial
`3`, since `3 + 3 = 1`. The final comparison with the actual zero polynomial
fails for every challenge. The [relation contract](security-properties.md#relation-bearing-results-and-terminal-verification)
therefore retains the actual terminal verifier obligation.

A later continuation can abort after an earlier verifier accepted. The
[continuation account](accepted-continuations.md) keeps those results and their custody
conditions separate where that is the promised interface. Ordinary sequencing
still uses the core's stopped-result semantics.

Likewise, two backends satisfying one weak postcondition need not be
interchangeable under the actual caller's state and observation contract.
[Interpreted contracts](contracts.md) and [realization](realization.md)
explain the required relations.

## 7. Supported envelope

[INT-09](../spec/conventions.md#execution-envelope) owns the
finite atomic envelope and its exclusions. A finite call bound does not bound
arithmetic hidden inside a provider. Atomicity also does not imply rollback:
failed actions retain effects already produced.

Unrestricted recursion, asynchronous projection, native concurrency and new
security properties require explicit extensions to this envelope or its
property account.

## 8. Formal reference and remaining work

The [program and interaction correspondence map](../spec/correspondence/programs.md)
classifies definitions, proved laws and adapter obligations separately.
[Status](../status.md) reports current implementation evidence. A predicate
named `honest`, a supplied operation interpretation, or a copied theorem name
cannot establish its premises for an actual external implementation.

## 9. Theory choices at this boundary

Dependent syntax establishes typed scope; algebraic effects separate bodies
from interpretation; phase and input refinements add different obligations.
Rationale records explain why [control is common while operations are
supplied](../rationale/operation-vocabulary.md), why there is
[no total choreography projector](../rationale/participant-generation.md) and why
the direct plan is [a profile, not a mandatory second IR](../rationale/direct-plan-profile.md). [Theory](../theory.md) maps the broader methods and sources.

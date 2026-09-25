# Evidence, requirements and use

A checking result states a proposition about an actual mathematical context.
Conditional evidence retains the premises needed to use that proposition.
Logical proof, native checker correspondence and cryptographic assumptions
are distinct parts of an application's evidence.

## Conditional evidence

Let `Context` be a type of actual subjects, inputs, interpretations and observers,
and let `claim : Context → Prop`. A conditional judgment consists of:

```text
Conditional Context claim =
  (requires : Context → Prop,
   valid : ∀ ctx, requires ctx → claim ctx).
```

The requirement is a proposition on that same context. A context may package
types and interpretation families; it is not restricted to a serialized record
or to the executable source's type universe.

For `j : Conditional Context claim`, use at `ctx` requires a proof of
`j.requires ctx` and yields `j.valid ctx` applied to that proof. A requirement
label, revision or digest alone does not establish the proposition.

## Conjunction and transport

For `j : Conditional C P` and `k : Conditional C Q`, their conjunction has:

```text
requires ctx = j.requires ctx ∧ k.requires ctx
claim ctx    = P ctx ∧ Q ctx.
```

Both component proofs use that same context. For a producer
`j : Conditional C P` and a conditional rule
`r : Conditional C (fun ctx => P ctx → Q ctx)`, transport has:

```text
requires ctx = j.requires ctx ∧ r.requires ctx
claim ctx    = Q ctx
valid ctx (hj, hr) = r.valid ctx hr (j.valid ctx hj).
```

The producer's evidence does not discharge the rule's requirements. Rebinding
evidence to another context requires the theorem's actual quantification or a
justified transport relating the contexts. Matching names or digests does not
identify changed source inputs, providers or observers.

*Example.* Evidence of `2 ≤ n` under `3 ≤ n`, combined with a rule yielding
`n < 6` under `n ≤ 5`, retains `3 ≤ n ∧ n ≤ 5`. The producer can apply at `n=8`;
the combined result cannot be used there.

## Evidence-bearing check results

For a proposition `P`, define:

```text
Inconclusive = missingInterpretation | unsupported | resourceLimit | checkerDefect

Check P = established(proof : P)
        | refuted(proof : ¬P)
        | unknown(reason : Inconclusive).
```

`proves` holds for the established branch and is false for the other two
branches. Thus `proves result` implies `P`, using the proof carried by that
result. A refutation carries a proof of `¬P`; an inconclusive result carries
neither a proof of `P` nor a proof of `¬P`.

This result type does not provide a decision procedure for every proposition.
A sound sufficient [analysis](analysis.md) can return no admission evidence
for a semantically valid program. That failure need not have the information
required to construct a logical refutation.

A native checker claiming an established result MUST connect actual parsed
input, executed checking, retained subject and returned result to the relevant
proof or trusted checking contract. It states its parser, checker/kernel and
execution trust boundary. Mathematical and cryptographic assumptions remain
the selected judgment's premises; a native success flag does not discharge them.

## Failure boundaries

Failures retain the meaning of the boundary at which they occur:

| Boundary | Meaning |
|---|---|
| Serialized input decoding | Malformed input or an unsupported external shape does not form the selected input object |
| Evidence or analysis | Missing meaning, unsupported constructs, resource limits or checker defects are inconclusive about the queried proposition unless separate evidence refutes it |
| Interpreted protocol execution | Verifier rejection, provider exhaustion and other modeled stops retain the actual state and ordered events |
| Native execution without completion | A process that produces no completed result has no completed semantic outcome unless a separate runtime rule defines one |

These boundaries need not share a universal status enum. An input error before
execution is not an extra protocol stop. A checker timeout is not a verifier's
rejection. A native crash is not an automatically returned `incomplete` result.
An explicitly modeled instruction-list `incomplete` exit follows its
[own semantics](../profiles/realization/instruction-machine.md#embedded-machine-exits).

## Caller requirements

Let `legal` be the transformation or execution proposition and `requirement`
the caller's requested property. Usability consists of both proofs:

```text
Usable legal requirement ⇔ legal ∧ requirement.
```

A requirement can concern time, memory, accepted assumptions, security or another
declared property. Legality alone establishes none of these automatically.
Resource conclusions identify actual quantities, units, input domain, observer
and evidence. Bounds on interface calls are not automatically bounds on native
time or storage.

## Cost comparison and optimality

For natural-valued actual costs and bounds, the sufficient comparison rule is:

```text
actualA ≤ upperA
upperA ≤ lowerB
lowerB ≤ actualB
─────────────────
actualA ≤ actualB.
```

The bounds constrain actual costs in the same comparison. Two upper bounds
alone do not establish their ordering.

*Example.* Actual costs `9` and `1` satisfy upper bounds `10` and `20`. The
smaller upper bound belongs to the more expensive actual computation.

A candidate can be usable while alternatives remain unresolved. An optimality
claim defines a comparison domain and a criterion and establishes the result
over that entire domain. Unresolved alternatives remain in it unless the domain
definition or another proof excludes them. Search failure does not silently
remove a candidate from the comparison.

The selected [preparation accounting law](../profiles/compiler/factor-preparation.md#immutable-preparation-and-prices)
gives a narrower exact comparison under its supplied prices and operational
counts. It does not establish an unrestricted optimizer optimum or a native
speedup without the corresponding cost model and evidence.

# Resolved source definitions

This profile adds shared definitions to the [typed region language](../../language/programs.md).
It fixes the meaning of calls to stored bodies after symbol resolution. It does
not select a protocol construction, establish participant locality, or define a
portable module format. The implementation is
[`Zkc.Source.Definitions`](../../../../formal/Zkc/Source/Definitions.lean).

The [generic static foundation](generic-definitions.md) separately specifies
requirement derivations and typed substitution before this resolved layer.

## Signatures and scope

Fix a language `L`. A definition signature is an ordered argument context and
one result sort:

```text
Signature = (arguments : List L.Ty, result : L.Ty).
```

A structured result sort may denote a tuple, polynomial or other domain value.
This profile does not impose scalar values. Its single result sort does not
settle the production IR's multiple-result representation. The
[common-protocol profile](common-protocols.md) adds ordered role-owned result
ports for distributed calls while reusing these local definitions.

For a definition scope `D : List Signature`, extend `L` with:

```text
primitive op        arguments = L.arguments op, result = L.result op
call ref            arguments = σ.arguments,   result = σ.result
                    where ref : Var D σ.
```

The original value sorts and condition interpretation are unchanged. A call
reference identifies a position and its exact signature in this actual scope;
matching another definition's signature is insufficient to substitute its body.

A definition table is built by:

```text
empty
extend(previous : Definitions D, σ : Signature,
       body : Region (L.withDefinitions D) σ.arguments σ.result)
  : Definitions (σ :: D).
```

The newest definition is at index zero. Its body can reference earlier
definitions, but neither itself nor later definitions. This represents an
acyclic resolved dependency order. It does not require MLIR declarations to
appear in textual dependency order. A future resolver must check and translate
the actual symbol graph, retaining the resulting reference map. These indices
are not persistent artifact, transcript, instance or invocation identities.

Bodies are stored once; calls and bounded loops retain their structure. A body
has only its declared value parameters as its lexical environment. Captures,
keys and resource handles needed by the body must be arguments or part of the
explicitly selected primitive interpretation. Their admission and ownership
remain separate contracts. Definition sharing does not allocate fresh resources
or reset existing state.

## Meaning and complete calls

Fix primitive interpretation `M`. The extended interpretation retains `M.Value`
and `M.condition`, interprets primitives with `M.operation`, and resolves calls
to the selected stored body. At the newest reference:

```text
operation(extend(D, σ, body), call here, values)
  = denote(body, meaning(D, M), values.get).
```

An older reference resolves recursively in `D`. A caller evaluates its ordered
operands and gives those values to the callee; it does not give the callee its
entire lexical environment. Returning binds the actual result in the caller's
environment and runs its normal suffix. The complete execution is:

```text
run(call ref args; next, η, s)
  = follow(run(actual_body(ref), eval(η, args), s),
           fun result state => run(next, η.push(result), state)).
```

Consequently, if the callee stops with `(stopped reason, final, events)`, the
call has exactly that complete result and never executes `next`. This includes
a primitive that changes state or emits events before stopping. A normally
returned `false` remains a result value; it is not a stopped execution.

Calls add no entry/exit events or hidden call stack in this profile. Protocol
invocation origins, scoped challenge identities and participant stop notification
must be represented by the surrounding profile. The production common-source
contract still needs those explicit bindings and returned/stopped boundaries.
This profile does not supply them merely by resolving a body.

## Renaming and optional inlining

Value-variable renaming and definition-reference renaming are distinct maps.
Adding a definition preserves earlier meanings at their shifted references.
A general definition-reference map preserves meaning only when every referenced
callee has the same interpretation on every actual argument tuple.

Inlining the newest definition performs both maps:

```text
inlined = bind(renameValues(actual_arguments,
                            shiftDefinitionReferences(body)),
               normal_suffix).
```

The suffix is stored once, including when the body branches or loops. For every
primitive interpretation, handler, environment and initial state, this concrete
transformation preserves the complete execution of the original call.
[`DefinitionInlining`](../../../../formal/Zkc/Compiler/DefinitionInlining.lean)
proves this equality using the existing capture and sequencing laws. No pure
handler or successful-return premise is required.

This is optional inlining. It does not justify replacing a callee by a
same-signature definition, discarding original input admission, or deleting
call-boundary observations introduced by another profile. Acyclic definitions
and finite region syntax also do not establish a uniform bound on primitive
effects; those meanings need the usual separate bound contracts.

## Maintained clients and remaining connections

The [Sumcheck definition](../../../../formal/Zkc/Protocols/Sumcheck/Definitions.lean)
stores the existing verifier source, including its accumulator, original
polynomial, round loop, rejection branch and terminal check. `run_eq_source`
proves equality to its existing staged interactive execution over any commutative
semiring with decidable equality, for arbitrary prover callbacks, inputs and
challenge lists.
It introduces no new security, PCS or commitment premise.

[Call controls](../../../../formal/Tests/SourceDefinitions.lean) exercise shared
nested calls, calls inside a loop, original captures, stopped effects and a
same-signature wrong-callee counterexample.
[Sumcheck controls](../../../../formal/Tests/SumcheckDefinitions.lean) retain
successful acceptance, failed round checks, exhausted coins and rejection of
the wrong original polynomial at the terminal.

Symbol/instance resolution, a portable decoder, role/resource admission,
common-to-participant projection and native execution are not implemented by
this profile. Their concrete connections must preserve these resolved-body
contracts rather than treat a type-correct call as an equivalence proof.

The [located-call profile](located-execution.md) supplies role-state lifting,
local-effect admission and shared-control agreement. It also proves that the
positive-round whole Sumcheck definition cannot be treated as a communication-free
local block. Distributed grammar, projection and native connections still remain.

The native [canonical local algorithm profile](../compiler/local-algorithms.md)
connects a straight-line closed subset to source parsing, MLIR calls,
construction, independent candidate checking and execution. Its canonical
expanded accounting is explicit; the generic inlining theorem does not by
itself prove native resource equivalence.

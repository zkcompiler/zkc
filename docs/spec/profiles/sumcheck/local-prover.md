# Local prover cuts

This component executes finite ring expressions and local coin calls until it
returns an abort or committed cut. Its returned message can be consumed by the
[product-provider experiment](one-round-consumer.md#committed-local-prover-consumer).

## Local prover state and code

The local prover component operates over a ring `F` with decidable equality.
Its expressions use the [pure expression grammar](../source/expressions.md#expression-syntax-and-meaning)
with variables of type `Input Nat | Register (Fin 4)`. Its local state and
history are:

```text
LocalEvent F = write(register : Fin 4, value : F)
             | coin(cardinality : Nat, outcome : Nat)
             | branch(tookZeroArm : Bool)

LocalState F = {
  inputs  : List F,
  regs    : Fin 4 → F,
  history : List (LocalEvent F)
}

initial(inputs) = (inputs, allRegistersZero, []).
```

Expression evaluation reads register values or `inputs[i]` with zero fallback
for a missing input. Register zero initialization is a language rule; missing
external inputs are rejected by the admission rule below before execution.
Local writes, coins and branches are:

```text
write(st,i,v) = st with regs[i]:=v,
                         history:=st.history ++ [write(i,v)]
coin(st,n,i,x : Fin(n+1)) =
  let t=write(st,i,cast(x.val))
  in t with history:=t.history ++ [coin(n+1,x.val)]
branch(st,b) = st with history:=st.history ++ [branch(b)].
```

The field or ring cast of a coin need not be injective; the natural outcome
and cardinality are retained separately. A coin records the write before the
coin event. In particular, bound parameter zero still requests `Fin 1` and
records the corresponding zero write and cardinality-one outcome.

The finite syntax is:

```text
Code = abort
     | assign(register : Fin 4, expression : Expr, next : Code)
     | random(bound : Nat, register : Fin 4, next : Code)
     | ifz(guard : Expr, yes : Code, no : Code)
     | commit(claim : Expr, constant : Expr, linear : Expr, quadratic : Expr).

Boundary F = { state : LocalState F, claim : F, message : F × F × F }
Cut F = stopped(state : LocalState F) | committed(boundary : Boundary F).
```

The expressions in a commitment are evaluated in the same current state.
Commitment returns the resulting claim, coefficient triple and unchanged
complete local state. It is terminal in this local language, before any later
verifier challenge. Four registers and three coefficients belong to this
component; they do not constrain the common program language.

## Local source, admission and cuts

The local effect signature has an operation for each `n : Nat` with reply
`Fin(n+1)`. The source expansion is:

```text
source(abort,st) = done(stopped(st))
source(assign(i,e,p),st) = source(p,write(st,i,eval(st,e)))
source(random(n,i,p),st) = call n (x ↦ source(p,coin(st,n,i,x)))
source(ifz(e,p,q),st) =
  if eval(st,e)=0 then source(p,branch(st,true))
  else source(q,branch(st,false))
source(commit(s,a,b,c),st) =
  done(committed(st,eval(st,s),(eval(st,a),eval(st,b),eval(st,c)))).
```

`Cut.stopped` is returned local data, not an outer process stop. Both returned
cut forms retain the original inputs and the executed local history. Local
state lives in source continuations and returned cuts; assignments and branches
emit no outer handler event by themselves. If a coin handler stops, common
execution retains that handler's actual state and events, but returns no cut
and promises no separate local-state snapshot. An interface needing that
snapshot selects an explicit reporting or state interpretation.

Define `exprInputs(e)` as expression dependencies filtered to input indices,
retaining occurrences. The full code dependencies are:

```text
codeInputs(abort) = []
codeInputs(assign(i,e,p)) = exprInputs(e) ++ codeInputs(p)
codeInputs(random(n,i,p)) = codeInputs(p)
codeInputs(ifz(e,p,q)) = exprInputs(e) ++ codeInputs(p) ++ codeInputs(q)
codeInputs(commit(s,a,b,c)) =
  exprInputs(s) ++ exprInputs(a) ++ exprInputs(b) ++ exprInputs(c).

inputCheck(p,inputs) = ∀ i ∈ codeInputs(p), i < length(inputs).
```

Admission checks every occurrence, including guards and dormant branches, and
then elaborates exactly `source(p,initial(inputs))`; failure returns no body.
The role and phase are both unit, every local coin operation is enabled, and
returned replies leave phase unit unchanged. The public call bound is:

```text
calls(abort) = calls(commit(s,a,b,c)) = 0
calls(assign(i,e,p)) = calls(p)
calls(random(n,i,p)) = calls(p)+1
calls(ifz(e,p,q)) = max(calls(p),calls(q)).
```

This bounds every typed-reply path, independently of actual inputs and coin
values. The admitted endpoint fixes the same code/input vector, start phase,
bound and returned-cut input-preservation condition. An empty input vector is
valid for code with no input occurrences. The correlated service's separate
five-capture setup requirement is not a requirement of standalone local code.

All local transitions preserve the input vector. Thus admitted input reads
remain in range throughout every operationally reached cut. Replacing the
missing-input fallback by any function `Nat → F` leaves evaluations unchanged
whenever their input occurrences are in range. This property uses the common
expression dependency law; multiplication need not be commutative.

The source itself selects no probability distribution for local coins. A
probabilistic interpretation supplies their actual law and retains both abort
and commit mass. The [product-provider consumer](../providers/product-tapes.md#actual-next-request-decision)
adds an explicit committed-only request decision; returned local abort data
does not automatically stop or request a challenge in every possible wrapper.
Input admission and local formation alone establish no false-claim acceptance
bound, confidentiality or native-source correspondence.

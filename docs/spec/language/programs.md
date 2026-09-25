# Typed programs

A program is finite syntax for operations, binding, branches and bounded
iteration. Its meaning is a [body](../core/execution.md#bodies) under a selected
interpretation and an environment of actual input values. Protocols supply the
operation vocabulary; the control structure is common.

The [common-protocol profile](../profiles/source/common-protocols.md) builds
role-tagged ports, explicit messages and shared distributed calls over the same
contexts and execution meaning. Its local computations reuse the regions
described here; its participant projection is a separate obligation.

## Language signatures

A language `L` consists of:

```text
Ty        : Type
Op        : Type
arguments : Op → List Ty
result    : Op → Ty
condition : Ty
```

`Ty` is the set of source sorts. `arguments o` is an ordered list, including
repeated sorts, and `result o` is the single result sort of operation `o`.
Several results can be represented by an explicitly interpreted aggregate sort.
The distinguished sort `condition` supplies the values tested by branches.

The language may contain several field, group, index or aggregate sorts. Their
[interpretations and conversions](../domains/values.md#sorts-and-interpretations)
determine their mathematical meaning. Equal host representations do not equate
distinct source sorts. A source operation cannot consume an operand of a
different sort through an implicit conversion.

`Ty` and `Op` are mathematical types. A portable profile supplies their concrete
descriptors, encoding and consumer resolution. Finiteness of a program does not
make an arbitrary descriptor type serializable.

## Contexts and values

A context `Γ` is a finite ordered list of sorts. The type `Var Γ τ` contains
references to exactly the positions of sort `τ` in `Γ`. Its constructors are:

```text
here       : Var (τ :: Γ) τ
there(v)   : Var (σ :: Γ) τ       where v : Var Γ τ

index here      = 0
index (there v) = 1 + index v
```

The newest binding is at position zero. Different positions remain distinct
even when their sorts are equal. The empty context contains no references.

For a value interpretation `V : Ty → Type`, a heterogeneous value list has one
value for each context entry:

```text
nil           : Values V []
cons(a, rest) : Values V (τ :: Γ)  where a : V τ, rest : Values V Γ
```

An environment for `Γ` has type `η : ∀ τ, Var Γ τ → V τ`; the sort argument is
implicit in `η v`. A value list supplies an environment by indexed lookup:

```text
get (cons a rest) here      = a
get (cons a rest) (there v) = get rest v
```

Extending an environment by `a : V τ` gives an environment for `τ :: Γ`:

```text
(η.push a) here      = a
(η.push a) (there v) = η v
```

Extension retains every original value at its successor position. It neither
reorders the context nor updates the original bindings.

## Operand lists

For a required argument context `Δ`, define
`Operands Γ Δ = Values (Var Γ) Δ`. An operand list contains typed references
into the surrounding context, in the operation's required argument order.
Evaluation replaces each reference by its actual value:

```text
eval η nil           = nil
eval η (cons v rest) = cons (η v) (eval η rest)
```

Evaluation retains order and multiplicity. Repeating a reference supplies the
same value at each occurrence. Exchanging two references of the same sort is a
well-typed syntactic change, whose semantic validity is a separate question.

*Example.* For `Γ = [F, F]`, `subtract [0, 1]` and `subtract [1, 0]` both
have the required argument sorts. With values `2, 4` in the field of order
five, they return `3` and `2`, respectively.

## Typed control

The judgment `Γ ⊢ p : τ` is relative to `L`. It has the following constructors
and no host-language continuation constructor:

| Program | Premises |
|---|---|
| `ret v` | `v : Var Γ τ` |
| `stop r` | `r : Stop`; any result sort `τ` |
| `letOp o args next` | `args : Operands Γ (L.arguments o)` and `L.result o :: Γ ⊢ next : τ` |
| `branch c yes no` | `c : Var Γ L.condition`; `Γ ⊢ yes : τ` and `Γ ⊢ no : τ` |
| `iterate n initial body next` | `n : Nat`; some accumulator sort `α`; `initial : Var Γ α`; `α :: Γ ⊢ body : α` and `α :: Γ ⊢ next : τ` |

`Stop` is the common [stop type](../core/execution.md#outcomes). Stopping does
not require a value of the declared result sort.

A loop body receives the current accumulator followed by the original
enclosing context. Its result supplies the accumulator for the next iteration.
The suffix `next` receives the final accumulator followed by that same original
context. Local operation results within the body do not become extra captures
of another iteration or of the suffix.

There is no implicit iteration-index variable. An index-dependent computation
includes the index in an interpreted accumulator or uses a separately specified
constructor. Mutable module state belongs to execution; it does not silently
rewrite lexical captures. An explicitly interpreted reference value can denote
mutable storage under its [lifetime contract](inputs.md#capture-lifetime).

## Operation meanings

At a fixed public instance, an interpretation `M` into an operation signature
`Σ` consists of:

```text
Value     : L.Ty → Type
condition : Value L.condition → Bool
operation : (o : L.Op) → Values Value (L.arguments o)
          → Proc Σ (Value (L.result o))
```

The branch test is the supplied Boolean interpretation of the condition value.
Each source operation is interpreted on its actual ordered arguments and may
return immediately, stop, or perform one or several interface calls. The source
operation descriptor by itself establishes no purity, call bound, phase law or
module precondition. Those claims concern this supplied meaning.

Source sorts and operation meanings need not coincide with an interface's
operation and reply types. A source operation can expand into a body that
combines several interface replies to compute its result.

## Denotation

For `Γ ⊢ p : τ` and an environment `η` interpreted by `M.Value`, write
`⟦p⟧M η : Proc Σ (M.Value τ)`. When `M` is fixed, omit its subscript.
Denotation is defined by:

```text
⟦ret v⟧η                 = done (η v)
⟦stop r⟧η                = halt r
⟦letOp o args next⟧η     = (M.operation o (eval η args)).bind
                            (fun a => ⟦next⟧(η.push a))
⟦branch c yes no⟧η       = if M.condition (η c) then ⟦yes⟧η else ⟦no⟧η
⟦iterate n a body next⟧η = (repeatN n (fun x => ⟦body⟧(η.push x)) (η a)).bind
                            (fun x => ⟦next⟧(η.push x))
```

For `f : A → Proc Σ A`, finite repetition is:

```text
repeatN 0 f a       = done a
repeatN (n + 1) f a = (f a).bind (fun b => repeatN n f b)
```

All sequencing uses [body composition](../core/execution.md#body-composition).
An operation or loop iteration that stops prevents the remaining iterations
and suffix from running. Its actual final state and event prefix remain in the
[complete execution](../core/execution.md#complete-results).

Zero iterations return the initial accumulator to the suffix without executing
the body. The body is still part of the typed program and must be formed.
A branch executes exactly its selected arm; formation checks both arms.

## Renaming

A renaming `r : Γ → Δ` is a sort-preserving family
`r : ∀ τ, Var Γ τ → Var Δ τ`. It need not be injective. Under a new binding,
its lifting is:

```text
lift r here      = here
lift r (there v) = there (r v)
```

Renaming a program acts on every reference and operand. It uses `lift r` in
the continuation of `letOp` and in both loop regions, and `r` in both branch
arms. It preserves operation descriptors, stop reasons and repetition counts.
For every `M` and environment `η` for `Δ`:

```text
eval η (rename r args) = eval (η ∘ r) args
⟦rename r p⟧M η       = ⟦p⟧M (η ∘ r)
```

Thus renaming is meaning-preserving relative to the corresponding environment
map, including cases where it aliases two source references.

## Source sequencing

For `Γ ⊢ p : α` and `α :: Γ ⊢ q : τ`, the syntax `seq p q` has type
`Γ ⊢ seq p q : τ`. Define `weaken v = there v` and the head substitution:

```text
substHead v here      = v
substHead v (there w) = w
```

Source sequencing is structural:

```text
seq (ret v) q                   = rename (substHead v) q
seq (stop r) q                  = stop r
seq (letOp o args tail) q        = letOp o args
                                    (seq tail (rename (lift weaken) q))
seq (branch c yes no) q          = branch c (seq yes q) (seq no q)
seq (iterate n a body tail) q    = iterate n a body
                                    (seq tail (rename (lift weaken) q))
```

The lifted weakening keeps `q`'s result slot at its head and moves its original
captures below the first region's new local binding. The loop body is unchanged;
`q` runs after that loop's suffix returns. The returned slot can alias an
original input without losing that input's role as a capture.

For every interpretation and environment:

```text
⟦seq p q⟧M η = (⟦p⟧M η).bind (fun a => ⟦q⟧M (η.push a))
```

Consequently, execution follows the first region's actual complete result into
the second. A stop in either region preserves all effects already produced.
This definition introduces no arbitrary host callback into source syntax.

## Reinterpreting operations

Let `θ` be an [operation interpretation](../core/interpretations.md#interpretation-interface)
from signature `Σ` to `Σ′`. Define `M.translate θ` to keep `M.Value` and
`M.condition`, and to replace each operation meaning by
`interpret θ (M.operation o args)`. Then:

```text
⟦p⟧(M.translate θ) η = interpret θ (⟦p⟧M η)
```

This equation uses the same `θ` for every operation expansion. Transporting
phase admission, bounds, observations or represented values requires the
corresponding additional interpretation or realization laws.

## Raw formation

Raw control has the grammar:

```text
Raw Ty Op = ret(index : Nat)
          | stop(reason : Stop)
          | letOp(op : Op, operands : List Nat, next : Raw Ty Op)
          | branch(condition : Nat, yes : Raw Ty Op, no : Raw Ty Op)
          | iterate(count : Nat, accumulator : Ty, initial : Nat,
                    body : Raw Ty Op, next : Raw Ty Op)
```

The descriptors already belong to the selected vocabulary. Decoding external
bytes and resolving untrusted descriptors to that vocabulary are separate
profile obligations.

Assume decidable equality of sorts. A raw index forms a `Var Γ τ` exactly when
that index exists in `Γ` and its sort is `τ`. An operand list forms exactly when
it has the required length and each position forms at the corresponding sort.
An invalid index or wrong sort is `invalidOperand(index, expectedSort)`; an
arity mismatch is `operandCount(expectedRemaining, actualRemaining)` for the
unmatched list suffix. Matching operands are processed from the head, so an
earlier invalid operand can fail before a later arity mismatch is reached.

Elaboration under `Γ` and result sort `τ` applies the typed constructor rules
recursively. It checks an operation's operands before its continuation; a
branch's condition, then its yes and no arms; and a loop's initial accumulator,
body, then suffix. No invalid branch or zero-count body is admitted by skipping
its formation. Formation supplies no default value or cross-sort cast.

Erasure replaces typed references by their indices, preserving every operation,
argument position, branch, loop count and accumulator sort. It satisfies:

```text
elaborate Γ τ (erase p) = ok p       for every Γ ⊢ p : τ.
```

Successful formation establishes typed control. It does not bind runtime inputs,
authenticate operation meanings, prove input locality or establish domain laws.

## Structural call bounds

Given `b : L.Op → Nat`, define:

```text
B(ret v)              = 0
B(stop r)             = 0
B(letOp o args q)     = b(o) + B(q)
B(branch c p q)       = max(B(p), B(q))
B(iterate n a p q)    = n * B(p) + B(q)
```

If, for every operation `o` and every typed argument list `args`,
`Within (b o) (M.operation o args)`, then for every program and environment:

```text
Within (B p) (⟦p⟧M η).
```

`Within` is the common [uniform call bound](../core/execution.md#uniform-call-bounds).
The bound includes an actual invocation that stops. It counts interface calls,
not handler arithmetic, allocations, native instructions or cryptographic
oracle queries without an additional cost correspondence.

Public endpoint admission separately binds counts and bounds to admitted public
parameters. A `Nat`-typed count is not evidence of its public provenance.
Typing and a structural call bound also do not establish
[phase admission](interaction.md#endpoint-admission).

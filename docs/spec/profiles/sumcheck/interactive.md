# Interactive Sumcheck

This profile combines the [quadratic object](quadratic.md#quadratic-coefficient-objects)
with the [message and interaction](scalar-rounds.md#messages-and-logical-rounds) definitions.
Its normal result is a Boolean from evaluation of the original bound polynomial.

The source and operational definitions use a commutative semiring `F` with
decidable equality. The table compiler and probability sections state their
additional ring or finite-field requirements at the corresponding boundary.

## Complete verifier source

For a fixed polynomial dimension `n`, the complete source retains:

```text
Accumulator F = { claim : F, challenges : List F }
advance(m,r,a) = (evaluate(m,r), a.challenges ++ [r])
terminal(p,a)  = (length(a.challenges)=n) ∧
                 (a.claim=eval(p,coordinates(n,a.challenges))).
```

The terminal expression returns a Boolean using decidable equality. The
[coordinate-list interpretation](../../domains/polynomials.md#coordinate-list-admission)
is total with its stated fallback; terminal acceptance additionally requires
the exact length `n`. A short or long forged point cannot use that fallback
to pass the arity condition.

The typed source vocabulary is:

| Operation | Ordered arguments | Result | Meaning |
|---|---|---|---|
| `receive` | none | message | Logical message call |
| `draw` | none | scalar | Logical challenge call |
| `check` | message, accumulator | boolean | Message boundary equals the current claim |
| `advance` | message, scalar, accumulator | accumulator | Evaluate and append the actual challenge |
| `reject` | none | unit | Logical rejection notification |
| `terminal` | polynomial, accumulator | boolean | The exact terminal predicate above |

The six sorts are `accumulator`, `polynomial`, `message`, `scalar`, `boolean`
and `unit`; their values are the displayed types, `Quadratic F n`, and the
ordinary Boolean/unit types. The condition interpretation is the Boolean value
itself. The source input context is ordered `[accumulator, polynomial]`.

The program repeats this body `count` times, carrying the accumulator:

```text
m := receive()
if check(m,accumulator) then
  r := draw()
  return advance(m,r,accumulator)
else
  reject()
  stop reject.
```

After iteration, it returns `terminal(originalPolynomial,accumulator)`, using
the polynomial retained from the actual input context. It does not replace
that input with a caller-supplied final oracle value. The source's denotation
is the corresponding accumulator round process followed by this pure terminal
operation. It conforms to the logical interaction, has call bound `2*count`,
and returns only in `finished`, for every typed initial accumulator and
polynomial. These formation statements do not require the terminal Boolean
to be true.

The complete entry fixes `count=n` and initial accumulator `(claim,[])`.
Residual-polynomial restriction is used in its mathematical proof; this source
instead retains the original polynomial and evaluates it at the completed
ordered point. The dense logical evaluation does not prescribe an efficient
native terminal algorithm or a polynomial-commitment opening protocol.

## Interactive execution and failure

Let `F` be a commutative semiring with decidable equality. Fix callbacks:

```text
send  : S → Message F × S
react : S → F → S.
```

The actual runtime state is `(prover : S, coins : List F)`. The direct logical
handler is:

```text
message at (s,coins):
  let (m,t)=send(s)
  return (returned m, (t,coins), [message m])

challenge at (s,[]):
  return (stopped exhausted, (s,[]), [])
challenge at (s,r::tail):
  return (returned r, (react(s,r),tail), [challenge r])

reject at state:
  return (returned (), state, [reject]).
```

The staged fresh construction expands a logical message to `receive`, a
challenge to `sample`, and rejection to `reject`. Its provider transition is
`[] ↦ (stopped exhausted,[])` and `r::tail ↦ (returned r,tail)`. The constructed
handler agrees exactly with the direct handler above.

Define `run(send,react,p,claim,s,coins)` as execution of the actual complete
entry through this staged construction. It returns `Execution (S×List F) Event Bool`.
The event vocabulary includes message, challenge, query and reject; this fresh
entry emits no query events. A boundary rejection preserves the post-send
prover state, leaves the next challenge unconsumed, emits message then reject,
and stops. An exhausted draw preserves the earlier message and post-send state.
A passed final arity/evaluation check returns `true`; a failed final check
returns `false`, with no terminal notification event. Extra provider coins
remain in residual state. At zero dimensions no round executes, but the entry
still compares the claim with the actual constant polynomial.

## Supplied local endpoints

The same complete entry can execute supplied prover and verifier steps through
the [named role-store profile](../source/named-inputs.md#typed-role-stores). Fix the
same `send`, `react`, polynomial and domain meanings as above. Each local step
has the following ordered input declarations; every entry is an invocation
argument, with its indicated owner and type.

| Local step | Ordered inputs | Returned value |
|---|---|---|
| Prover send | `memory : S`, private to prover | `send(memory) : Message F × S` |
| Prover react | `memory : S`, private to prover; `challenge : F`, shared | `react(memory,challenge) : S` |
| Verifier check | `message : Message F`, shared; `accumulator`, private to verifier | `decide(boundary(message)=accumulator.claim) : Bool` |
| Verifier advance | `message : Message F`, shared; `challenge : F`, shared; `accumulator`, private to verifier | `advance(message,challenge,accumulator)` |
| Verifier terminal | `statement : Quadratic F n`, shared; `accumulator`, private to verifier | `terminal(statement,accumulator)` |

Here the accumulator has the [complete-source type](#complete-verifier-source).
Each program applies its named operation to those ordered operands and returns
the result. These operations are pure local computations: their runtime state
is unit and their event list is empty. Prover memory and verifier accumulator
are explicit input/output data. The verifier's local interpretation refuses
communication operations; the five programs contain none. Missing or inaccessible
inputs fail common input resolution before that step executes.

The supplied binding fills precisely the declared slots for the executing role.
Other roles' private stores and hidden provider state are absent from the
resolved environment. Equal permitted role views give equal local runs for
the same fixed meaning. This does not certify hidden captures of arbitrary
native callback code or permit selection of `send` after reading future coins.

Executing the five programs under these bindings yields the displayed values,
so extracting their returned values needs no fallback. A synchronous driver
uses the resulting send/react functions in the actual handler and replaces the
complete source's check, advance and terminal operations by the corresponding
bound local steps. It delivers the actual received message and drawn challenge
to the next applicable step. The resulting complete execution equals the entry
above, including stops, residual prover/provider state, and ordered events.
The same substitution preserves the [framed entry](framing.md#complete-statement-root-and-framed-execution)
under the identical query provider and initial frame state.

For the fresh interactive entry, complete equality gives the same acceptance
event and [probability bound](#honest-execution-and-interactive-soundness) under
its existing premises. These are supplied local sources with this driver; they
do not define automatic endpoint projection, asynchronous delivery or progress
for another transport.

## Adaptive strategy and terminal equivalence

The mathematical prover strategy is an indexed finite tree:

```text
Strategy F 0     = done
Strategy F (k+1) = send(m : Message F, next : F → Strategy F k).
```

The message is selected before that round's challenge. The continuation can
depend arbitrarily on the delivered challenge. The callback strategy is:

```text
strategy(0,s) = done
strategy(k+1,s) =
  let (m,t)=send(s)
  in send(m, r ↦ strategy(k,react(t,r))).
```

For the complete tape type `Tape F 0 = Unit`, `Tape F (k+1) = F × Tape F k`,
define the reference verifier:

```text
verify(constant c, claim, done, ()) = (claim=c)
verify(p,claim,send(m,next),(r,tail)) =
  if boundary(m)=claim then
    verify(restrict(p,r),evaluate(m,r),next(r),tail)
  else false.
```

Its Boolean result is distinct from the complete execution record. Define
`finalClaim` by the same recursion without the polynomial or terminal check:
at zero rounds it returns `some claim`; on a failed boundary it returns `none`;
otherwise it continues with `evaluate(m,r)`. Let `tapePoint` and `tapeList`
preserve the tape's coordinate order. Then:

```text
verify(p,s,a,tape)=true ↔
  finalClaim(a,s,tape)=some(eval(p,tapePoint(tape)))

run(send,react,p,s,prover,tapeList(tape)).outcome = returned true ↔
  verify(p,s,strategy(n,prover),tape)=true.
```

These equivalences use exactly `n` challenges in the typed tape. The operational
run and its transformation laws also apply to arbitrary shorter or longer
lists, preserving their actual stops and residuals.

## Residual connection and prepared evaluation

The complete source can be understood as a round producer connected to a
direct evaluator. For a fixed actual input `(n,p,claim,prover,tape)`, expose
`Residual = { point : Fin n → F, value : F }`. The producer requires:

```text
residual.point = tapePoint(tape)
runRounds(n,claim,prover,tape).outcome =
  returned { claim = residual.value, challenges = tapeList(tape) }.
```

The evaluator checks `residual.value = eval(p,residual.point)` using the original
input polynomial. Its boundary is connected to the producer's boundary by
equality of the **whole residual**, including point and value. Existence of
compatible accepted boundaries is equivalent to the complete source accepting.
Each component separately satisfies acceptance-and-output realization: the
round constraints use `finalClaim`, justified by the actual round execution;
the evaluator constraints use the same original object and exposed point.
The common [connection law](../../realization/representations.md#acceptance-and-output-realization)
therefore applies without hiding the two boundaries independently.

This reference covers every typed tape admitted by the source. Honest
completeness does not restrict challenges to Boolean coordinates. It is direct
evaluation, not a succinct polynomial-commitment opening. Input-specific
realization also does not establish an interactive probability law; challenge
generation remains governed by the selected experiment or construction.

An optional prepared interpretation replaces `advance`'s evaluation by
immutable preparation with complete key `(message, delivered challenge)` and
value `evaluate(message,challenge)`. That actual returned value becomes the
next claim; the same challenge is appended to the accumulator. Other operations
use the selected construction as external calls. Under a valid cache, either
direct or memoized preparation preserves the original source's complete outcome,
external state and ordered protocol events after removing accounting records.
This holds for every well-typed body in the vocabulary and every selected
construction/handler, including stopped challenge queries.

The cache can therefore be private to this optimization while the original
polynomial, transcript and challenge-provider state retain their meanings.
Reuse requires an actual repeated key; correctness gives no profitability or
native performance claim. The direct residual connection also applies to the
prepared Fresh execution through its source-execution correspondence.

## Honest execution and interactive soundness

For `p=node(a,b,c)`, the honest round message is
`(booleanSum(a),booleanSum(b),booleanSum(c))`. Its boundary is `booleanSum(p)`
and its evaluation at `r` is `booleanSum(restrict(p,r))`. The honest strategy
recursively sends this message and continues with the restricted polynomial.

The honest callback state is the dependent pair `(k,q : Quadratic F k)`.
At positive `k`, `honestSend` returns the honest round message and unchanged
state, and `honestReact` decrements `k` while restricting `q` at the delivered
challenge. At zero it returns a zero message if called and leaves state
unchanged; the zero-round verifier never makes that call. The initial state
for polynomial `p` is `(n,p)`. With initial claim `booleanSum(p)`, honest
execution accepts for every complete tape over a commutative semiring with
decidable equality.

For probability, additionally let `F` be a finite field. Its cardinality is
nonzero. Fix `p`, `claim`, `send`, `react` and initial `prover` independently
of the verifier tape. Each of the `n` tape coordinates is independent and
uniform over all of `F`. Define:

```text
sourceAcceptance(send,react,p,claim,prover) =
  (1 / |F|^n) * Σtape [
    run(send,react,p,claim,prover,tapeList(tape)).outcome = returned true ].
```

The sum is over all complete tapes, and its arithmetic is rational. It agrees
with the recursive uniform average and the reference verifier's acceptance
probability. No message-honesty predicate restricts the adversarial callbacks.
For every such callback pair and private initial state:

```text
claim ≠ booleanSum(p) → sourceAcceptance ≤ 2*n/|F|.
```

The honest callbacks with claim `booleanSum(p)` and initial state `(n,p)` have
acceptance probability one. At `n=0`, a false constant claim has acceptance
probability zero. The upper bound is valid even when it exceeds one, in which
case it is uninformative.

The round argument uses the nonzero difference between the received message
polynomial and the honest round polynomial when their boundary sums differ.
That difference has degree at most two and at most two roots over a field.
A false claim either causes immediate rejection or can become a true residual
claim only on those collision challenges; the remaining false-residual branch
continues the induction. Here nonzeroness follows from the differing boundary
sums; unequal coefficient vectors do not imply unequal field functions.
In the field of order two,
for example, `x+x²` vanishes on both field elements but has the same boundary
as the zero polynomial, so it does not contradict the false-boundary argument.

The separate private-seed mixture fixes a finite nonempty seed type, a map
`privateState : Seed → S`, and the callbacks and statement. A uniform seed is
sampled independently of the verifier tape, and the same bound applies to the
average of `sourceAcceptance(...,privateState(seed))`. A correlated future-tape
seed or adaptive statement selection needs its own enclosing experiment law.

## Checked evaluation and table-bound entry

The checked arithmetic child has ordered scalar inputs `(a,b,c,r)`. Its source
computes `a+(b*r+c*(r*r))`; its supplied candidate computes
`a+(b+c*r)*r`. The semiring Horner rule checks that actual source and candidate
and produces the plan consumed by the parent. The plan's complete execution
returns `evaluate(m,r)` with unit state and no events when its inputs are
the actual received coefficients and delivered challenge.

The parent uses this checked plan in `advance`, then appends the same actual
challenge. Its interpretation retains an explicit stopped-child branch, though
the checked pure child's law proves that branch unreachable for these inputs.
All other parent operations retain their meanings. The optimized denotation
equals the original for every well-typed source of this vocabulary and actual
environment. Thus its complete run agrees under any common handler or
construction, and the interactive acceptance theorem uses the same adversary
callbacks and initialization.

For actual flat `values` and occurrence `source`, define the table entry:

```text
tableRun(values,source,send,react,claim,prover,coins) =
  match compile(inputTables(values),source) with
  | none   → (stopped refused, (prover,coins), [])
  | some p → optimizedRun(send,react,p,claim,prover,coins).
```

Unsupported factor arity refuses before interaction or coin consumption.
Successful compilation gives complete equality with `run` for its actual
compiled `p`, including short or extra tapes. On a complete tape, acceptance
is equivalent to:

```text
finalClaim(strategy(n,prover),claim,tape) =
  some(evalExpression(inputTables(values),tapePoint(tape),source)).
```

For the finite-field independent-tape experiment and actual compiler success,
the false premise is the original one:

```text
claim ≠ expressionSum(inputTables(values),source)
  → Pr[tableRun returns true] ≤ 2*n/|F|.
```

The honest callbacks initialized with the actual compiled polynomial and that
original sum have perfect completeness. These claims bind the same table
cells, axis order, factor multiplicity, source, compilation result and terminal
point. They establish neither a native decoding theorem nor knowledge, zero
knowledge, a polynomial-commitment terminal, a larger degree profile or
Fiat–Shamir security.

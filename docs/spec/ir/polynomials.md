# Polynomial recipes with runtime arity

This profile complements [static polynomial SSA](mathematics.md).
It retains a finite formal expression while its factor tables change arity under
[iteration](iteration.md). Static `!poly.polynomial<F,n>` keeps its
existing meaning; no dynamic type mutation or ambient padding is introduced.

## Recipe and degree

`poly.recipe @name` is an isolated symbol with one block of 1–16 same-field
factor slots, a `degree` integer in `[0,16]`, and `poly.recipe_yield`.
The expression has at most 128 operations, each a field constant, addition,
subtraction or multiplication. Operands must refer to earlier results or slots.
All intermediates have conservative degree at most 16. The yielded expression's
derived degree must be at most the declared degree. Constants have degree zero,
slots degree one, addition/subtraction take the maximum, and multiplication adds.
Dead operations count toward these formation/work limits.

The declared degree is an ABI bound: simplification may lower the expression's
derived degree without changing the message width. Coefficients are zero padded
to `degree + 1`. The body denotes a **formal ring expression** `R`; substitution
into an F-algebra defines its meaning. Rewrites must preserve formal polynomial
meaning, not merely equality as functions on a particular finite field.
Inverses, comparisons, calls and control are permanently excluded from this
ring-template contract. Execution uses the same ring expression specialized to
scalars or coefficient polynomials; it is not an arbitrary executable callback.

## State and mathematical meaning

For factor tables `T1,...,Tk` of equal runtime arity `n`, define

```text
P(X0,...,X(n-1)) = R(MLE(T1)(X), ..., MLE(Tk)(X)).
```

`MLE` uses logical high-bit-first Boolean order. Products are products of the
factor MLEs; they are not MLEs of pointwise products. An implementation must
preserve shared factors and this distinction away from the Boolean cube.

The state is an ordinary single-alternative nominal variant containing
`(point, T1, ..., Tk)`, with descriptor name `poly.residual.<recipe-name>` and
alternative `state`. Its type is uniform for all arities. The current executable
installation is BLS12-381 Fr only. The nominal name is ABI identity; renaming a
recipe requires rewriting its state descriptors and signatures together.

This state provides **no origin attestation**. Its descriptor can be constructed
by ordinary aggregate operations. Generated routines check current shape, not
honest derivation from an original subject. For an honest sequence starting with
arity `n0`, the invariant is `len(point) + n = n0`, and each `Ti` is its original
table fixed at that prefix. No routine certifies that historical invariant.
A verifier must check against its own original subjects or a separately checked
opening relation. Prover-produced state, rounds and terminal values do not
acquire verifier trust from their types. Tables have no native message codec in
this profile; state sharing is not a witness-confidentiality theorem.

## Checked realizations

`poly.realize` declares a symbol, recipe reference, kind and exact function type.
Preparation validates the whole original module, then expands declarations into
scoped `func.func` bodies and runtime bindings before application expansion.
Each function borrows `!runtime.scope` and returns an `!exec.outcome` whose
payload is the declared data result. Primitive invocations use `exec.apply`;
explicit dispatch preserves their success and stopped paths. Ordinary helper
returns package the payload, while outlined control bodies use charged
`exec.complete`.
All compile-time recipes are erased, including unused ones. Every invocation is
an ordered `protocol.local_call`; its checks, work and failures are observable.
Symbol-use verification and defensive signature derivation reject malformed
siblings without assuming verification order.

| Kind | Signature | Required meaning/checks |
|---|---|---|
| `init` | `(ui64, table^k) → state` | All factor arities equal the supplied count; prefix is empty |
| `arity` | `state → ui64` | Check equal factor arities and return the current arity |
| `round` | `state → !data.field_array<"F", degree+1>` | Require positive common arity; return coefficients of `sum_y P(X,y)` |
| `bind` | `(state,F) → state` | Require positive common arity; fold every factor at the same scalar and append it to the prefix |
| `finish` | `state → (point,F)` | Require arity zero; evaluate `R` on singleton factor values |
| `evaluate` | `(point,table^k) → F` | Check equal arities and `len(point) = arity`; return `R(T1(point),...,Tk(point))` |

`round` emits one bounded scoped loop over the suffix cube. Each slot contributes
`[T[i], T[i+half]-T[i]]`; the ring expression combines coefficient arrays by
addition/subtraction/convolution, then sums them over rows. The high-half pairing,
`poly.fold`, prefix append and evaluation share logical axis order. Generated
`exec.range` and its checked CF structure forward immutable captures to an
outlined function and carry the coefficient accumulators through each iteration.
`poly.table_arity` observes a concrete table's arity; it is independent of storage
layout. Expansion is bounded before construction to 100000 work units,
including slot-dependent shape checks, intermediate coefficient widths, and a
conservative allowance for scoped outcome and control-flow construction.
Separate later compiler/runtime budgets still apply. Stored code size depends
on recipe size/degree, not runtime table length or round count.

Shape and endpoint checks invoke `control.require` through `exec.apply`; failure is a
local backend stop. The direct Sumcheck clients additionally guard the received
count against the verifier's own original table arity before entering rounds.
Verifier claims are updated from actual received coefficients and its actual
draws, and terminal evaluation uses its original subjects.

## Assurance and extension boundary

Independent numerical checks cover degree-two and degree-three recipes,
asymmetric factor tables, zero/one/multiple rounds and changed incoming data.
They do not prove the expansion for all recipes or Sumcheck soundness.
The recipe realization checker reads the actual scoped CFG independently of the
producer, then compares its ordered primitives, actual operands, shape guards,
coefficient convolution, captures and returns against the source recipe. Every
generated outlined body and binding must be consumed by this comparison;
retained declarations must be unchanged. This native correspondence check is
distinct from the fixed-arity polynomial checker and from a Lean proof or a
Sumcheck security theorem. Adding an execution strategy such as
point evaluation followed by interpolation must preserve this same recipe and
its declared degree, rather than introducing a second mathematical model.

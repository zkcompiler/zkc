# Pure expressions and captures

This profile defines a homogeneous ring expression language and immutable
closures with explicit captures. Scope checking, available input values and
successful issuance are separate predicates. The common
[typed language](../../language/programs.md) can contain other sorts and effects.

## Positional inputs

For a value type `F`, role type `Role` with decidable equality, and hidden-state
type `H`, the positional reader has:

```text
Slot Role = shared Nat | owned Role Nat
World = (publicInputs : Nat → Option F,
         privateInputs : Role → Nat → Option F,
         hidden : H)

permitted ρ (shared i)  = True
permitted ρ (owned r i) = (r = ρ)

read ρ w (shared i)  = w.publicInputs i
read ρ w (owned r i) = if r = ρ then w.privateInputs ρ i else none
env ρ bindings w i  = (bindings[i]?).bind (read ρ w).
```

`bindings : List (Slot Role)` fixes the order of source inputs. Position `i`
is an index into that list, not necessarily the underlying slot number.
Repeated bindings are permitted. A missing list position, absent value or
foreign owner's slot produces `none`; this reader does not distinguish their
diagnostics. None of them becomes a present zero. A successful read implies
that the slot is permitted.

The permitted-view relation is:

```text
SameView ρ w v ⇔
  w.publicInputs = v.publicInputs ∧
  w.privateInputs ρ = v.privateInputs ρ.
```

It equates availability and values for shared and actor-private inputs. It
does not equate hidden state or other actors' private values. Equal permitted
views give equal reads at every slot and equal positional environments for
the same binding list.

## Expression syntax and meaning

For variable type `A`, define:

```text
Expr A = var(a : A) | lit(n : Nat)
       | add(Expr A, Expr A) | mul(Expr A, Expr A) | sub(Expr A, Expr A)
       | ifz(Expr A, Expr A, Expr A).
```

Select a ring `F` with decidable equality and environment `η : A → F`.
Multiplication need not be commutative. Evaluation is total:

```text
eval η (var a)     = η a
eval η (lit n)     = the natural numeral n in F
eval η (add x y)   = eval η x + eval η y
eval η (mul x y)   = eval η x * eval η y
eval η (sub x y)   = eval η x - eval η y
eval η (ifz c x y) = if eval η c = 0 then eval η x else eval η y.
```

Literals are part of the fixed source. This syntax supplies no network read,
random draw, mutable storage access or host callback. A source generator that
chooses literals from secrets needs its own
[source-selection and release law](../../language/inputs.md#source-selection-and-release).

## Dependencies and scope

Dependencies are an ordered list of variable occurrences:

```text
deps(var a)         = [a]
deps(lit n)         = []
deps(add x y)       = deps(x) ++ deps(y)
deps(mul x y)       = deps(x) ++ deps(y)
deps(sub x y)       = deps(x) ++ deps(y)
deps(ifz c x y)     = deps(c) ++ deps(x) ++ deps(y)

Allowed scope e ⇔ ∀ a ∈ deps(e), a ∈ scope.
```

For decidable equality of `A`, the Boolean checker evaluates this membership
condition for every listed occurrence. It succeeds exactly when `Allowed`
holds. Lists can contain duplicates; the predicate requires membership, not
uniqueness. The summary includes both arms of every zero test, even when a
guard is a known literal. It is a sufficient syntactic dependency summary,
not the minimal mathematical support of the expression.

For any two total environments `η, θ : A → F`:

```text
(∀ a ∈ deps(e), η a = θ a) → eval η e = eval θ e.
```

Consequently a checked expression has equal values in environments that agree
on its scope. This statement presupposes total values for evaluation; a scope
certificate does not supply an absent input.

## Substitution and intrinsic scope

For `σ : A → Expr B`, substitution replaces `var a` by `σ a`, retains each
literal, and acts recursively on every child of arithmetic and zero-test
constructors. Its evaluation law is:

```text
eval η (e.bind σ) = eval (fun a => eval η (σ a)) e.
```

Define intrinsic scoped syntax and its erasure by:

```text
Scoped scope = Expr {a : A | a ∈ scope}
erase e      = e.bind (fun a => var a.value).
```

Given `Allowed scope e`, restriction attaches that membership evidence to
every variable, preserving every constructor. Its erasure is exactly `e`.
Every erased scoped expression is allowed. Thus:

```text
check scope e = true ⇔ ∃ t : Scoped scope, erase t = e
eval η (erase t)     = eval (fun a => η a.value) t.
```

These laws preserve syntax and meaning of this expression fragment. They do
not infer availability, ownership, or preservation of unrelated compiler
annotations.

## Finite closures

A closure over `A` consists of:

```text
size     : Nat
body     : Expr (Fin size)
captures : Fin size → Expr A

expand c = c.body.bind c.captures.
```

The capture function represents a finite indexed collection of syntax. Capture
positions are distinct, ordered positions even when expressions repeat. A
zero-capture closure has no variable in its body but can contain literals and
arithmetic. Expansion has the substitution meaning:

```text
eval η (expand c) = eval (fun i => eval η (c.captures i)) c.body.
```

Checking only the expanded expression justifies a value-agreement law at that
expanded expression's dependencies. Whole-capture issuance below retains the
obligations of every declared capture, including captures the body never uses.

## Whole-capture readiness

For positional variables, let `Env F = Nat → Option F`. Define:

```text
captureDeps c = concat [deps(c.captures 0), …, deps(c.captures (size - 1))]
ready scope η ds = all i in ds: (i ∈ scope and η i is some value).
```

The displayed capture list is empty at size zero. It enumerates indices in
increasing order and retains dependency multiplicity. Readiness succeeds
exactly when every listed index is in scope and has a present value. It is
true for an empty dependency list. Agreement of partial environments on the
scope preserves both successful and failed readiness.

*Example (informative).* A closure with constant body `lit 7` and one capture `var 1`
requires input `1` to be available and in scope, although its expanded body is
constant. An unavailable variable in a dormant branch inside that capture also
causes refusal. Removing such a capture before checking changes this profile's
admission behavior.

## Issuance and actor admission

An issued code/value pair is:

```text
Bound n F = (body : Expr (Fin n), values : Fin n → F)
total η i = (η i).getD 0
capture c η = (c.body, fun i => eval (total η) (c.captures i))

issue scope η c =
  if ready scope η (captureDeps c)
  then some (capture c η)
  else none.
```

The raw `capture` function has specified totalized behavior. Admission is the
guarded `issue` function. On successful issuance, every dependency of every
capture has a present value, so each capture evaluates identically with any
other fallback in place of zero. This law does not admit an unavailable read.
Success fixes the actual source body and every actual capture value; a manually
constructed `Bound` record does not establish the issuance equation.

Actor admission supplies the positional reader and its valid indices:

```text
admit ρ bindings w c =
  issue (range (length bindings)) (env ρ bindings w) c.
```

For each declared dependency, successful admission implies that its binding
exists, its owner is permitted and its actual read is present. Other unused
binding-list entries need not be available. For fixed `ρ`, `bindings` and `c`,
`SameView ρ w v` gives equality of the entire admission result: either the
same issued code/value pair or `none` in both worlds.

## Invocation and elaboration

Invocation of `b : Bound n F` is `value b = eval b.values b.body`. It reads
only the retained body and values. For `issue scope η c = some b`:

```text
value b = eval (total η) (expand c).
```

Elaboration into any operation signature is `elaborate b = done (value b)`.
It has zero interface calls, conforms at every entry phase and returns that
value at the unchanged phase. For any fixed continuation `k : F → Proc Σ A`,
handler `h` and initial state `s`:

```text
run h ((elaborate b).bind k) s = run h (k (eval (total η) (expand c))) s.
```

This includes stopped continuation outcomes and their actual state and events.
The continuation is supplied semantic context, not an additional serialized
closure constructor. Comparing invocations under related handlers additionally
requires the common handler relation and related initial states; input-view
agreement alone does not equate different runtime states.

Native captures obey the common [lifetime contract](../../language/inputs.md#capture-lifetime).
An issued immutable value does not follow later environment mutation. A live
reference needs its own interpretation. Neither issuance nor invocation
creates authenticity, publication permission or one-use authority.

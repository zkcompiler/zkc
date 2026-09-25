# Relations and terminal verification

A relation describes the mathematical statement being established. A protocol
reduction connects actual statement instances, and a terminal contract connects
the final decision to the residual instance. These contracts have a different
subject from equality of [program executions](../verification/refinement.md).

## Relation families and instances

A relation family consists of:

```text
Family = {
  Statement : Type,
  Witness   : Type,
  holds     : Statement → Witness → Prop
}

Valid(F,x) := ∃ w : F.Witness, F.holds x w.
```

A public parameter may select a family; the selected parameter and its
interpretation are fixed when using `Valid`. A statement instance is an actual
value of that selected `Statement` type. A relation-bearing reduction binds its
input and returned residual instances to the source, actual ordered inputs and
domain/setup dependencies it uses. Ordered axes, challenge prefixes and
polynomial occurrences are part of this binding where the relation depends on
them. A scalar or same-typed handle does not reconstruct omitted bindings.

An ordinary arithmetic computation can have no witness relation. Giving every
arithmetic value a reduction wrapper is not required. Conversely, naming an
object a claim does not establish the correspondence between that object and
the intended mathematical statement.

## Source encoding adequacy

An external representation may reorder public values and add auxiliary witness
coordinates. Fix source and target families `S,T`, a statement map `f`, and a
witness correspondence `C(s,w,z)`. An adequate encoding supplies both laws:

```text
S.holds(s,w) → ∃ z, T.holds(f(s),z) ∧ C(s,w,z)
T.holds(f(s),z) → ∃ w, S.holds(s,w) ∧ C(s,w,z).
```

The second law quantifies over every satisfying target assignment, including
assignments an honest witness generator never emits. Together they imply
`Valid(S,s) ↔ Valid(T,f(s))`. Auxiliary values need not be unique, and witness
recovery need not be executable. An importer claiming stronger knowledge or
efficient extraction properties must state those additional requirements.

Composition uses the actual composed statement map and an existential related
intermediate witness. A target protocol's reduction and terminal acceptance can
then establish source validity with the same exceptional event; encoding
adequacy does not bound that event's probability or prove the target protocol.
These laws are implemented by
[`Zkc.Relation.Encoding`](../../../formal/Zkc/Relation/Encoding.lean).

An operation whitelist, successful export, hash equality or honest-witness test
alone does not construct such an encoding. Artifact-specific equation comparison
and differential testing provide evidence at their stated scope. The
[constraint views](../domains/constraints.md) define the imported mathematical
objects independently of any frontend's preservation claim.

## Component connections

Fix component boundary types `A, B`, predicates `left : A → Prop` and
`right : B → Prop`, and a connector `connect : A → B → Prop`. Define:

```text
Connected(left,connect,right) :=
  ∃ a b, left(a) ∧ connect(a,b) ∧ right(b).
```

The predicates retain their actual statement, configuration and domain
parameters. A component predicate can hide its local relation witness using
`Valid`; a boundary used by another component remains free until connection.
A connector over shared events
[carries the order in which they happened](../../rationale/connection-ordering.md).
Different components need not expose the same tuple or storage layout. For
example, a proof can expose a key and commitment, a signature a key and message,
and the connector relate their keys. Each component still binds its other
arguments to the selected statement.

Pointwise equivalence of `left` with `left'` and `right` with `right'` preserves
`Connected` for every connector on those boundary types. Equivalence of their
separately closed existential predicates is insufficient: each may be inhabited
only at incompatible boundary values.

A replacement in a selected context can use weaker, conditional premises:

```text
∀ a b, connect(a,b) → right(b) → (left(a) ↔ left'(a))
∀ a b, connect(a,b) → left'(a) → (right(b) ↔ right'(b))
─────────────────────────────────────────────────────────────
Connected(left,connect,right) ↔ Connected(left',connect,right').
```

The second premise uses the already-replaced `left'`. Thus one component may
remove a range check enforced by its connected component, but both cannot remove
it by each relying on the other's old check. This law preserves the combined
relation in that context; it does not make either replacement valid in every
other caller, or preserve native stopping and event order by itself.

### Changing boundary representations

For target types `U, V`, let `L : A → U → Prop` and `R : B → V → Prop` be
representation relations. A sufficient connection law requires:

```text
left(a)  → ∃ u, L(a,u)
right(b) → ∃ v, R(b,v)
targetLeft(u)  ↔ ∃ a, left(a) ∧ L(a,u)
targetRight(v) ↔ ∃ b, right(b) ∧ R(b,v)
left(a) ∧ right(b) ∧ L(a,u) ∧ R(b,v) →
  (targetConnect(u,v) ↔ connect(a,b)).
```

These premises imply equivalence of the source and target connections. Coverage
concerns valid source boundaries; neither relation must be globally bijective
or functional. Exact images without coverage permit an empty target for an
inhabited source and do not suffice. Executable encoders supply actual maps and
their laws rather than obtaining code from this existential theorem. Multiple
representations of one boundary are allowed, but connector compatibility must
hold for each admitted representation. Conversely, source boundaries related
to the same target value cannot be distinguished by a compatible connector
against the same represented partner. No global injectivity is required.

These laws are implemented in
[`PIR.Relation.Connected`](../../../formal/Zkc/Semantics/RelationComposition.lean).
They concern logical relation composition. Protocol completeness, knowledge,
zero knowledge and shared-randomness security require their separately selected
experiments and hypotheses.

## Soundness-direction reduction

Let `S` and `R` be input and residual types, `input : S → Prop` and
`residual : R → Prop` their predicates, `s : S` the actual source instance,
`r : R` the actual returned residual, and `bad : Prop` an explicitly selected
exceptional event of the execution. Define:

```text
ReductionContract(input,residual,s,r,bad) :=
  residual(r) → input(s) ∨ bad.
```

The predicates can be validity in specified relation families or other
explicit mathematical predicates. The contract is an implication for these
actual instances. It does not generate the residual, reconstruct a witness,
assert honest completeness or bound the probability of `bad`.

If the first reduction has residual `r : R` and a second has final result
`t : T`, composition is:

```text
ReductionContract(input,middle,s,r,bad₁)
ReductionContract(middle,last,r,t,bad₂)
────────────────────────────────────────────────────────────
ReductionContract(input,last,s,t,bad₁ ∨ bad₂).
```

Both premises use the same actual `r` and the same predicate `middle`.
Equality of type names or identifiers is insufficient. The rule follows by
applying the second implication and, on its valid-middle branch, the first.
The exceptional events remain a disjunction; any probability estimate uses
their [actual joint experiment](probability.md#attempts-and-extensions).

## Finite obligation derivations

A selected claim type can name the actual propositions of one execution. It must
retain the relation, operands, subject and context needed by its interpretation;
the common semantics does not prescribe a universal claim language or wrapper
for ordinary runtime values.

A finite reduction rule has a list of prerequisites and one conclusion. For a
fixed interpretation `holds` and the rule's exceptional event `bad`, its law is:

```text
(∀ p ∈ rule.prerequisites, holds(p)) → holds(rule.conclusion) ∨ bad(rule).
```

An ordered derivation checker starts with explicitly supplied terminal facts and
adds a conclusion only when every prerequisite is available. It then checks
**all independently supplied source requirements**, rather than deriving the
requirements from the candidate's surviving rules. Missing prerequisites reject
the candidate; an unseeded cycle cannot establish its own premises. Facts are
reusable, and repeated requirements cannot replace a different missing root.

Given sound terminal facts and a sound law for each applied rule, successful
checking implies that all required propositions hold together or an exceptional
event of an applied rule occurs. The
[`PIR.Obligations`](../../../formal/Zkc/Semantics/Obligations.lean) reference
proves this implication and packages it as the existing `ReductionContract`.
Its sequencing law uses the actual available facts returned by the first segment.

An accepted finite derivation remains accepted when one substitution is applied
consistently to its requirements, terminals and every rule. This is the forward
instantiation law (`Rule.map`, `derive_map`, `check_map`). `Rule.Sound.map`
transports a semantic law when its predicate is the target predicate pulled back
through the same map. The substitution need not be injective, but then the
converse does not follow: merging distinct claim
subjects can make an originally unavailable prerequisite appear available.
Semantic validity of the instantiated laws and association with the actual call
remain separate premises; structural instantiation establishes neither.

Structural checking establishes availability, not truth or rule validity. An
empty-premise rule still requires a law. An unresolved exported residual can
enter the fact list only as an explicit assumption. A terminal with an exceptional
event needs its conditional law rather than an unconditional fact. Neither a
claim declaration, a named theorem, nor a body hash establishes correspondence
with actual execution. Compiler integration separately binds requirements,
rules, terminal decisions and any erasure to their source and executed bodies.
This result adds no probability bound, knowledge extraction, zero-knowledge
composition, or universal linear-use discipline.

## Terminal decisions and contracts

For accepted-value type `A`, define the result data:

```text
Terminal A = accepted(a : A) | rejected.
```

This is distinct from an execution outcome. An execution can return either
terminal value or stop with a [stop reason](../core/execution.md#complete-results).
In particular, `returned rejected` and `stopped reject` are different records.
The [accepted-continuation profile](../profiles/services/accepted-continuations.md#verifier-decisions-and-ordinary-composition)
specifies the adapter that turns a returned rejection into a stopping combined
execution.

For `verify : R → Terminal A`, define:

```text
TerminalContract(residual,verify) :=
  ∀ r a, verify(r) = accepted(a) → residual(r).
```

The contract fixes the actual terminal function. Together with the reduction
contract and an actual acceptance, it gives:

```text
ReductionContract(input,residual,s,r,bad)
TerminalContract(residual,verify)
verify(r) = accepted(a)
────────────────────────────────────────────
input(s) ∨ bad.
```

For an effectful terminal consumer, the selected experiment connects its actual
accepting execution to this predicate, or states the corresponding implication
over its complete results directly. Merely possessing an unrelated pure
`verify` function does not connect the consumer to it. Return-phase completion
and the `accepted` constructor alone supply neither implication.

## Scalar terminal

For a value type `F` with decidable equality and a fixed target `t : F`, define:

```text
scalarTerminal(t,a) =
  if a = t then accepted(()) else rejected.
```

This function satisfies `TerminalContract(a ↦ a=t, scalarTerminal(t))`.
It uses equality only; no field structure is required. A caller reducing to
this scalar must bind the actual target and residual and establish the
corresponding reduction contract. Finishing a round sequence with scalar `a`
does not establish `a=t`.

## From reduction to a probability claim

Let `Ω` be the complete sample type of one experiment with normalized law `p`.
Let `source : Ω → S`, `result : Ω → R`, and `accept,bad : Ω → Prop` denote
its actual instances and events. Suppose, for every sample in `support(p)`:

```text
accept(ω) → residual(result(ω))
residual(result(ω)) → input(source(ω)) ∨ bad(ω).
```

Then the event `accept(ω) ∧ ¬input(source(ω))` is contained, on that support,
in `bad(ω)`. Consequently:

```text
Pr[p : accept ∧ ¬input∘source] ≤ Pr[p : bad].
```

For a fixed false source instance this is an acceptance bound. For adaptive
instance selection it bounds acceptance of the actual false selected instance
under the enclosing law; it does not condition on false-instance selection.
The samplewise contract and event inclusion still require a separate bound on
`Pr[p : bad]` for the allowed strategies. This connection supplies no extractor
or honest-prover completeness theorem.

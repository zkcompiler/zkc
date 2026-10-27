# Relations and terminal verification

Native relation declarations, reduction checks and explicit terminal decisions use these obligations.
This chapter states shared laws; a native implementation claim needs its
actual instance and evidence. Independent formal examples retain their own
[model scope](../../lean/docs/README.md).

A relation describes the mathematical statement being established. A protocol
reduction connects actual statement instances, and a terminal contract connects
the final decision to the residual instance. These contracts have a different
subject from equality of [program executions](verification/refinement.md).

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

## Retained subjects and owner boundaries

One checked closed source subject binds bodies and static arguments, logical
schemas, roles, source occurrences, relation declarations, actual selectors and
selected acceptance/completion. The [source interface](formats/entry.md) keeps
that association. A definition's name, dimensions or purpose label alone does
not identify its actual input. Equal-typed public leaves remain ordered.

Formula identity includes its transitive body closure and logical schemas.
Applications retain the actual role-local selectors and output projection.
Masks, scopes, natural versus field count interpretation and selected clauses
remain inputs or parts of the selected definition. Expansion retains the
original declaration and application mapping. Inlining, layout changes,
mutation and specialization invalidate derived views unless an independently
checked transformation reconstructs their correspondence to the same original.
Cached analysis and copied attributes cannot renew that correspondence.

Relation owns the predicate; Constraint owns its assignment domain, equations,
AIR row/boundary scopes or R1CS ONE/public-prefix layout, and projections. An
imported asset has one immutable definition and an explicit predicate
interpretation, rather than a second handwritten formula that may drift.
The existing [constraint contracts](domains/constraints.md) remain authoritative
while their compiler owners are migrated.

An opening claim also binds the actual commitment operand, scheme, setup,
polynomial or table interpretation, coordinates and claimed value. Generic
Data that describes such a claim is unverified. The actual check and final
acceptance must remain connected. Polynomial openings and authenticated-vector
queries have different guarantees; their [polynomial commitment](../../libraries/commitments/kzg/README.md) and
[oracle](domains/oracles.md) contracts determine the interpretation.

### Retention through lowering

Information needed by a selected consumer must remain in its authoritative
subject or in a checked mapping to that subject until the consumer has used it.
It need not be copied onto every lower-level instruction. For example, numerical
lowering may expand a polynomial operation while retaining its ordered axes,
degree and domain in the mathematical definition used for candidate comparison.
A commitment consumer still needs the actual opening instance and its connection
to the selected decision after its arithmetic has been lowered.

Each derived view identifies its source, transformation boundary and applicable
premises. A new body, representation or selector requires rechecking the view;
an analysis cache is valid only for the unchanged inputs on which it depends.
Contextual premises discharged by another component remain premises of that
particular composition. They do not become unconditional laws of the replaced
component.

This requirement does not turn every operation into a security claim. An
ordinary program may compute and ignore a check result; a claim about its
selected acceptance must establish the required connection. Likewise, a source
lookup predicate and a selected randomized lookup argument have different
contracts. Characteristic bounds, compression challenges and denominator
conditions belong to the argument that uses them, rather than all source
membership predicates.

## Exact explicit-table predicates

For a finite ordered table `T` and queries `Q` carrying Boolean `active` flags:

```text
Membership(T,Q) := forall q in Q, q.active implies q.value in T
IndexedRead(T,i,v) := i < length(T) and T[i] = v
```

Positions are exact natural indices in the admitted native index domain.
Duplicates in either input are allowed; membership consumes no multiplicity.
An empty query list is true. An active query against an empty table is false;
an inactive query imposes no value constraint. An out-of-range read is false.
The [table library](../../libraries/relations/table/README.md) supplies exact
finite scans and retained predicate applications. Selection-vector construction
checks equal lengths before traversal. A malformed reached descriptor stops;
it does not shorten the query list or return false.

A field-valued reciprocal balance is a verifier equation, not this predicate.
Its randomized argument requires its own commitment, challenge and security
law. The [executable control](../../examples/projects/table/README.md) exhibits
a successful reciprocal equation on a false membership instance.

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
`Valid(S,s) ↔ Valid(T,f(s))`. A positive existential encoding does not automatically expose an exact Boolean:
encoding `P(x)` as `exists z, C(x,z)` does not justify negating `C` on a chosen
assignment to decide `not P(x)`. A Boolean consumer requires a law for both
returned truth values, with actual input/output projections and every satisfying
target assignment. A protocol verifier encoding names that verifier; its
cryptographic reduction to the source predicate is a separate law.

Auxiliary values need not be unique, and witness
recovery need not be executable. An importer claiming stronger knowledge or
efficient extraction properties must state those additional requirements.

These are source-encoding adequacy obligations. The current scalar relation
adapter mechanizes a specific authored discrete-log predicate connection; it does
not supply a general native relation-encoding theorem.

An operation whitelist, successful export, hash equality or honest-witness test
alone does not construct such an encoding. Artifact-specific equation comparison
and differential testing provide evidence at their stated scope. The
[constraint views](domains/constraints.md) define the imported mathematical
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
A connector over shared events retains their order. An unordered collection can
admit a read before the write that justifies it. Encoding positions and events
needs injectivity on the admitted domain; reducing unbounded natural positions
modulo a finite field can merge different orders. A compressed encoding needs
that injectivity argument or a separate probabilistic loss. Omitting order
requires a law showing it irrelevant to the connected predicates.

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
[`PIR.Relation.Connected`](../../lean/Zkc/Semantics/RelationComposition.lean).
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

`ReductionContract` here is mathematical notation for an implication. Lean
uses ordinary predicates and the checked obligation derivation API, without
a separate record wrapping this implication.

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
their [actual joint experiment](../../lean/docs/architecture.md#reuse-and-composition).

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
event of an applied rule occurs. A checker implementing this derivation scheme must prove the implication.
Its sequencing law must use the actual facts returned by the first segment;
the current protocol certificate API does not provide a general native rule-graph checker.

An accepted finite derivation remains accepted when one substitution is applied
consistently to its requirements, terminals and every rule. A forward
instantiation proof transports a semantic law when its predicate is the target predicate pulled back
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
terminal value or stop with a [stop reason](../../lean/docs/spec/semantics.md#effects-and-observations).
In particular, `returned rejected` and `stopped reject` are different records.
The [accepted-continuation profile](../../lean/Zkc/Semantics/Continuation.lean)
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


## Native public-table reduction instance

The [structured native profile](ir/mathematics.md)
instantiates a Boolean-sum-to-point requirement. For retained recipe `R`, input
validity is `sum_{x in {0,1}^n} R(T,U)(x) = c` and residual validity is
`R(T,U)(p) = v`, with unit witness. Subject, point and scalar refer to actual
verifier values and are connected to the terminal's inputs and decision.

For true round polynomial `h_i`, received `q_i` and actual draw `r_i`, define
`Bad_i` as a passed guard with formal `q_i != h_i` and `q_i(r_i) = h_i(r_i)`.
Then `S_(i+1) implies S_i or Bad_i`, where `S_i` is the remaining-sum predicate
after the actual verifier prefix. The terminal establishes `S_n`.
Quantitative bounds additionally require degree and challenge-experiment
assumptions. Honest completeness requires agreeing role inputs, faithful
delivery and execution resources. Private subjects need another terminal
contract with public commitments and existential witnesses.

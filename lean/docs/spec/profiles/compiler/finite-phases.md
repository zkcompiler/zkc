# Finite phase certificates

This chapter defines an independent formal model. Native implementation
claims require the explicit correspondence described in the
[assurance policy](../../../../../docs/assurance.md#native-correspondence).

This profile checks finite phase covers against a structured source. Its
realization laws connect operation summaries to the common
[interaction judgments](../../language/interaction.md#all-reply-conformance)
for all typed replies. It describes the independent Lean source and admission
models; native program admission does not consume these certificates.

## Abstract phase policy

Fix a source language `L` and an abstract phase type `X` with decidable equality.
An abstract phase policy consists of:

```text
step : L.Op → X → Option (List X).
```

`step op before = some exits` is a proposed summary of all returning phases of
that source operation at that abstract entry. `none` means unsupported by this
policy. `some []` supplies an empty returning cover; its semantic law must
justify the absence of a returning phase from each related concrete entry.
It is distinct from an unsupported summary.

Phase lists represent finite sets for coverage and containment. The type `X`
itself need not be finite. No numeric widening or order on `X` is assumed.

Define `merge xs ys` by concatenating the lists and retaining the first
occurrence of each phase. Then:

```text
x ∈ merge xs ys ⇔ x ∈ xs ∨ x ∈ ys.
```

The selected aggregate operation transfer is:

```text
stepMany policy op [] = some []
stepMany policy op (x :: xs) =
  let first ← policy.step op x
  let rest  ← stepMany policy op xs
  some (merge first rest).
```

Here and below `←` propagates `none`. Every supplied entry phase is checked;
one unsupported summary causes this aggregate transfer to fail. An empty entry
list consults no operation summary.

## Certificates

A phase certificate is finite data with grammar:

```text
Certificate X = terminal
              | next(tail : Certificate X)
              | branch(yes : Certificate X, no : Certificate X)
              | loop(invariant : List X,
                     body : Certificate X, next : Certificate X)
              | bind(body : Certificate X, next : Certificate X).
```

The certificate's constructors match the actual source's control shape.
`terminal` matches a return or stop; `next` matches an operation binding;
`branch` matches a branch; `loop` matches a bounded iteration; and `bind`
matches a compact region's explicit shared continuation. Only the loop
constructor carries an abstract-state annotation. A certificate supplies no
new source, operation policy, interpretation, entry list or allowed return list.

## Checking rules

For fixed `policy`, write `check p c starts : Option (List X)`. Returns and
stops have rules:

```text
check (ret v)  terminal starts = some starts
check (stop r) terminal starts = some [].
```

For an operation binding:

```text
check (letOp op args p) (next c) starts =
  let exits ← stepMany policy op starts
  check p c exits.
```

For a branch:

```text
check (branch guard yes no) (branch cy cn) starts =
  let ys ← check yes cy starts
  let ns ← check no cn starts
  some (merge ys ns).
```

For a loop:

```text
check (iterate count initial body next) (loop inv cb cn) starts =
  if starts ⊆ inv then
    let exits ← check body cb inv
    if exits ⊆ inv then check next cn inv else none
  else none.
```

Containment means that every member of the first list occurs in the second.
Constructor mismatches return `none`. The selected checker tests loop entry
containment before the body, and body-exit containment before the suffix.

The branch rule checks both arms with the same entry cover. It does not use
the guard's value. The loop rule checks the complete body against the supplied
invariant and checks the suffix from that invariant. It does not unroll the
count; it checks the body even when the count is zero.

For compact sequencing:

```text
check (bind body next) (bind cb cn) starts =
  let exits ← check body cb starts
  check next cn exits.
```

The suffix is checked once from the body's complete returning cover. A stopped
body contributes no returning phases; this does not erase its actual stopped
state/events. The checker traverses compact regions directly. Tree programs use
their `toRegion` embedding and the same checking algorithm; flattening a shared
continuation is not part of admission. Merging path information may lose
precision, so this is not a claim of equivalence to independently annotated
copies of a flattened program. Check cost also depends on phase-set sizes and
operation summaries, not only the number of source nodes.

A successful check can retain duplicate entries from an unchanged input list;
`merge` removes duplicates at its own uses. Semantic soundness uses membership,
not a canonical serialization of every phase list.

## Realizing a policy

Fix the actual source interpretation `M : Interpretation L Σ` and concrete
interaction `P` over `Σ`. A realization of `policy` supplies:

```text
relates : X → P.Phase → Prop.
```

For every `op`, `before` and `exits` with
`policy.step op before = some exits`, it additionally establishes, for every
typed argument list `args` and every concrete phase `φ` satisfying
`relates before φ`:

```text
Conforms P (M.operation op args) φ

Returns P (fun _ ψ => ∃ after ∈ exits, relates after ψ)
  (M.operation op args) φ.
```

The judgments are the [all-reply interaction judgments](../../language/interaction.md#all-reply-conformance).
The law concerns the whole interpreted operation body. That body may make
several interface calls, and every interface-typed reply is included. A law
for one sampled or honest reply cannot replace this obligation.

The relation need not be equality, functional or total. Consumer resolution
binds it and its operation laws to the actual interpretation and interaction.
An absent summary requires no operation law; it supplies no positive legality
claim for that entry either.

## Coverage and soundness

Define concrete phase coverage by:

```text
Covered starts φ ⇔ ∃ x ∈ starts, relates x φ.
```

Coverage weakens along list containment. If
`check policy p c starts = some exits`, the supplied realization laws imply,
for every typed source environment `η` and concrete entry phase `φ` with
`Covered starts φ`:

```text
Conforms P (⟦p⟧M η) φ ∧
Returns P (fun _ ψ => Covered exits ψ) (⟦p⟧M η) φ.
```

This is a universal input-environment result, conditional on actual initial
coverage. Empty `starts` covers no concrete phase. A successful syntactic check
from it therefore establishes no invocation's phase legality without another
initial-domain argument. A loop with an empty entry list can still check a
nonempty supplied invariant; emptiness does not bypass certificate traversal.

An empty returned cover describes no normal returning phase. It does not erase
the source's stopping behavior or its retained runtime state and events.

## Checked phase admission

For the consumer's policy, actual source `p`, initial cover `starts` and allowed
return cover `allowed`, a phase admission record contains:

```text
certificate : Certificate X
exits       : List X
accepted    : check policy p certificate starts = some exits
permitted   : exits ⊆ allowed.
```

The admission function runs `check` and returns this record exactly when the
check returns an exit list contained in `allowed`. It returns `none` otherwise.
The consumer, independently of the certificate, supplies the policy, realized
meaning and interaction, entry phases and allowed return phases.

The maintained `checkRegion_sound` proves the common soundness judgment directly
for compact regions; tree `check_sound` follows through the embedding.
`Admitted`/`admit` package the tree-program result. The
`RegionArtifact.Checked` admission theorems join checked phase coverage to the
actual decoded source and candidate region, establishing every instrumented
call's permission and allowed returned phases. They remain conditional on
consumer-selected laws and actual initial coverage. Applying these results to
another implementation requires correspondence for its decoder, checker and
execution; parsing the same certificate is insufficient.

With the realization laws and actual initial coverage, a phase admission record
establishes conformance and `Returns P (fun _ ψ => Covered allowed ψ)` for the
actual source denotation in every environment. It does not establish public
call bounds, input access, locality or an arbitrary result-dependent postcondition
without additional evidence.

Combining this result with a [checked direct plan](direct-plan.md#checked-plans)
for the same source and actual interpretation establishes permission of every
instrumented plan call and coverage of every actual returning final phase.
Removing the phase instrumentation recovers the entire ordinary plan execution,
including stopped outcomes, residual state and original events.

## Precision and unsupported cases

This analysis is sufficient and intentionally incomplete for the semantic phase
judgments. It can refuse a well-formed program whose legality depends on an
infeasible branch, a reply/phase correlation, a value-dependent invariant or the
fact that a loop count is zero.

*Example.* A zero-iteration loop with a body that requests a challenge too early
never executes that body and can conform semantically. The invariant checker
still checks the body and refuses that certificate. This is not a proof that
the program is semantically illegal.

A stronger analysis, another sound certificate rule or a direct semantic proof
may establish admission for such a program. Weakening the meaning of an
operation summary to ignore a possible reply is not a sound repair.

## Table trace application

The independent [table model](../../../../Examples/TableProtocol/README.md)
instantiates this discipline with phases `{ready, sent}`, related by equality.
Initial coverage is `[ready]`; allowed normal-return coverage is `[ready]`.

| Logical operation | Abstract entry | Returning cover |
|---|---|---|
| `send` | `ready` | `[sent]` |
| `draw` | `sent` | `[ready]` |
| `send` at `sent`, or `draw` at `ready` | Either unsupported entry | Unsupported |
| Other operations of this table model | Any phase `p` | `[p]` |

Write calls are enabled at either phase and preserve it for every returned
Boolean. Send calls advance to `sent` for either returned Boolean; draw calls
advance to `ready` for every field reply. A stopped call supplies no reply and
retains its entry phase and actual state/events. Pure table operations perform
no interaction calls.

The consumer supplies the interpretation and coverage sets. The certificate
contains only the structural grammar above. Admission checks the actual source
and candidate, then checks phase coverage for that same decoded source. A
normal return with outstanding `sent` coverage is refused. Stops require no
normal-return phase, and pure computations need not send anything.

This describes one invocation starting at `ready`. A caller linking invocations
must establish its own boundary-phase and resource relation. Stored tape length
or message count does not determine the phase. The result supplies neither
participant projection nor a sampling law.

## Stateful table application

The model's endpoint admission selects actor `prover` and an independently
supplied entry `[role, phase]`. The source role must agree, the phase must be
`ready` or `sent`, and the initial cover is exactly `[phase]`. Private inputs
must belong to the selected actor; normal returns remain covered by `[ready]`.
An admitted entry must match the consumer's actual owned actor and phase.
It is not a provider identity or complete-state equality test.

Instrumentation follows each actual interface call, including calls inside a
composite source operation. If its second call stops, the residual phase
includes the first call's completed transition. A final operation-result check
cannot replace this call boundary. A stopped run supplies its actual residual
phase, not permission to replay the source; a subsequent invocation requires
admission from that phase.

This logical phase contract assumes exclusive provider access, phase/data
consistency and truthful outcomes. Host interruptions that produce no logical
completion need a separate recovery contract; the model does not establish
crash consistency, remote exactly-once execution or authentic restoration.

## Physical scalar application

The independent [physical table model](../../../../Examples/TablePhysical/README.md)
retains the logical input context and original source certificate. Its decoded
physical body's projection must denote the same procedure as the original
source for every input under the selected interpretation. Its folding rule
replaces `linear(a, a, r)` with `a` only when the endpoints are the same variable;
the field interpolation law justifies that replacement. Checking compares the
source and projected candidate through the existing control grammar. The
certificate still applies to the original source.

Instantiate physical correspondence with the interaction's call instrumentation.
For related inputs and stores, complete physical execution must correspond to
logical execution, including actual calls, final phase, residual provider state
and stops. Combined with source admission and initial coverage, this establishes
permission of physical execution's logical calls and coverage of normal returns.
Equality under one uninstrumented handler does not provide that premise.

Preparation and scalar reads have no provider calls or phase changes. Immutable
publication preserves every previously represented value, and final scalar
values are interpreted in the completion store. Invalid shape stops at its
logical occurrence even when the result is unused. The fold law does not justify
deleting unused partial operations or identifying distinct variables from
sampled values, equal types or an unchecked invariant.

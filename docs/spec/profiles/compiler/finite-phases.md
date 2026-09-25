# Finite phase certificates

This profile checks finite phase covers against a structured source. Its
realization laws connect operation summaries to the common
[interaction judgments](../../language/interaction.md#all-reply-conformance)
for all typed replies.

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
`Admitted`/`admit` currently package the tree-program result. A native compact
consumer must bind the actual region, policy, initial coverage and allowed exits
to its invocation; parsing a binding certificate is not that implementation.
The maintained `RegionArtifact.Checked` admission theorems already join checked
phase coverage to the actual decoded source and candidate region, establishing
every instrumented call's permission and allowed returned phases. They remain
conditional on consumer-selected laws and actual initial coverage. The table
consumer below implements native certificate custody for one fixed policy;
general native policy resolution remains implementation work.

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

The optional `table-round/1` consumer profile interprets `table-protocol/1` with
local role `trace`. It admits both finite-source and compact-region artifacts.
Its abstract and concrete phase types are `{ready, sent}`, related by equality.
Initial coverage is `[ready]`; allowed normal-return coverage is `[ready]`.

| Logical operation | Abstract entry | Returning cover |
|---|---|---|
| `send` | `ready` | `[sent]` |
| `draw` | `sent` | `[ready]` |
| `send` at `sent`, or `draw` at `ready` | Either unsupported entry | Unsupported |
| Other operations of this table profile | Any phase `p` | `[p]` |

The interaction enables base write calls at either phase and preserves phase
after any returned Boolean reply. It enables send calls only at `ready` and
moves to `sent` for either returned Boolean. It enables draw calls only at
`sent` and returns to `ready` for every field reply. Stopped calls supply no
reply and retain their actual state/events; their instrumented entry phase
does not advance. Pure table operations perform no interaction calls.

The selected role, summary interpretation and coverage sets come from the
consumer profile. The untrusted certificate carries only the grammar above.
Admission checks the actual retained source and candidate under the selected
artifact contract, then checks phase coverage for that same decoded source.
The direct plan uses its direct preservation law; the physical application
below supplies a separate correspondence law.
A return with outstanding `sent` coverage is not admitted; a stop requires no
normal-return phase. No required send count is imposed on pure computations.

This discipline describes one invocation starting at `ready`. It does not infer
an initial phase from stored tape length or sent messages, reset an evolving
provider, or authorize resuming a stopped protocol as a new invocation. A caller
linking invocations must establish its own boundary-phase/resource relation.
This application establishes neither endpoint projection nor a sampling law.

## Stateful table application

The separate `table-endpoint/1` profile uses the same table interpretation,
summary laws and `{ready, sent}` phases. Its local actor is `prover`; allowed
normal-return coverage is `[ready]`. This is the phase part of local endpoint
admission. It adds no participant projection, multi-role ownership theorem,
public call-bound admission or cryptographic provider law. Its invocation's
private inputs must belong to the selected actor.

The consumer supplies an entry record `[role, phase]` independently of source,
candidate and certificate. Admission requires source-role agreement, role
`prover`, and a decoded phase of `ready` or `sent`. The initial cover is exactly
`[phase]`. The installed checker acknowledges the selected profile and decoded
entry. The admitted object retains both with the checked source/candidate and
certificate; acknowledgment still relies on the installed checker's execution.

Before binding inputs, reserving resources and starting execution, a stateful
consumer compares that entry to its actual owned actor and recorded phase.
Missing evidence, another profile, a different entry or an unknown actual phase
cannot bind that endpoint. A phase-less request does not downgrade an existing
stateful binding to the trace application. Matching entries authorize reuse of
code under the entry domain; they are not a provider identity or complete-state
equality test.

Native instrumentation follows **each actual interface call**. In this table
interpretation those calls are write, send and challenge receive. A returned
call advances according to the interaction; a stopped call retains its entry
phase and actual effects. In a composite source operation, a stop at its second
call retains the second call's entry phase, including the first call's completed
transition. A final source-operation result check cannot replace this boundary.
The local actor's identity is checked before these primitives; all belong to
that same actor in this profile. This fixed-role check does not demonstrate
ownership discrimination between participants.

During a native call, `unknown` records that no accepted completion is yet known.
An error, malformed reply or unwind before accepted completion leaves it unknown
and blocks binding. A host failure between completed calls retains the last
known phase. `unknown` is a host recovery marker, not a logical phase or stopped
outcome; both the reference entry and invocation codecs reject it. No ordinary
Lean execution is claimed for a native interruption.

Initial phase/data consistency, exclusive provider access and truthful logical
outcomes are deployment/adapter obligations. The in-process marker does not
establish crash consistency, remote exactly-once execution, or authentic state
restoration. Persistent deployments need a separate recovery contract; editing
or reloading an invocation file is not checked recovery evidence. A record's
message count and remaining tape do not determine its phase.

A stopped run supplies its actual residual phase, not permission to replay its
source. A subsequent source must be admitted from that phase. This profile does
not offer a successful handoff at `sent`: its normal returns are at `ready`.
Stops remain failures/terminal outcomes, not a newly invented yield convention.
A controller needing another normal boundary must select a corresponding
application of the existing general return-cover contract.

## Physical scalar application

The `table-physical-plan` realization may consume either table policy above.
It retains the logical input context and original source certificate. Its
independently decoded physical body's logical projection must denote the same
procedure as that original source for every input environment under the installed
interpretation. The admitted table folding rule replaces `linear(a, a, r)` with
`a` only when its endpoints are the same variable; the field interpolation law
justifies the replacement. Independent normalization compares the source and
projected candidate through the existing control grammar. Other operations,
operands, guards and control are retained. Successful checking acknowledges the
physical realization as well as the selected policy and, for the stateful
application, the exact entry. The certificate remains a certificate for the
original source, even when its candidate has fewer operations. A direct or
reference-only realization's acknowledgment cannot authorize this candidate.

The physical correctness law is parameterized by the logical handler, state
and events. Instantiate it with the interaction's call instrumentation. For
related inputs and stores, the complete physical execution must correspond to
the instrumented logical execution, including actual logical calls, final
phase, residual provider state and stopped outcomes. Together with source
admission and initial coverage, this implies enabled physical execution's
logical calls and covered normal returns. Equal observations under a single
uninstrumented handler do not supply this premise.

Preparation and scalar reads have no logical provider calls or phase changes.
Immutable publication must preserve every previously represented value; final
scalar values are interpreted in the actual completion store. An invalid shape
still stops at its logical occurrence, even when the result is unused.

The native stateful adapter retains the same logical endpoint owner across
physical operations. It applies the existing actual-call completion discipline
and entry checks. A failed operand read before a call keeps the last known
phase. A host failure during the call leaves it unknown; a logical stopped
completion retains its entry phase and effects. Output decoding cannot reset
the endpoint or discard its completion state.

The executable reference's instrumented simulation is formal evidence. The
native realization consumes it through the checker contract and differential
validation; this profile does not assert a native implementation proof or
authorize other logical rewrites. The fold's total-procedure law does not justify
deleting unused partial operations or replacing distinct variables using sampled
values, equal types or an invariant not checked for the authored loop body.

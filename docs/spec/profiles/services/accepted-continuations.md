# Accepted continuations

An accepted continuation runs an arm after the actual verifier returns an
accepted value. The arm may return a different result type or stop. This
profile defines ordinary composition, retained reports, a single-entry
handoff, and an installed atomic service with separate authority state.

## Verifier decisions and ordinary composition

Use the common [terminal datatype and contract](../../properties/relations.md#terminal-decisions-and-contracts).
For signature `I`, accepted value type `A` and arm result type `B`, let:

```text
p   : Proc I (Terminal A)
arm : A → Proc I B

after(p,arm) = bind(p, result ↦
  match result with
  | accepted a → arm(a)
  | rejected   → halt reject).
```

An `accepted` constructor is verifier result data. Its mathematical meaning
comes from the actual bound source, interpretation and terminal/property
contract. Formation or a successful host call does not supply that meaning.

Fix an actual handler `h : Handler I S E` and initial runtime state `s`.
Write `first=run h p s`. Complete execution is:

```text
first.outcome = stopped why:
  run h (after(p,arm)) s = (stopped why, first.state, first.events)

first.outcome = returned rejected:
  run h (after(p,arm)) s = (stopped reject, first.state, first.events)

first.outcome = returned (accepted a):
  let last=run h (arm(a)) first.state
  run h (after(p,arm)) s =
    (last.outcome, last.state, first.events ++ last.events).
```

The arm is not invoked in the first two cases. Returned rejection becomes
an explicit reject stop without adding a rejection-notification event. In the
accepted case the arm starts from the actual verifier post-state. Failed arm
effects remain; no rollback or prefix retraction is part of this composition.
If the arm returns `false`, `none` or another negative value as ordinary `B`
data, the combined execution still returns that value.

## Phases and finite bounds

For interaction `P`, initial phase `φ` and returned-phase predicate
`post : Terminal A → P.Phase → Prop`, the formation rule is:

```text
Conforms(P,p,φ)
Returns(P,post,p,φ)
∀ a ψ, post(accepted a,ψ) → Conforms(P,arm(a),ψ)
─────────────────────────────────────────────────────
Conforms(P,after(p,arm),φ).
```

These use the common [all-reply return and sequencing rules](../../language/interaction.md#phase-safe-sequencing).
The arm's premise concerns the verifier's actual permitted accepted return
phases, not an unrelated initial phase. A rejected return has no arm
continuation. Acceptance grants no additional runtime-state precondition;
an arm needing one establishes it through the actual verifier contract or
checks it before use.

If `Within(n,p)` and `Within(m,arm(a))` for every `a`, then
`Within(n+m,after(p,arm))`. A zero arm bound is allowed, and a rejected branch
adds no calls. This bound concerns calls in the composed body; it does not
count host policy computation, ledger storage or native work.

## Retained verifier and arm report

The report type is:

```text
Report S E A B = {
  verifier : Execution S E (Terminal A),
  arm      : Option (Execution S E B),
  combined : Execution S E B
}.
```

For the same `p,arm,h,s`, define `runReport(p,arm,h,s)` by running the verifier
once and constructing the following record:

```text
first.outcome = stopped why:
  (first, none, (stopped why,first.state,first.events))

first.outcome = returned rejected:
  (first, none, (stopped reject,first.state,first.events))

first.outcome = returned (accepted a):
  let last=run h (arm(a)) first.state
  (first, some last, (last.outcome,last.state,first.events ++ last.events)).
```

The verifier field is exactly `run h p s`, and the combined field is exactly
`run h (after(p,arm)) s`. The optional arm record contains its own events,
without a second copy of the verifier prefix inside that field. This account
preserves verifier acceptance even when the combined execution stops in the
arm. It does not execute the verifier again to reconstruct its decision.

An implementation may retain a smaller representation with an adequate
observation relation instead of copying logical states. It MUST preserve the
verifier, arm and combined observations that its report interface promises.
A freely constructed or deserialized record proves neither that the execution
occurred nor that its private fields may be released.

## Single-entry handoff

Let `Key` have decidable equality and let the authoritative entry have type
`Option (Key × A)`. This component starts with an already-authorized handoff;
it does not issue or authenticate the right. Define:

```text
take(expected,none) = (stopped refused,none,[])
take(expected,some(key,a)) =
  if key=expected then (returned a,none,[])
  else (stopped refused,some(key,a),[]).
```

The event type can be unit; these transitions emit no events. A matching take
consumes the entry before returning its value. A mismatch retains the unmatched
entry. Repeating a matching take against the resulting state therefore refuses.
`Key` denotes the selected source run/site, binding, consumer and target
occurrence through its actual interpretation; equality alone does not create
those meanings or an authorization scheme.

For an arm that can receive this entire entry state, consumption persists only
under an appropriate frame. In particular:

```text
arm : A → Option (Key × A) → Execution (Option (Key × A)) Unit B
(arm(a,none)).state = none
────────────────────────────────────────────────────────────
follow(take(key,some(key,a)),arm).state = none.
```

This applies to every arm outcome under the displayed final-state premise.
An arm that writes the old entry back before aborting violates that premise
and can restore the right. A final-state frame alone does not exclude temporary
restoration at a reentrant intermediate boundary. Exclusive custody, issuance
and the lifetime of this authoritative entry are separate obligations. The
installed service below instead removes ledger-writing access from its arm
and exposes only one atomic invocation boundary.

## Admitted invocation and installed service

Fix interaction `P`, frontend `F : Frontend I P.Role (Terminal A)` and endpoint
contract `C : EndpointContract P (Terminal A)`. An invocation contains:

```text
Invocation F C = {
  source   : F.Source,
  binding  : F.Binding,
  actor    : P.Role,
  body     : Proc I (Terminal A),
  admitted : Admitted(F,C,source,binding,actor,body)
}.
```

The common [admission judgment](../../language/interaction.md#endpoint-admission)
fixes actual elaboration, input validity, phase conformance, public call bound
and returned-phase contract for the same operands. The executed body is that
frontend's actual elaborated body. A source/binding label attached to a
different body does not satisfy the invocation definition. Binding values
retain their common source and capture-lifetime obligations.

The policy type and ordered parameters are:

```text
Policy F = F.Source → F.Binding → P.Role → Nat → Nat → Nat → Bool
policy(source,binding,actor,site,consumer,target).
```

The three natural identifiers denote the invocation site, selected recipient
and target occurrence. This policy interface has no separate runtime-state,
run-number, ledger or arm-result operand. A claim requiring a result predicate
must establish it in the installed arm contract. The policy is an installed
function; a request cannot substitute its own authority Boolean.

The service fixes:

```text
Service F C S E B = {
  policy       : Policy F,
  handler      : Handler I S E,
  arm          : A → Proc I B,
  armBound     : Nat,
  armConforms  : ∀ a ψ, C.returned(accepted a,ψ) → Conforms(P,arm(a),ψ),
  armBounded   : ∀ a, Within(armBound,arm(a))
}.
```

The requester supplies an admitted invocation, site, consumer, target and
ordinary input state. It cannot replace the installed handler, policy or arm.
The corresponding composed body conforms from `C.initialPhase` and has call
bound `C.publicBound+service.armBound`. A native service identifier MUST select
this same installed interpretation and its authoritative ledger instance.

## Ledger, receipt and export result

The service's authority state is separate from ordinary runtime state `S`:

```text
Ledger = { nextRun : Nat, consumedTargets : List Nat }
emptyLedger = (0,[])

Receipt F S E A B = {
  source : F.Source, binding : F.Binding, actor : P.Role,
  run : Nat, site : Nat, consumer : Nat, target : Nat,
  report : Report S E A B
}

Result F S E A B = {
  receipt          : Option (Receipt F S E A B),
  combined         : Execution S E B,
  ledger           : Ledger,
  authorizedExport : Option B
}.
```

Target freshness is non-membership in `consumedTargets`, across all runs, sites
and consumers of this one instance. Changing the site or consumer does not
make a consumed target fresh. Target identifiers require the instance's actual
occurrence interpretation; they are not globally authenticated identifiers.
`nextRun` is an unbounded natural number. A bounded native representation
states a capacity domain that preserves this meaning. A refusal outside that
domain occurs at the [native admission/start boundary](../../realization/representations.md#capacity-and-progress)
before execution; it is not the logical service's `stopped refused` result or
a wrapped identifier.

For an arm outcome define `exportReturned(returned b)=some b` and
`exportReturned(stopped why)=none`. This function adds no predicate on `b`.
Its authorization is for the actual policy-selected consumer in the receipt;
an `Option B` detached from that transition does not carry independent authority.

## Atomic service transition

For the actual service, invocation `call`, identifiers `site,consumer,target`,
runtime state `state` and authoritative ledger `ledger`, define
`execute(service,call,site,consumer,target,state,ledger)` as follows. First check:

```text
allowed = service.policy(call.source,call.binding,call.actor,site,consumer,target)
fresh   = target ∉ ledger.consumedTargets.
```

If policy denies or the target is consumed, the result is:

```text
(receipt=none,
 combined=(stopped refused,state,[]),
 ledger=ledger,
 authorizedExport=none).
```

Policy is checked before target membership in the defining algorithm. Both
refusal cases have this same complete result. Neither executes the verifier,
allocates a run number or emits a runtime event.

Otherwise set `runId=ledger.nextRun`, execute
`first=run service.handler call.body state`, and define
`next=(runId+1,ledger.consumedTargets)`. The three result cases are:

| Actual verifier outcome | Arm and combined execution | Final ledger | Export |
|---|---|---|---|
| `stopped why` | No arm; `(stopped why,first.state,first.events)` | `next` | None |
| `returned rejected` | No arm; `(stopped reject,first.state,first.events)` | `next` | None |
| `returned (accepted a)` | Run `arm(a)` from `first.state`; use its outcome/state and concatenate verifier then arm events | `(runId+1,target :: ledger.consumedTargets)` | `exportReturned(last.outcome)` |

Every permitted fresh attempt creates a receipt containing the actual source,
binding, actor, old `runId`, site, consumer, target and the displayed report.
Its report is `runReport(call.body,service.arm,service.handler,state)`, and its
combined field agrees with ordinary `after`. The run counter advances once
even when the verifier rejects or stops. Those cases do not consume the target,
so a later permitted invocation at that target can retry with a new run number.

On acceptance, the target is consumed before entering the arm. The arm and
handler operate on `S` and have no ledger-writing operation in this profile.
Consequently both returned and stopped arms leave that consumption intact.
All previously consumed targets remain consumed. Replaying any such target
against this successor ledger refuses before verification, independently of
whether its earlier arm returned or stopped. Ledger updates are authority
state changes, not additional `E` events.

The transition is atomic to callers. Its logical ordering does not define
callbacks, concurrent intermediate states or crash points inside the invocation.
Native implementations exposing any such boundary need an extended interface
and custody law; a final ledger snapshot alone cannot establish them.

*Example (informative).* Suppose the admitted verifier accepts `7` without
changing the state or emitting events. The arm
increments ordinary state from `0` to `1`, emits `[42]` and stops abort. The
receipt still records acceptance, the combined execution is
`(stopped abort,1,[42])`, the target is consumed and there is no export.
A later request at that target refuses using the retained ledger. Returning
`false` instead would authorize that ordinary arm value unless the installed
arm enforces an additional validation rule.

## Authenticity, custody and disclosure

With every operand above fixed, define mathematical authenticity by:

```text
Authentic(out) ⇔ out = execute(service,call,site,consumer,target,state,ledger).
```

This is correspondence to the actual atomic transition. It is not a signature
scheme, deserialization check or proof that a remote service ran. A receipt
record alone is neither an invocation capability nor a replay-resistant ticket.
Authenticity also says nothing by itself about permission to disclose its
source, captures, verifier value, arm result or runtime histories.

A native consumer MUST use the same installed instance and its current
authoritative ledger, preserve target consumption through arm failure, and
isolate that ledger from requester and arm writes. Reusing an old ledger copy
or resetting the instance's authority is outside the interpretation. Any
encoded receipt or service handle needs its actual identity and execution
correspondence under the common [realization requirements](../../realization/representations.md).

The selected [public-status projection](../../properties/disclosure.md#authorized-service-status-projection)
can report receipt presence, verifier decision/stop and combined return/stop
status while erasing private payloads and state. Its use still needs permission
to release those statuses in the actual experiment. Authorized transfer to the
policy-selected consumer and public disclosure are separate judgments.

This profile authorizes one atomic arm result for a fresh accepted target.
It provides no transferable-ticket API, repeated export registry, reentrant
execution, crash persistence, distributed custody or hostile-owner
authentication. Each extension must preserve the actual invocation, consumer
and authority-state correspondence at its newly exposed boundaries.

# Accepted continuations and retained decisions

The [continuation specification](../spec/profiles/services/accepted-continuations.md) owns the selected
combinator, report and atomic authorization profile. This chapter explains its
equations and examples. The
[correspondence](../spec/correspondence/properties.md) records the
Formal declarations and exact limits. Native authentication, custody and release
remain realization obligations.

## 1. Three results with different meanings

Returning to a caller, reaching an accepting verifier decision, and completing
a subsequent computation are different events. A verifier interpretation
supplies the meaning of:

```text
Terminal A = accepted A | rejected
```

An arbitrary body can construct `accepted a`; the constructor alone proves
no protocol relation or security claim. Its verifier meaning must come from
the bound source, inputs, interpretation and terminal predicate. An operation
or body that stops has no returned `Terminal` value. In particular, an
unavailable resource producing `refused` is not silently a negative verifier
decision. A complete verifier contract must explain all applicable cases.

The follow-on computation, called the arm below, may return a different type
`B`, emit events, change state or stop. An accepted value of type `A` does
not imply that this later computation succeeds.

## 2. The ordinary continuation equations

[CONT-02](../spec/profiles/services/accepted-continuations.md#verifier-decisions-and-ordinary-composition) specifies:

```text
after p arm = p.bind (fun | accepted a => arm a | rejected => halt reject)
```

Let `v = p.run h s`. Its complete execution has three cases:

| Verifier execution | Arm execution | Combined execution |
|---|---|---|
| `v.outcome = stopped why` | None | `(stopped why, v.state, v.events)` |
| `v.outcome = returned rejected` | None | `(stopped reject, v.state, v.events)` |
| `v.outcome = returned (accepted a)` | `t = (arm a).run h v.state` | `(t.outcome, t.state, v.events ++ t.events)` |

The accepted arm starts in the actual retained state. Both successful and
failed arm events remain after the verifier prefix. No rollback is implied.
`rejected_no_arm`, `stopped_no_arm` and `accepted_retains_prefix` prove these
equations. A negative terminal returned by `p` and a direct `halt reject`
can have the same combined stop, but their verifier executions differ.

The `formed` theorem additionally requires the verifier body's conformance,
its [returned-phase condition](composition.md), and each accepted arm's
conformance at every phase permitted by that condition. Acceptance does not
reset the interaction phase or grant missing module preconditions.

## 3. Retain the verifier result independently

Ordinary bind retains state and events but replaces an earlier returned value
with the suffix's outcome. With unit state and no events,

```text
after (done (accepted ())) (fun _ => halt abort)
```

has the same complete execution as `halt abort`. The
[integration control](../../formal/Tests/Integration.lean) `unrecorded_acceptance_then_abort`
proves this equality. It is not a defect in `bind` or in prefix preservation.
The earlier acceptance was never recorded in an enduring component.

[CONT-03](../spec/profiles/services/accepted-continuations.md#retained-verifier-and-arm-report) specifies the report produced by `Continuation.runReport p arm h s`:

```text
Report S E A B = {
  verifier : Execution S E (Terminal A),
  arm      : Option (Execution S E B),
  combined : Execution S E B
}
```

`runReport` evaluates the verifier and, only for an accepted return, the arm
in its retained state. It uses the cases in §2 to assemble the report.
Three generic theorems connect it to the original execution:

- `report_verifier`: the retained verifier execution is exactly `p.run h s`.
- `report_combined`: the combined result is exactly `(after p arm).run h s`.
- `report_accepted`: an accepted verifier outcome remains accepted in the
  retained field, and the arm field records its actual execution, regardless
  of that arm's eventual outcome.

For example, the checked handler records one counter increment per call.
Starting at `3`, the verifier returns `accepted 3` at state `4`, with events
`[3]`. The arm makes another call and aborts. The report retains:

```text
verifier = (returned (accepted 3), 4, [3])
arm      = some (stopped abort, 5, [4])
combined = (stopped abort, 5, [3,4])
```

This is an internal mathematical account, not a mandated runtime layout.
An implementation may retain an appropriately scoped decision record instead
of copying all intermediate state, provided its correspondence establishes
the required observation. The report type has public constructors in Lean;
an arbitrary record is not evidence that these computations occurred.
The theorems concern `runReport` with its actual operands and state.

Those operands bind the mathematical result to an execution expression.
They do not authenticate a serialized claim about a source, runtime occurrence
or native computation. The complete adapter must retain that external binding
through actual use. Reports may contain private values, states and traces;
they are not automatically permitted public artifacts. The selected disclosure
projection remains required for any exported representation.

## 4. One-use handoff and its frame condition

The existing `take` reference models one outstanding, already-authorized
handoff with a ledger of type `Option (Key × A)`. A key stands for the exact
source run/site, capture binding, consumer and target occurrence. Merely
choosing a Lean `Key` type or a digest does not construct those meanings.

```text
take expected none                  = (stopped refused, none, [])
take expected (some (key,a)), match  = (returned a, none, [])
take expected (some (key,a)), other  = (stopped refused, some (key,a), [])
```

Exact key equality is a parameter of this reference. A mismatch leaves the
unmatched right in place; a successful take consumes it before the arm starts.
`wrong_target` and `replay_refused` prove the corresponding cases. The latter
uses the residual authoritative ledger after the first take, not a copied
old ledger value. Issuance, generative occurrence identity and exclusive
access to that ledger must be supplied by its interpretation.

The preserved `failing_arm_consumes` theorem uses a specific arm that stops
while preserving its input state. It is not a theorem about arbitrary arms
with write access to the entire ledger. The general derived law makes the required frame explicit:

```text
(arm a none).state = none
--------------------------------------------------------------
((take key (some (key,a))).follow arm).state = none
```

`consumed_under_frame` proves this for every arm outcome. The premise is
a final-state frame; by itself it says nothing about intermediate access.
A real authoritative registry should isolate its custody state from arbitrary
arm writes and keep consumption effective at every permitted observation or
reentrant boundary. A semantic state product with controlled operations is
one possible implementation; a host-language type alone is insufficient.

A negative control supplies a privileged arm that writes the old entry
back and then aborts. The consumed entry reappears. This exhibits why the
frame is necessary, rather than changing the original theorem or imposing
transactional rollback. These ledger laws do not establish crash persistence,
distributed registry consistency or safety against a hostile registry owner.

## 5. Joined source, authorization, custody and export

[AuthorizedContinuation](../../formal/Zkc/Semantics/AuthorizedContinuation.lean)
defines the actual atomic adapter. Its `Invocation` contains the source,
immutable binding, actor, body and a proof of the common `Admitted` judgment.
The body executed is the one returned by that frontend's elaboration. An
installed service policy receives these actual source/binding/actor values
and the requested site, consumer and target. The requester does not supply an
"authorized" Boolean to replace that policy.

`Service` fixes the installed policy, handler and arm; requests cannot replace
these. Its arm conformance and public call-bound fields connect to the actual
verifier returned-phase contract through `Service.formed` and `Service.bounded`.
Native service identity must select this same installed interpretation.

Each service instance maintains an authoritative `Ledger` with a monotone next
run number and consumed target occurrences. The transition is:

1. A denied policy or already-consumed target refuses before verifier execution.
2. A fresh permitted attempt executes the bound verifier and receives its actual
   run number. Rejection/stop retains the verifier result, creates no arm export
   and does not consume an accepted-continuation target.
3. Acceptance reserves and consumes the target before invoking the arm. The arm
   receives ordinary runtime state but no operation for writing the ledger.
4. The receipt retains source, binding, actor, run, site, consumer, target and the
   actual verifier/arm/combined report. A returned arm authorizes its actual
   result; a stopped arm authorizes no export. Ordinary negative result data
   is still a return; additional export validation belongs in the installed arm.

`source_bound` proves the receipt fields refer to the actual invocation and
verifier execution. `actual_report` equates the combined computation with the
ordinary `after` semantics on the admitted path. `accepted_consumed`,
`failed_arm_no_export`, `unauthorized_refused` and `replay_refused` establish the
resource/export behavior. `Authentic` denotes correspondence to this actual
transition; a freely constructed or deserialized receipt is not that proof.

The [integration controls](../../formal/Tests/Integration.lean) use an executable
source frontend and an installed policy fixing source, capture, site, consumer
and target. The accepted value is 7. Its arm changes state to 1, emits `[42]`
and aborts. The receipt remains accepted, the target remains consumed, no export
is authorized and replay refuses. Separate controls cover successful export,
rejected source, wrong body, changed capture, wrong site/consumer/target and
replay under the current ledger.

These laws apply to a **single atomic export in one service instance**. It does not require a transferable ticket or
multi-export registry. Target numbers are interpreted within the authoritative
instance; a native implementation must bind instance identity and reject copied
or reset authority. Runtime reentrancy, crash recovery, distributed custody and
cross-instance persistence require corresponding extensions. The finite adapter
provides no callbacks into ledger transitions.

A failed arm may already have emitted events or changed ordinary state. No
rollback or retraction is implied. Its internal receipt can contain private
captures, so [artifact disclosure](execution.md#3-artifact-release-is-a-separate-channel)
remains an independent boundary. `authorizedExport` authorizes transfer to the
policy-selected consumer; it does not automatically authorize public release.
Native decoding, identity authentication, storage isolation and serialization
remain realization obligations with these exact meanings.

## 6. Theory choices and current evidence

Outcome-sensitive contracts and framing justify custody after successful and
failed arms. Affine reasoning explains at-most-once use: a right may be abandoned,
but consumption must prevent another use. Here that property is enforced by the
installed service's isolated ledger; an affine type checker or distributed
capability protocol would require its own implementation correspondence.
[Theory](../theory.md#4-communication-resources-and-implementation) places this
choice beside the session and module boundaries.

[Continuation](../../formal/Zkc/Semantics/Continuation.lean) defines `after`;
[ContinuationReport](../../formal/Zkc/Semantics/ContinuationReport.lean) retains
both executions and states the custody frame.
[AuthorizedContinuation](../../formal/Zkc/Semantics/AuthorizedContinuation.lean)
connects source admission, installed service, receipt, ledger and export.
[Integration controls](../../formal/Tests/Integration.lean) exercise failure,
replay, wrong bindings and the separate disclosure projection.

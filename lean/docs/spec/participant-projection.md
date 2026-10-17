# Participant projection

This chapter defines the formal check that a compiler-exported role-local
validator implements the original protocol program at the validator role, and
its composition with the
[transcript-construction rule](fiat-shamir.md#the-rule). The native
[export](../../../docs/spec/formats/constructed-participant.md) supplies the
validator; the [structured import](structured-source.md) supplies the admitted
original program.

## Readings

The original side is the admitted root's participant process at the validator
role, `Program.participant F G validator inputs`: the root body under the
structured semantics with every component outside the role's scopes absent,
with masked outputs. The exported side is the constructed program's interactive
reading `spec` (see [constructed programs](fiat-shamir.md#constructed-programs)):
each challenge is the selected query on a service handle, the observation of a
message the validator sends is its delivery to the producer, and transcript
values are inert histories. Calls name helpers of the original program and are
read with its closed helper table, `helperTable program`.

## Slots

The rule tracks, for every original component in scope, what the exported
program holds for it (`Slot`):

- `absent`: the component is absent at the validator;
- `held r`: the exported value at reference `r` encodes the component;
- `free`: the component is present, and the exported program does not keep it;
- `service`: the component is the replaced challenge service.

The root's input slots hold each published data input at its exported position
and the replaced service as `service`; every other input is absent. The root's
input scopes then mask the slots as the semantics masks the values.

## The rule

`project program context participant` walks the root body in lockstep with the
exported instructions. Before every instruction it consumes, it skips transcript
plumbing, which the interactive reading runs without any action: coordinate
constructions and observations of messages the validator does not send. For each
original operation:

- marks and retained statements have no action and no exported counterpart;
- a restriction keeps its operand's slot when the validator is among its roles,
  and is absent otherwise;
- a calculation of the carrier vocabulary with an absent operand is absent.
  Otherwise the next instruction must be the same calculation on the references
  that hold its operands, with data results; its result is then held. If the next
  instruction is anything else, the calculation is admitted without an exported
  counterpart only when it cannot stop, and its result is `free`;
- a Math helper invocation whose operands are all absent is absent when the
  checked helper's body preserves absence (`absentPreserving`: every operation
  in it reads an operand and is evaluated strictly, so absent inputs give absent
  outputs with no effect or stop); a fold with an absent operand is absent. Other
  Math invocations and folds at the validator are refused (`projection-invoke`,
  `projection-operation`);
- a helper call owned by the validator must be implemented by a call of the
  same checked helper of the original program on the references holding its
  operands, with the helper's data outputs; its results are held. Calls owned by
  other roles are absent;
- a guard owned by the validator must be implemented by a guard on the
  reference holding its condition;
- an exchange must have distinct sender and receiver roles and a scalar type. A
  message from the producer to the validator must be implemented by a receive at
  the same qualified site with the same type; the received value is held. A
  message from the validator to the producer must be implemented by the
  observation of the reference holding it as a message the validator sends at
  the same qualified site, with an admitted occurrence: the delivery of a
  challenge. Exchanges between other roles are absent, and any other exchange
  involving the validator is refused;
- a draw owned by the validator on the replaced service must be implemented by a
  challenge of the same field at the same qualified query site, with an admitted
  occurrence; its answer is held;
- a protocol application in which the validator participates is walked through
  the callee's checked body in the child context (the application's qualified
  site prefix and role substitution), from the argument slots under the callee's
  input masks; its results are the callee's output slots under its output masks.
  The exported program has no instruction for the application itself: the
  callee's instructions are inlined. An application without the validator is
  absent, and an unknown callee is refused (`projection-application`);
- a repeat in which the validator participates must be implemented by the next
  exported loop, at the same qualified site, with the same maximum and with its
  count held at the loop's count operand. The loop's carried values must start
  with the references holding the state components the validator has, in order
  (the others are absent); the remaining carried values are transcript plumbing.
  The loop body is walked once against the repeat body, from slots holding the
  induction index, the carried state and the repeat's captures; after its
  instructions only plumbing may remain, and the yielded references must start
  with the references holding the new state components the validator has. After
  the loop, those components are held at the loop's results
  (`projection-repeat`, `projection-repeat-yield`). A repeat without the
  validator is absent.

After the body, only plumbing may remain, every returned reference must be
bound, and the returned references other than the last (the final transcript)
must hold the validator's outputs in original order. Each refusal names its
obligation (`projection-calculation`, `projection-receive`,
`projection-unexplained`, …).

Helper calls are read with the original program's checked helpers
(`helperTable`). The candidate's prepared helper bodies are not compared with
them by these rules: that a candidate helper computes its original's function is
the native construction check's obligation, which the bridge exercises with a
mutated helper body.

The rule compares operations, not their algebra: a calculation implemented by an
algebraically equal but different calculation is refused. A total calculation
the export omits may be omitted only because its result is never needed: a
later use of a `free` component as an operand, guard condition, message or
output requires a held reference and is refused.

## Soundness

`project_sound` proves, for every accepted export, service handle, data input,
initial transcript and original inputs related to the exported inputs by the
input slots:

```text
spec context handle (helperTable program) returned instructions (data ++ [transcript initial])
    >>= (values ↦ done (dropLast values))
  = (participant validator inputs >>= (outputs ↦ done (validatorOutputs outputs))).interpret project
```

The two processes take the same actions with the same replies, stop at the same
points with the same reasons, and return the same validator outputs. Absent
outputs are omitted; present ones are encoded. The proof is a simulation over
the walk: each accepted operation transports agreement of continuations
(`OperationSound`, `walkStep_sound`), with the invariant that every slot relates
its original component to the exported environment (`Holds`). Helper calls use
the closed helper table's lookup of the checked helper; calculations use the
structured evaluator, and an absence-preserving Math helper's component
evaluation is absent on absent inputs (`absentPreserving_component`). An
application uses the callee's linked body (`protocol_invoke_body`). A repeat is
proved by induction on its iterations (`iterate_projects`): each body iteration
implements one step of the repeat's fold, with the carried values related to the
masked state (`carriedSlots`); a count above the maximum stops both sides with
the same reason. `walk_sound` composes the steps by induction on the walk's
fuel, and the final step reads the returned references through the output
slots.

## Composition with transcript construction

`checkCompiled original program participant` runs `checkExport` (the
transcript-construction rule against the original export) and then `project`
with the derived context. `compiled_transform` composes the two soundness
theorems at the exported program's interactive reading: for every accepted
export, monad, challenge function, service handle, related input, initial
transcript and proof, and for any final selection of the returned values that
agrees with a selection of the validator's outputs,

```text
ideal context challenge (helperTable program) returned instructions (data ++ [transcript initial]) proof
  = transform context challenge (participant validator inputs, read through its outputs) initial proof
```

up to that selection. The construction rule supplies
`ideal = transform ∘ spec` and the projection rule supplies `spec = original`;
the Fiat–Shamir transform is unchanged and applied to the original validator.
The consumer provides the original's admission, `Structured.check original =
.ok program`, which ties the checked program to the export's source digest.

## The compiled Sumcheck proof Entry

`ZkcExamples.Construction.SumcheckProof` checks the compiled `example::Proof`
of the Sumcheck example. Its original export is the admitted Sumcheck source
(`SumcheckSourceData`, rendered from the same bytes by both bridges); its
validator has a protocol application with a repeat, guards and helper calls.
`compiled` runs the composed check in the kernel, and `compiled_transform`
proves, for every challenge function, that the compiled verifier's ideal meaning
is the Fiat–Shamir transform of the original Sumcheck validator, read through
its acceptance output. `compiled_transform_rounds` rewrites the original with
`SumcheckSourceVerifier.verifier_checked`: for an admitted round count and a
decoded verifier table, the transformed process is the source rounds followed by
the multilinear terminal check. No security theorem is claimed for this Entry;
a multi-round Fiat–Shamir bound would be stated about this transform.

## Controls

`Tests.ProjectionControls` runs the composed check on mutations of the actual
compiled Schnorr validator. Each mathematical mutation keeps the transcript
wiring, so `checkExport` accepts it, and each is refused by the projection rule:
the final comparison of the base with itself, the response scaling the
statement, the challenge scaling the base, a sum with the wrong summand, a
comparison with swapped operands, and a constant `true` returned as the decision
(`projection-unexplained`). The other controls are a returned sum instead of the
decision (`construction-final`), a non-Boolean acceptance selection
(`construction-acceptance`), the witness published to the validator
(`construction-context`), a delivery observed as sent by the producer
(`projection-delivery`), a challenge drawn at the delivery site
(`projection-challenge`), a response received at the commitment site
(`projection-receive`), an extra calculation (`projection-unexplained`) and a
truncated program (`projection-outputs`).

`Tests.SumcheckProjectionControls` does the same for the compiled Sumcheck
validator: a dropped round check (`projection-guard`), a round check comparing
the sum with the claim (`projection-guard-operand`), a mutated claim update and
challenge term (`projection-unexplained`), a loop yielding the claim it started
with (`projection-repeat-yield`), a changed loop bound, an unqualified loop site
and a loop starting from the table values (`projection-repeat`), and a terminal
check with swapped operands (`projection-call`). The transcript-construction
rule accepts every one of these mutations.

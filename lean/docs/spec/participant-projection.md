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
  outputs with no effect or stop). When its operands are all present, the
  checked helper's body is walked inline: every operation in it must be a
  carrier calculation, matched as above, and the body's returned slots are the
  invocation's results: the export must inline the helper, and a Math helper
  kept as a call is refused. An invocation with both absent and present operands
  is refused (`projection-invoke`). A fold with an absent operand is absent;
  other folds at the validator are refused (`projection-operation`);
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
  (the others are absent); the remaining carried values are not related to the
  original: the transcript, or data that no matched instruction reads.
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
later use of a `free` component as a guard condition, message, helper argument
or output requires a held reference and is refused, and a total calculation on a
`free` operand can itself only be omitted.

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
points with the same reasons, and return the same validator outputs. Outputs
outside the validator's scopes are omitted; the others are encoded as optional
values. The proof is a simulation over
the walk: each accepted operation transports agreement of continuations
(`OperationSound`, `walkStep_sound`), with the invariant that every slot relates
its original component to the exported environment (`Holds`). Helper calls use
the closed helper table's lookup of the checked helper; calculations use the
structured evaluator, an absence-preserving Math helper's component
evaluation is absent on absent inputs (`absentPreserving_component`), and an
inlined helper body is related to the helper's component evaluation by its own
walk (`walkHelper_sound`). An
application uses the callee's linked body (`protocol_invoke_body`). A repeat is
proved by induction on its iterations (`iterate_projects`): each body iteration
implements one step of the repeat's fold, with the carried values related to the
masked state (`carriedSlots`); a count above the maximum stops both sides with
the same reason. `walk_sound` composes the steps by induction on the walk's
fuel, and the final step reads the returned references through the output
slots.

## Composition with transcript construction

`checkCompiled imported participant` takes an admitted original,
`imported : Structured.Imported original`: the program together with the proof
`Structured.check original = .ok program`. It runs `checkExport` (the
transcript-construction rule against the original snapshot) and then `project`
against `imported.program` with the derived context. Both rules therefore read
the same original: a program admitted from another snapshot cannot be paired
with this snapshot's export. `compiled_transform` composes the two soundness
theorems at the exported program's interactive reading: for every export
accepted against an admitted original, monad, challenge function, service
handle, related input, initial transcript and proof, and for any final
selection of the returned values that agrees with a selection of the
validator's outputs,

```text
ideal context challenge (helperTable program) returned instructions (data ++ [transcript initial]) proof
  = transform context challenge (participant validator inputs, read through its outputs) initial proof
```

up to that selection, where `program` is `imported.program`. The construction
rule supplies `ideal = transform ∘ spec` and the projection rule supplies
`spec = original`; the Fiat–Shamir transform is unchanged and applied to the
original validator. The admission ties the checked program to the snapshot and
so to the export's source digest.

The equation leaves three positional premises to each Entry: where the export
returns its acceptance output, how its data inputs hold the original validator's
inputs, and how many data inputs there are. `select imported participant`
constructs that selection from the admitted original and the export's policy:
the derived context, the acceptance output's position among the returned values,
the types of the published inputs in policy order, the validator's input slots
and its acceptance output. `Selection.check` validates it against the export
(the acceptance output precedes the final transcript, every slot holds a
published value of its type, the replaced service or nothing, and the acceptance
output is the validator's output at that position), and `selection_sound`
proves the three premises from an accepted check. `compiled_selected` then
states the equation for every list of published values of the selected types,
read through the acceptance output on both sides, with no positional fact about
the Entry.

## Reading exported programs

`Zkc.Construction.Reading` gives general laws of the interactive reading `spec`
itself. Observations and challenges extend transcript values as inert
histories, and no action, stop or data value reads one, so environments that
agree except for transcript histories (`Similar`) give the same reading for
continuations that also ignore histories (`specK_similar`). A loop whose body
reads, on the encoding of every valid state at its induction index, as one step
of a plain process followed by the encoding of the step's result reads as that
many repeated steps (`iterate_repeatN`, `iterate_range_repeatN`), whatever
histories its yielded transcript values carry; `Yields` states what every
result of a plain step satisfies, which the loop laws may assume of earlier
steps. `specK_append` reads concatenated instruction lists in sequence. With
`spec_transform`-style uses of the construction rule these laws relate an
export's reading to a plain verifier directly, without the projection rule.

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
the multilinear terminal check. `ZkcSecurity.Examples.CompiledSumcheckFiatShamir`
composes this equation with the multi-round Fiat–Shamir soundness of the
imported verifier's transform
([multi-round security](fiat-shamir-security.md#the-compiled-sumcheck-proof-entry)):
the compiled verifier's ideal interpretation accepts a false claim with
probability at most `(Q + count) / |F|` for a fixed statement, and adaptively
chosen statements are bounded under a binding that determines them.

## The compiled composed Sumcheck proof Entry

`ZkcExamples.Construction.ComposedSumcheckProof` checks the compiled
`example::Proof` of `examples/projects/sumcheck/composed`. Its `TwoSums`
protocol applies the Sumcheck `Reduce` protocol at two sites, each with its own
repeat and both drawing from one challenge service, then runs two terminal
checks and conjoins them with the Math helper `zkc::boolean::both`, which the
compiler inlines as a Boolean conjunction. Its original is admitted from the
typed bodies printed from the admitted snapshot (`admitted`), the composed check
accepts the export (`compiled`) and the selection check accepts it
(`selection_checked`), so `compiled_transform` is `compiled_selected` at the
Entry's published inputs and acceptance output: no proof is specific to the
Entry. No security theorem is stated for this Entry.

## The compiled Sigma proof Entries

`ZkcExamples.Construction.SchnorrAndProof` and
`ZkcExamples.Construction.ChaumPedersenProof` check the compiled
`example::AndProof` and `example::EqualityProof` of `examples/projects/sigma`:
two Schnorr statements with independent witnesses and one shared challenge, and
one witness for two bases. Both validators receive two commitments, take one
challenge, receive the responses (two for AND, one for Chaum–Pedersen) and
conjoin two checked equations. Each original is admitted from typed bodies
printed by `bridges/structured/bodies.py` and checked by `structured_views` in
the kernel, so its entry types are literal. The composed check accepts the
export (`compiled`), and `compiled_transform` instantiates the generic theorem
at the Entry's public inputs and acceptance output (`inputs_related`,
`acceptance_decision`), as for Schnorr, with no equation about the program's
meaning specific to the Entry. The Fiat–Shamir theorems of the Sigma
compositions are about the transforms of the imported interactive verifiers; no
security theorem is stated for these compiled Entries.

## The compiled GKR proof Entry

`ZkcExamples.Construction.GkrProof` checks the compiled `example::Proof` of
`examples/projects/gkr`. Its original export is the admitted GKR source
(`GkrSourceData`); the whole unit, honest prover included, is admitted from
typed bodies by `structured_views` in the kernel. The validator has an
output-point loop and a layer loop whose body holds three inner loops, the two
`Rounds` applications and the line coefficients, with guards for the round and
wiring checks and helper calls for the extensions, blocks, line point and power
sum. `compiled` runs the composed check in the kernel, and `compiled_transform`
is the generic equation at the Entry's public inputs and acceptance output, as
for Sumcheck. `spec_transform` uses the transcript-construction rule alone: the
compiled meaning is the Fiat–Shamir transform of the interactive reading of the
exported instructions, read through the acceptance output. `GkrProof.reading`
(module `GkrProofReading`) proves that reading, on a well-formed statement,
equal to the plain GKR verifier, which
`ZkcSecurity.Examples.CompiledGkrFiatShamir` bounds
([multi-round security](fiat-shamir-security.md#the-compiled-gkr-proof-entry)).

## The compiled guessing proof Entry

`ZkcExamples.Construction.GuessProof` checks the compiled `example::Proof` of
the construction bridge's fixture `lean/bridges/construction/fixtures/guess.zkc`:
the validator receives a guess, takes a field challenge, delivers it and returns
whether the guess plus the public offset is the challenge. Its original is
admitted from typed bodies by `structured_views` in the kernel, the composed
check accepts the export (`compiled`), and `compiled_transform` is the generic
equation at the Entry's public offset and acceptance output, as for Schnorr. The
original validator is the four-operation participant process `experiment`, by
computation (`verifier_correspondence`).
`ZkcSecurity.Examples.CompiledGuessFiatShamir` bounds the compiled verifier by a
certificate imported from an ArkLib verifier
([imported certificates](fiat-shamir-security.md#imported-certificates-for-compiled-verifiers)).

## Controls

`Tests.ProjectionControls` runs the composed check on mutations of the actual
compiled Schnorr validator. Each mathematical mutation keeps the transcript
wiring, so `checkExport` accepts it, and each is refused by the projection rule:
the final comparison of the base with itself, the response scaling the
statement, the challenge scaling the base, a sum with the wrong summand, a
comparison with swapped operands, and a constant `true` returned as the decision
(`projection-unexplained`). The other controls are a returned sum instead of the
decision (`construction-final`), an acceptance selection of an output the
validator does not have (`construction-acceptance`), the witness published to the validator
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
rule accepts every one of these mutations. The same module exercises that rule's
deployment checks inside the loop: coordinates without the induction index and a
template without its repeat step (`construction-observe`), coordinates appending
a non-index value (`construction-coordinates`), and a loop count, guard or call
reading the wrong sort (`construction-loop`, `construction-guard`,
`construction-call`). The construction bridge also refuses
mutations of the composed export: a conjunction reading the left check twice
(`projection-unexplained`) and a right terminal check reading the left
reduction's point and claim (`projection-call`); and of both Sigma exports: the
second commitment's observation absorbing the first commitment
(`construction-observe`), a comparison of a base with itself and a conjunction
reading the first check twice (`projection-unexplained`). For the GKR export it refuses a
dropped first round check and a dropped wiring check (`projection-guard`), a
mutated round claim update (`projection-unexplained`), a layer loop yielding the
claim it started with (`projection-repeat-yield`) and a challenge origin naming
the delivery site (`construction-challenge-site`).

`Tests.ProjectionControls` also shows why the composed check takes an admitted
original. Changing the original Schnorr root's final comparison into a
comparison of the sum with itself gives a snapshot that still admits; its
program and a candidate whose decision compares the sum with itself pass the
construction rule against the unchanged snapshot and the projection rule
against the altered program (`unlinked_accepts_mixed`), and the altered pair
passes the composed check against its own snapshot (`altered_accepted`). The
unchanged snapshot does not admit the altered program (`mixed_unadmitted`), so
every admitted subject of the unchanged snapshot is the actual program
(`subject_unique`) and refuses the altered candidate (`mixed_refused`,
`projection-unexplained`).

`Tests.SigmaProofControls` evaluates the compiled Sigma verifiers in the kernel
over `ZMod 3`: each accepts an honest proof exactly at the challenge it answers,
rejects a wrong response and stops with a refusal on a truncated proof, so the
instantiated `compiled_transform` equations are not about verifiers that always
stop.

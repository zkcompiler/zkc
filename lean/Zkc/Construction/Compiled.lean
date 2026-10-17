module

public import Zkc.Construction.ProjectionSoundness

@[expose] public section

/-! Composition of the construction and projection rules.

`checkCompiled` runs the transcript-construction rule and the participant
projection rule on one exported validator. `compiled_transform` composes their
soundness theorems: the compiled validator's ideal meaning is the Fiat–Shamir
transform of the original validator's participant process, read through
matching selections of their results. The two rules meet at the exported
program's interactive reading (`spec`): the construction rule relates it to the
ideal meaning and the projection rule to the original.
-/

set_option autoImplicit false

namespace Zkc.Construction
open Zkc.Source Zkc.Source.Structured

/-- The composed per-compile check of a compiled validator: the
transcript-construction rule, then the participant projection rule on the
same export, against the admitted original. -/
def checkCompiled (original : Structured.Snapshot) (program : Structured.Program)
    (participant : Participant) : Except String Unit :=
  match checkExport original participant, exportContext original participant with
  | .ok (), some context => project program context participant
  | .error error, _ => .error error
  | .ok (), none => .error "construction-context"

/-- The checked export's data inputs are the published inputs. -/
theorem exportContext_published {original : Structured.Snapshot} {participant : Participant}
    {context : Context} (found : exportContext original participant = some context) :
    participant.inputs.dropLast.length = participant.policy.publicInputs.length := by
  unfold exportContext at found
  simp only at found
  split at found
  · split at found
    · split at found
      · split_ifs at found with conditions
        have lengths := congrArg List.length conditions.2.2.2
        simpa using lengths
      · cases found
    · cases found
  · cases found

/-- An accepted export has a final transcript input. -/
theorem check_inputs_nonempty (context : Context) (participant : Participant)
    (checked : check context participant = .ok ()) : participant.inputs ≠ [] := by
  intro empty
  simp [check, empty] at checked

section Compiled
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- What one final selection of the returned values may observe: two readings
agree on every returned list of the declared length. -/
theorem spec_bind_congr (context : Context) (handle : Nat) (table : Structured.Meanings F G)
    (returned : List Nat) (instructions : List Instruction) (env : List (Value F G)) {B : Type}
    (first second : List (Value F G) → B)
    (agree : ∀ values, values.length = returned.length → first values = second values) :
    (spec context handle table returned instructions env).bind (fun values => .done (first values)) =
      (spec context handle table returned instructions env).bind (fun values => .done (second values)) := by
  simp only [spec, specK_bind]
  congr 1
  funext final
  cases found : read final returned with
  | none => rfl
  | some values =>
    simp only [PIR.Proc.bind]
    rw [agree values (read_length found)]

/-- The composed rules: for every accepted export, the compiled validator's ideal
meaning, read through a selection of its returned values, is the Fiat–Shamir
transform of the original validator's process read through the matching
selection of its outputs, for every challenge function, service handle, data
input related to the original inputs, initial transcript and proof. -/
theorem compiled_transform (original : Structured.Snapshot) (program : Structured.Program)
    (participant : Participant) (accepted : checkCompiled original program participant = .ok ()) :
    ∃ context, exportContext original participant = some context ∧
      ∀ {m : Type → Type} [Monad m] [LawfulMonad m] {B : Type} (challenge : History F G → m F)
        (select : List (Value F G) → B) (decide : List (Option (Value F G)) → B),
        (∀ values, values.length = participant.returned.length →
          select values = decide (values.dropLast.map some)) →
        ∀ (handle : Nat) (data : List (Value F G)) (initial : History F G) (proof : Proof F G)
          (inputs : Values (Component (assignment F G)) program.payload.entry.inputs),
          HoldsValues handle (data ++ [.transcript initial])
            (inputSlots context participant.policy program.payload.entry.inputs) inputs →
          data.length = participant.policy.publicInputs.length →
          (fun result => (mapOutcome select result.1, result.2)) <$>
              ideal context challenge (helperTable program F G) participant.returned
                participant.instructions (data ++ [.transcript initial]) proof =
            transform context challenge
              (((program.participant F G context.validator inputs).bind fun outputs =>
                .done (decide (validatorOutputs context.validator program.payload.entry.outputScopes
                  outputs))).interpret CommonAdapter.project) initial proof := by
  unfold checkCompiled at accepted
  split at accepted
  · rename_i context exported found
    refine ⟨context, found, ?_⟩
    intro m _ _ B challenge select decide agree handle data initial proof inputs related arity
    obtain ⟨context', found', checked⟩ := checkExport_sound exported
    rw [found] at found'
    cases found'
    have inputsArity : data.length + 1 = participant.inputs.length := by
      have published := exportContext_published found
      have nonempty := check_inputs_nonempty context participant checked
      have positive : 0 < participant.inputs.length := List.length_pos_iff.mpr nonempty
      simp only [List.length_dropLast] at published
      omega
    rw [check_sound context challenge handle (helperTable program F G) participant checked data initial
      proof inputsArity, ← transform_bind_done]
    congr 1
    rw [spec_bind_congr context handle (helperTable program F G) participant.returned
      participant.instructions _ select (fun values => decide (values.dropLast.map some)) agree]
    have projected := project_sound program context participant accepted handle data initial inputs
      related arity
    have composed := congrArg (fun process => process.bind fun options => .done (decide options))
      projected
    simp only [PIR.Proc.bind_assoc, PIR.Proc.bind] at composed
    rw [composed, PIR.Proc.interpret_bind, PIR.Proc.interpret_bind, PIR.Proc.bind_assoc]
    congr 1
  · cases accepted
  · cases accepted

end Compiled


end Zkc.Construction

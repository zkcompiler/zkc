module

public import Zkc.Executable.DomainSchema

@[expose] public section

/-! Relate the checked participant boundary to a schedule's returned values.
The output schema is finite syntax. Its proof uses the declarations enforced
by actual Domain execution, for all replies and all stopped paths. -/
set_option autoImplicit false
namespace Zkc.Executable.DomainVM
open Zkc.Construction Zkc.Source

private theorem read_sorts {carriers : Structured.Carriers}
    (env : Domain.Environment carriers) : ∀ (references : List Nat)
    (values : Domain.Environment carriers), Domain.read env references = some values →
      references.mapM ((env.map Domain.Value.sort)[·]?) = some (values.map Domain.Value.sort)
  | [], values, found => by
      simp only [Domain.read, List.mapM_nil, Option.pure_def, Option.some.injEq] at found
      subst values
      rfl
  | reference :: references, values, found => by
      simp only [Domain.read, List.mapM_cons] at found
      cases head : env[reference]? with
      | none => simp [head] at found
      | some value =>
          cases tail : Domain.read env references with
          | none => simp [Domain.read] at tail; simp [head, tail] at found
          | some rest =>
              have tail' := tail
              simp only [Domain.read] at tail'
              simp [head, tail'] at found
              subst values
              have remaining := read_sorts env references rest tail
              simp only [List.getElem?_map] at remaining
              simp [List.getElem?_map, head, remaining]

/-- The static selected references have the declared output schema. -/
def ReturnSchema (artifact : Participant) : Prop :=
  artifact.returned.mapM ((artifact.inputs ++ artifact.instructions.flatMap Instruction.results)[·]?) =
    some artifact.outputs

instance (artifact : Participant) : Decidable (ReturnSchema artifact) :=
  inferInstanceAs (Decidable (_ = _))

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- All result declarations are checked by Domain itself. Selecting typed
return positions therefore cannot introduce an extra output-schema refusal. -/
theorem participant_values (program : Structured.Program) (context : Context)
    (artifact : Participant) (env : Environment F G)
    (inputs : env.map Domain.Value.sort = artifact.inputs) (outputs : ReturnSchema artifact) :
    (Domain.participant (Structured.ringModel F G) program context artifact env).bind
        (fun result => .done result.values) =
      .call (.checkpoint env) (fun _ => outcome program context artifact.instructions artifact.returned env) := by
  have inputMatch : Domain.sortsMatch artifact.inputs env = true := by
    simp [Domain.sortsMatch, inputs]
  simp only [Domain.participant, inputMatch, ite_true, PIR.Process.bind, PIR.Process.bind_assoc]
  congr 1
  funext _
  unfold outcome
  apply (evaluate_schema (Structured.ringModel F G) program context artifact.instructions env).bind_congr
  intro final schema
  cases found : Domain.read final artifact.returned with
  | none => simp [found, readback, PIR.Process.bind]
  | some values =>
      have selected := read_sorts final artifact.returned values found
      rw [schema, inputs] at selected
      have sorted : values.map Domain.Value.sort = artifact.outputs :=
        Option.some.inj (selected.symm.trans outputs)
      simp [found, readback, Domain.sortsMatch, sorted, PIR.Process.bind]

/-- The reusable unmetered seam between native schedule normalization and the
actual selected participant. Only administrative checkpoints are forgotten. -/
theorem participant_observation (program : Structured.Program) (context : Context)
    (artifact : Participant) (env : Environment F G)
    (inputs : env.map Domain.Value.sort = artifact.inputs) (outputs : ReturnSchema artifact) :
    ((Domain.participant (Structured.ringModel F G) program context artifact env).bind
        (fun result => .done result.values)).interpret Original.forgetCheckpoints =
      observation program context artifact.instructions artifact.returned env := by
  rw [participant_values program context artifact env inputs outputs]
  rfl

end Zkc.Executable.DomainVM

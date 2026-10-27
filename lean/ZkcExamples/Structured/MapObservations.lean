module

public import Zkc.Source.Structured.Participant

@[expose] public section

/-! Reference observations of the scoped map examples: one retained callback
mark per reached row, erased only by the participant interpretation. -/
namespace ZkcExamples.Structured.MapObservations
open Zkc.Source.Structured

variable {F G A B : Type}

def rows (values : List A) : PIR.Process (observedInterface F G) (List A) :=
  values.mapM fun value => .call (.mark "body") fun _ => .done value

theorem rows_nil : rows (F := F) (G := G) ([] : List A) = .done [] := rfl

theorem rows_cons (value : A) (values : List A) :
    rows (F := F) (G := G) (value :: values) =
      .call (.mark "body") fun _ =>
        (rows values).bind fun rest => .done (value :: rest) := by
  simp only [rows, List.mapM_cons]
  rfl

theorem rows_map (values : List A) (formula : A → B) :
    (values.mapM fun value =>
      (PIR.Process.call (.mark "body") fun _ => .done (formula value) :
        PIR.Process (observedInterface F G) B)) = rows (values.map formula) := by
  simp only [rows, List.mapM_map, Function.comp_def]

theorem rows_forget (values : List A) :
    (rows (F := F) (G := G) values).interpret forgetSites = .done values := by
  induction values with
  | nil => rfl
  | cons value values ih =>
    rw [rows_cons]
    simp only [PIR.Process.interpret, forgetSites, PIR.Process.bind,
      PIR.Process.interpret_bind, ih]

end ZkcExamples.Structured.MapObservations

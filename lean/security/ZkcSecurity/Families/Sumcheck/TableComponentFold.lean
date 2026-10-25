module

public import Zkc.Source.Structured.Laws

@[expose] public section

/-! A reusable arithmetic law for source finite sums. All retained helper
names and the actual step equation are explicit parameters. The theorem uses
the existing structured fold semantics and counts its checked index bound.
-/

set_option autoImplicit false
namespace ZkcSecurity.Families.Sumcheck.TableComponent
open Zkc.Source Zkc.Source.Structured

def sumFold (field domain step : String) : FoldSpec :=
  ⟨⟨domain, [.vector field], (.vector field), .here, false⟩, [.field field], [], step, "", .math⟩

variable {F G : Type} [CommRing F]

theorem fold_values_sum (field : String) (raw : List F) (initial : F) :
    raw.foldl (fun (state : Values (assignment F G) [.field field]) value =>
      Values.cons (state.get .here + value) .nil) (.cons initial .nil) =
      .cons (initial + raw.sum) .nil := by
  induction raw generalizing initial with
  | nil => simp
  | cons value rest ih =>
      simpa only [List.foldl_cons, Values.get, List.sum_cons, add_assoc]
        using ih (initial + value)

set_option backward.isDefEq.respectTransparency false in
theorem sumFold_equation (table : Meanings F G)
    (field domain step : String) (raw : List F) (initial : F)
    (bounded : raw.length < indexLimit)
    (stepLaw : ∀ (a value : F), invoke table (sumFold field domain step).stepHelper
      (.cons a (.cons value (.cons raw .nil))) = .done (.cons (a + value) .nil)) :
    Evaluation.denoteFold table (sumFold field domain step)
      ((Values.cons raw .nil).append ((Values.cons initial .nil).append .nil)) =
      .done (.cons (initial + raw.sum) .nil) := by
  have admitted : ((sumFold field domain step).domain.denote (Values.cons raw
      (Values.nil : Values (assignment F G) []))).admit = .returned raw := by
    change (Finite.Domain.check (raw.length < indexLimit) .exhausted (.elements raw)).admit = _
    simp [Finite.Domain.admit, bounded]
  have folded := Evaluation.denoteFold_reference table (sumFold field domain step)
    (.cons raw .nil) (.cons initial .nil) .nil raw admitted
    (fun (state : Values (assignment F G) [.field field]) (value : F) =>
      Values.cons (state.get .here + value) .nil) (fun _ => True) trivial (by
      intro state value _ _
      cases state with | cons a rest => ?_
      cases rest
      constructor
      · exact (Evaluation.foldTransition_unfiltered _ (sumFold field domain step) rfl _ _ _ _).trans
          (stepLaw a value)
      · trivial)
  exact folded.trans (congrArg PIR.Process.done (fold_values_sum field raw initial))

end ZkcSecurity.Families.Sumcheck.TableComponent

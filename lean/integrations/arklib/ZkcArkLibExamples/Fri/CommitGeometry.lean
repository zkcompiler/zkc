module

public import ZkcArkLibExamples.Fri.RetainedFold
public import Zkc.Source.Structured.NumericalFold
public import Zkc.Source.Structured.ReferenceLibrary

@[expose] public section

/-! Arithmetic used to construct a virtual word in the admitted Commit
round. Each equation selects the checked helper in its actual linked table. -/
set_option autoImplicit false
namespace ZkcSecurity.ArkLib.Fri.CommitGeometry
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
open FriSourceBodies FriSourceViews
open ZkcSecurity.Domains.KoalaBear (Octic)
open ZkcSecurity.Domains.KoalaBearModel (model octicIdentity inverse_octic)

private def rootLaw := ReferenceLibrary.marked model "s0" (ReferenceLibrary.execute model
  (inputs := helper3Helper.inputs) (.numerical .polyRoot octicIdentity "") (.cons .here .nil))

private def inverseLaw := ReferenceLibrary.marked model "s0" (ReferenceLibrary.execute model
  (inputs := helper4Helper.inputs) (.numerical .fieldInverse octicIdentity "") (.cons .here .nil))

theorem generator {I : PIR.Signature} (k : Nat) (bound : k ≤ 5) :
    invoke (RetainedFold.helpers (I := I)).closed helper3Helper (.cons (2 ^ k) .nil) =
      .done (.cons (RetainedDomain.root k) .nil) := by
  refine (rootLaw.invokeOn unit.definitions unit.linked
    (helper := helper3Helper) (by exact_body helper3Definition) _ trivial).trans ?_
  have size : 2 ^ k < indexLimit := lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) bound)
    (show 2 ^ 5 < indexLimit by decide)
  let field := {model.toFieldModel with inverse := fun _ ↦ none}
  have checked : Numerical.checkValues field (.cons (ty := .index) (2 ^ k) .nil) = .ok () := by
    change (Numerical.require (2 ^ k < indexLimit) >>= fun _ ↦ Except.ok ()) = _
    rw [show Numerical.require (2 ^ k < indexLimit) = .ok () from ite_eq_left size]
    rfl
  change primitiveOutcome (Numerical.checkedEvaluateOn field octicIdentity "" .polyRoot
    (.cons (2 ^ k) .nil)) = _
  unfold Numerical.checkedEvaluateOn
  erw [checked]
  have selected : Numerical.domainRoot field octicIdentity (2 ^ k) = .ok (RetainedDomain.root k) :=
    (Numerical.domainRoot_with_inverse _ _ _ _).trans (RetainedDomain.domainRoot k bound)
  change primitiveOutcome (Numerical.evaluateOn field octicIdentity "" .polyRoot (.cons (2 ^ k) .nil)) = _
  simp only [Numerical.evaluateOn, selected, bind, Except.bind, pure, Except.pure]
  rfl

theorem inverse {I : PIR.Signature} (x : Octic) (nonzero : x ≠ 0) :
    invoke (RetainedFold.helpers (I := I)).closed helper4Helper (.cons x .nil) =
      .done (.cons (x⁻¹ : Octic) .nil) := by
  refine (inverseLaw.invokeOn unit.definitions unit.linked
    (helper := helper4Helper) (by exact_body helper4Definition) _ trivial).trans ?_
  have computes := Numerical.inverse_eq model.toFieldModel octicIdentity
    (fun y : Octic ↦ (y⁻¹ : Octic)) inverse_octic x nonzero
  change primitiveOutcome (Numerical.finish (Numerical.inverse model.toFieldModel octicIdentity x
    >>= fun y ↦ Except.ok (Values.cons (Value := model.Value) (ty := .field octicIdentity) y .nil))) = _
  rw [computes]
  rfl

theorem challenge {I : PIR.Signature} (beta : Octic) :
    invoke (RetainedFold.helpers (I := I)).closed helper6Helper (.cons beta .nil) =
      .done (.cons beta .nil) :=
  (ReferenceLibrary.projection model (inputs := helper6Helper.inputs) (.cons .here .nil)).invokeOn
    unit.definitions unit.linked (helper := helper6Helper) (by exact_body helper6Definition) _ trivial

end ZkcSecurity.ArkLib.Fri.CommitGeometry

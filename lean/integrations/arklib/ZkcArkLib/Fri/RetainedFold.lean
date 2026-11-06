module

public import ZkcArkLib.Fri.RetainedDomain
public import ZkcArkLib.Fri.SourceCalculations
public import ZkcExamples.Structured.FriApplications
public import Zkc.Source.Structured.ReferenceLaws
public import Zkc.Source.Structured.WordDerivation

@[expose] public section

/-! Mathematical presentations of the retained pair selection and fold.
Their associations refer to the actual checked helpers used by the virtual
oracle. Each law uses the common structural constructor. -/
set_option autoImplicit false
namespace ZkcSecurity.ArkLib.Fri.RetainedFold
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
open FriSourceBodies FriSourceViews
open ZkcSecurity.Domains.KoalaBearModel (model)
open ZkcSecurity.Domains.KoalaBear (Octic)

theorem pairResult (model : DomainModel)
    (table : Evaluation.MeaningsOn model.toCarriers closedInterface) (position rows : Nat) :
    helper14Body.denote (Evaluation.meaningOn model SiteObservations.closed table)
      (Values.cons (Value := model.Value) (ty := .index) position (.cons rows .nil)).get =
      .done (.cons (bitAnd position (wrappingSubtract (logicalShiftRight rows 1) 1)) .nil) := by
  derive_word_process

def pairLaw (model : DomainModel) : ReferenceLaw model helper14Helper.inputs helper14Helper.outputs where
  body := helper14Body
  Requires _ _ := True
  reference
    | .cons position (.cons rows .nil) => .returned (.cons
        (bitAnd position (wrappingSubtract (logicalShiftRight rows 1) 1)) .nil)
  valid table
    | .cons position (.cons rows .nil), _ => pairResult model table position rows

def foldLaw (model : DomainModel) : ReferenceLaw model helper15Helper.inputs helper15Helper.outputs where
  body := helper15Body
  Requires _ _ := True
  reference
    | .cons low (.cons high (.cons beta (.cons inverseTwo (.cons inverseX .nil)))) =>
      .returned (.cons (((low + high : model.Field FriSource.extension) * inverseTwo +
        beta * (low - high) * inverseTwo * inverseX)) .nil)
  valid _
    | .cons _ (.cons _ (.cons _ (.cons _ (.cons _ .nil)))), _ => by derive_process

abbrev helpers {I : PIR.Signature} :=
  unit.definitions.foldl (Evaluation.ComponentTablesOn.extend model (.silent I)) ⟨[], []⟩

theorem pair_index {I : PIR.Signature} {m : Nat} (small : m + 1 ≤ 63)
    (position : Fin (2 ^ (m + 1))) :
    invoke (helpers (I := I)).closed helper14Helper (.cons position.val (.cons (2 ^ (m + 1)) .nil)) =
      .done (.cons (position.val % 2 ^ m) .nil) := by
  have bounded : 2 ^ (m + 1) < wordModulus := Nat.pow_lt_pow_right (by decide) (by omega)
  have call := (pairLaw model).invokeOn (I := I) unit.definitions unit.linked
    (helper := helper14Helper) (by exact_body helper14Definition)
    (.cons position.val (.cons (2 ^ (m + 1)) .nil)) trivial
  exact call.trans (congrArg (fun i ↦ PIR.Process.done (I := I)
    (Values.cons (Value := model.Value) (ty := .index) i .nil))
    (machine_pair_low position.val m small (position.isLt.trans bounded)))

/-- At every admissible pair, invoking the installed helper returns the
ArkLib folded cell for the selected natural-order coset. -/
theorem folded_cell {I : PIR.Signature} {m : Nat}
    (domain : Domain.SmoothCosetFftDomain (m + 1) Octic) (shift : Octic)
    (geometry : ∀ i : Fin (2 ^ (m + 1)), domain i = point RetainedDomain.root shift (m + 1) i)
    (word : Fin (2 ^ (m + 1)) → Octic) (beta : Octic) (low : Fin (2 ^ m)) :
    invoke (helpers (I := I)).closed helper15Helper (.cons (word (lowIndex low))
      (.cons (word (highIndex low)) (.cons beta (.cons ((2 : Octic)⁻¹ : Octic)
        (.cons ((shift⁻¹ * (RetainedDomain.root (m + 1))⁻¹ ^ low.val) : Octic) .nil))))) =
        .done (.cons (ProximityGap.foldWord domain word 1 beta low) .nil) := by
  have call := (foldLaw model).invokeOn (I := I) unit.definitions unit.linked
    (helper := helper15Helper) (by exact_body helper15Definition)
    (.cons (word (lowIndex low)) (.cons (word (highIndex low)) (.cons beta
      (.cons ((2 : Octic)⁻¹ : Octic) (.cons ((shift⁻¹ * (RetainedDomain.root (m + 1))⁻¹ ^ low.val) : Octic) .nil))))) trivial
  exact call.trans (congrArg (fun x : Octic ↦ PIR.Process.done (I := I)
    (Values.cons (Value := model.Value) (ty := .field FriSource.extension) x .nil))
    (prepared_inverse_fold RetainedDomain.root domain shift geometry word beta low))

end ZkcSecurity.ArkLib.Fri.RetainedFold

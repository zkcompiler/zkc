import Zkc.Source.DeriveRegion
import Zkc.Source.RegionView
import Zkc.Source.Structured.ProjectedBody
import Zkc.Source.Structured.DerivationRules
import Zkc.Source.Structured.EqualityDerivationRules
import ZkcExamples.Structured.SumcheckSourceViews

/-! Automation clients of maintained admitted bodies. No source operation tree
is restated here. The generated target uses a nondefinitional addition rewrite. -/
set_option smartUnfolding false

namespace Tests.DeriveRegionSources
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured

/-- Direct projection and its association need no second digest-named body. -/
def sumAdd := SumcheckSourceViews.program.payload.definitions[0]'(by decide)

theorem sum_add_is_actual : sumAdd = SumcheckSourceViews.sumAddDefinition := rfl

def sumAddView : Region dialect sumAdd.inputs sumAdd.outputs := region_view% sumAdd.body

theorem sum_add_view_exact : sumAddView = sumAdd.body := rfl

theorem sum_add_association :
    BodyIn SumcheckSourceViews.program.payload.definitions sumAdd.helper sumAdd.body := by
  exact BodyIn.of_checked SumcheckSourceViews.sumAddDefinition (by structured_mem)

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- Reuse the local scalar law on the actual admitted Sumcheck helper. -/
theorem sum_add_reversed (table : Meanings F G) (a b : F) :
    Region.Derivation (meaning F G table) (fun op => .call op .done) sumAdd.body
      (Values.cons a (.cons b .nil)).get (.done (.cons (b + a) .nil)) := by
  derive_region using (exact fieldAdd_reverse_law _ _ _ _ _)

end Tests.DeriveRegionSources

namespace Tests.DeriveRegionSources
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
set_option maxRecDepth 20000 in
private theorem sumBodies :
    SumcheckRelationContract.Bodies SumcheckSourceViews.program.payload.definitions where
  add := by exact_body SumcheckSourceViews.sumAddDefinition
  step := by exact_body SumcheckSourceViews.sumStepDefinition
  total := by exact_body SumcheckSourceViews.sumTotalDefinition

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- The bounded fold is supplied as an explicit local call law. -/
private theorem sumTotal_law (xs : List F) (bounded : xs.length < indexLimit) :
    (meaning F G (closedMeanings SumcheckSourceViews.program.payload.definitions)).OperationLaw
      (fun op => .call op .done) (.invoke SumcheckRelationContract.totalHelper)
      (.cons xs .nil) .nil (.done (.cons xs.sum .nil)) := by
  apply RegionMeaning.OperationLaw.identity
  exact SumcheckRelationContract.total_equation
    SumcheckSourceViews.program.payload.linked sumBodies xs bounded

/-- A mathematical callee law summarizes the fold. The caller spine is derived
from the actual checked formula; neither it nor the fold is copied. -/
theorem sum_formula_automated (xs : List F) (claim : F) (bounded : xs.length < indexLimit) :
    Region.Derivation
      (meaning F G (closedMeanings SumcheckSourceViews.program.payload.definitions))
      (fun op => .call op .done) SumcheckSourceViews.sumFormulaDefinition.body
      (Values.cons xs (.cons claim .nil)).get (.done (.cons (decide (claim = xs.sum)) .nil)) := by
  derive_region using (first
    | exact sumTotal_law xs bounded
    | (apply RegionMeaning.OperationLaw.identity; rfl))

/-- The same equality orientation used by the real Schnorr helper is reused at
this actual scalar comparison, after the explicit bounded fold summary. -/
theorem sum_formula_reversed (xs : List F) (claim : F) (bounded : xs.length < indexLimit) :
    Region.Derivation
      (meaning F G (closedMeanings SumcheckSourceViews.program.payload.definitions))
      (fun op => .call op .done) SumcheckSourceViews.sumFormulaDefinition.body
      (Values.cons xs (.cons claim .nil)).get (.done (.cons (decide (xs.sum = claim)) .nil)) := by
  derive_region using (first
    | exact sumTotal_law xs bounded
    | exact fieldEqual_reverse_law _ _ _ _ _)

end Tests.DeriveRegionSources

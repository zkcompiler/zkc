module

public import ZkcExamples.Structured.SumcheckContractBindings

@[expose] public section

/-! Exhaustive interpretations of the two selected maintained declarations.
A formula law does not assert that a runtime output satisfies the formula.
In particular, false-claim soundness is probabilistic, and the input clause is
not assumed true in that experiment. Residual discharge stays an external request.
-/
namespace ZkcExamples.Structured.SumcheckContractInterpretations
open Zkc.Source Zkc.Source.Structured SumcheckContractBindings

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

variable {sourceEnvironment : RelationEnvironment SumcheckSourceViews.imported F G}
variable {reductionEnvironment : RelationEnvironment SumcheckReduceViews.imported F G}

def publicContract : ContractInterpretation publicOwner F G sourceEnvironment where
  subjects
    | ⟨0, _⟩ => inputShape
    | ⟨1, _⟩ => publicTarget
    | ⟨index + 2, bound⟩ => by
      change index + 2 < 2 at bound
      omega
  residuals index residual selected := by
    rcases index with ⟨index, bound⟩
    change index < 2 at bound
    rcases index with _ | index
    · change none = some residual at selected
      cases selected
    rcases index with _ | index
    · change none = some residual at selected
      cases selected
    omega
  decisions index selector selected := by
    rcases index with ⟨index, bound⟩
    change index < 2 at bound
    rcases index with _ | index
    · change none = some selector at selected
      cases selected
    rcases index with _ | index
    · change some publicDecision.erase = some selector at selected
      cases Option.some.inj selected
      exact ⟨publicDecision, rfl⟩
    omega

def reductionContract : ContractInterpretation reductionOwner F G reductionEnvironment where
  subjects index := by
    have same : index = ⟨0, by decide +kernel⟩ := by
      apply Fin.ext
      have bound := index.isLt
      change index.val < 1 at bound
      change index.val = 0
      omega
    subst index
    exact reductionInput
  residuals index residual selected := by
    have same : index = ⟨0, by decide +kernel⟩ := by
      apply Fin.ext
      have bound := index.isLt
      change index.val < 1 at bound
      change index.val = 0
      omega
    subst index
    change none = some residual at selected
    cases selected
  decisions index selector selected := by
    have same : index = ⟨0, by decide +kernel⟩ := by
      apply Fin.ext
      have bound := index.isLt
      change index.val < 1 at bound
      change index.val = 0
      omega
    subst index
    change none = some selector at selected
    cases selected

theorem public_formulas (index : Fin publicOwner.contract.clauses.length) :
    ((publicContract (F := F) (G := G) (sourceEnvironment := sourceEnvironment)).subjects index).interpretation.FormulaLaw := by
  rcases index with ⟨index, bound⟩
  change index < 2 at bound
  rcases index with _ | index
  · exact input_shape_formula_law
  rcases index with _ | index
  · exact public_formula_law
  omega

theorem reduction_formulas (index : Fin reductionOwner.contract.clauses.length) :
    ((reductionContract (F := F) (G := G) (reductionEnvironment := reductionEnvironment)).subjects index).interpretation.FormulaLaw := by
  have same : index = ⟨0, by decide +kernel⟩ := by
    apply Fin.ext
    have bound := index.isLt
    change index.val < 1 at bound
    change index.val = 0
    omega
  subst index
  exact reduction_formula_law

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- The residual wrapper authors no extra clauses. Its mathematical request is
external and must not be represented as an invented source continuation. -/
theorem reduction_root_inventory : reductionRoot.contract.clauses = [] := rfl

end ZkcExamples.Structured.SumcheckContractInterpretations

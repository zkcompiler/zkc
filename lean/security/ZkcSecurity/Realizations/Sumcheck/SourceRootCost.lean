module

public import ZkcSecurity.Realizations.Sumcheck.SourceInstallations
public import ZkcSecurity.Obligations.SourcePure

@[expose] public section

/-! ENNReal query budgets for the same actual complete source roots.
Closed helper work is free of queries, including its stopping outcomes. Prices
are conditional on each reached history; two calls share the actual service. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcSecurity.Realizations.Sumcheck.SourceRootProperties
open ZkcSecurity.Families.Sumcheck ZkcSecurity.Realizations.Sumcheck
open Zkc.Source Zkc.Source.Structured Zkc.Transcript Zkc.Obligations
open ZkcExamples.Structured SumcheckReferenceInstallation TableComponent SourceIteration
open SumcheckSourceSelections hiding field
attribute [local implicit_reducible] NormalForm.InputPattern.scope SourceRootReference.pattern
open ZkcSecurity.FiatShamir

variable (model : DomainModel) [fieldLaw : Fact (IsField (model.Field field))]
local instance : Field (model.Field field) := fieldLaw.out.toField
variable {Frame E P : Type} {Raw : E → Type}

variable (absorb : Interface (Occurrence.signature model.toCarriers) E P Raw)
  (charge : List E → E → ENNReal)

omit fieldLaw in
theorem terminal_cost (selection : Selection) (original : List (model.Field field))
    (out : Values (Component model.Value) SumcheckVerifierBodies.reduceOutputs) (history : List E) :
    Typed.ChargedCostBound absorb charge (terminalCheck model selection original out) history 0 := by
  exact SourceFamily.terminal_cost model absorb charge (SourceFamilySelections.installed selection) original out history

theorem one_cost (selection : Selection) (site : String)
    (original : List (model.Field field)) (count handle : Nat) (scalar : model.Field field)
    (callerFrame : Frame) (shape : original.length = 2^count) (bounded : count ≤ maximum selection)
    (cuts : SourceRound.Cuts model absorb (context site) handle)
    (boundaries : Boundaries model absorb (context site)) (error : ENNReal)
    (price : ∀ reached, charge reached cuts.query ≤ error) (history : List E) :
    Typed.ChargedCostBound absorb charge
      (SourceRootReference.one model selection {} site (some original) (some scalar) (some count) (some handle))
      history (count • error) := by
  exact SourceFamily.one_cost_bounded model absorb charge (SourceFamilySelections.installed selection) site original count handle scalar callerFrame shape bounded cuts boundaries error price history

end ZkcSecurity.Realizations.Sumcheck.SourceRootProperties

namespace ZkcSecurity.Realizations.Sumcheck.SourceInstallations
open ZkcSecurity.Families.Sumcheck ZkcSecurity.Realizations.Sumcheck
open Zkc.Source Zkc.Source.Structured Zkc.Transcript Zkc.Obligations
open ZkcExamples.Structured SumcheckReferenceInstallation TableComponent SourceIteration SourceRootProperties
open SumcheckSourceSelections hiding field
attribute [local implicit_reducible] NormalForm.InputPattern.scope SourceRootReference.pattern
open ZkcSecurity.FiatShamir
variable (model : DomainModel) [fieldLaw : Fact (IsField (model.Field field))]
local instance : Field (model.Field field) := fieldLaw.out.toField
variable {Frame E P : Type} {Raw : E → Type}
  (absorb : Interface (Occurrence.signature model.toCarriers) E P Raw)
  (charge : List E → E → ENNReal)

theorem small_cost (original : List (model.Field field)) (count handle : Nat) (scalar : model.Field field)
    (callerFrame : Frame) (shape : original.length = 2^count) (bounded : count ≤ maximum .small)
    (cuts : SourceRound.Cuts model absorb (context "label_726564756365") handle)
    (boundaries : Boundaries model absorb (context "label_726564756365")) (error : ENNReal)
    (price : ∀ reached, charge reached cuts.query ≤ error) (history : List E) :
    Typed.ChargedCostBound absorb charge
      (Occurrence.participant model (source .small) 1 (SourceRootReference.rootInputs model .small
        (.cons (some original) (.cons (some scalar) (.cons (some count) (.cons (some handle) .nil))))))
      history (count • error) := by
  let args : NormalForm.Binders model (SourceRootReference.pattern .small).scope :=
    .cons (some original) (.cons (some scalar) (.cons (some count) (.cons (some handle) .nil)))
  change Typed.ChargedCostBound absorb charge
    (Occurrence.participant model (source .small) 1 (SourceRootReference.rootInputs model .small args))
    history (count • error)
  rw [SourceRootReference.actual_reference model .small args]
  dsimp only [args]
  apply (CostComposition.map_iff _ _ _).mpr
  exact one_cost model absorb charge .small "label_726564756365" original count handle scalar
    callerFrame shape bounded cuts boundaries error price history

theorem two_cost (left right : List (model.Field field)) (count handle : Nat) (a b : model.Field field)
    (callerFrame : Frame) (leftShape : left.length = 2^count) (rightShape : right.length = 2^count)
    (bounded : count ≤ maximum .twoSums)
    (leftCuts : SourceRound.Cuts model absorb (context "label_6c656674") handle)
    (rightCuts : SourceRound.Cuts model absorb (context "label_7269676874") handle)
    (leftBoundaries : Boundaries model absorb (context "label_6c656674"))
    (rightBoundaries : Boundaries model absorb (context "label_7269676874")) (leftError rightError : ENNReal)
    (leftPrice : ∀ reached, charge reached leftCuts.query ≤ leftError)
    (rightPrice : ∀ reached, charge reached rightCuts.query ≤ rightError) (history : List E) :
    Typed.ChargedCostBound absorb charge
      (Occurrence.participant model (source .twoSums) 1 (SourceRootReference.rootInputs model .twoSums
        (.cons (some left) (.cons (some right) (.cons (some a) (.cons (some b)
          (.cons (some count) (.cons (some handle) .nil))))))))
      history (count • leftError + count • rightError) := by
  let args : NormalForm.Binders model (SourceRootReference.pattern .twoSums).scope :=
    .cons (some left) (.cons (some right) (.cons (some a) (.cons (some b)
      (.cons (some count) (.cons (some handle) .nil)))))
  change Typed.ChargedCostBound absorb charge
    (Occurrence.participant model (source .twoSums) 1 (SourceRootReference.rootInputs model .twoSums args))
    history (count • leftError + count • rightError)
  rw [SourceRootReference.actual_reference model .twoSums args]
  dsimp only [args]
  apply CostComposition.bind _ _ (count • leftError) (count • rightError)
    (one_cost model absorb charge .twoSums "label_6c656674" left count handle a callerFrame
      leftShape bounded leftCuts leftBoundaries leftError leftPrice history)
  intro first reached
  have second := one_cost model absorb charge .twoSums "label_7269676874" right count handle b callerFrame
    rightShape bounded rightCuts rightBoundaries rightError rightPrice reached
  simpa only [add_zero, SourceRootReference.one] using CostComposition.bind _ _ (count • rightError) 0 second (by
    intro second final
    apply (CostComposition.map_iff _ _ _).mpr
    exact ZkcSecurity.Obligations.SourcePure.components_cost absorb charge model _ _ _ final)

#print axioms small_cost
#print axioms two_cost
end ZkcSecurity.Realizations.Sumcheck.SourceInstallations

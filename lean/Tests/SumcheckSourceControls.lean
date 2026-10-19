module

public import Tests.SumcheckHelperMutants
public import ZkcExamples.Structured.SumcheckReduceContracts
public import Mathlib.Data.ZMod.Basic

@[expose] public section
namespace Tests.SumcheckSourceControls
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
open PrimitiveLibrary MapPrefixBodies MapFirstLaws MapPrefixLaws SumcheckHelperBodies SumcheckHelperLaws
open Tests.SumcheckHelperMutants
open Zkc.Polynomial Zkc.Polynomial.Multilinear

variable {F : Type} [CommRing F] [DecidableEq F]

def sourceCheck (xs point : List F) (claim : F) : Closed (Values (assignment F F) [.boolean]) :=
  invoke (SumcheckSourceContracts.helperMeanings (F := F) (G := F))
    checkHelper (checkInputs xs point claim)

theorem source_check_equation (xs point : List F) (claim : F)
    (vectorBound : xs.length < indexLimit) (pointBound : point.length < indexLimit) :
    sourceCheck xs point claim = .done (boolResult (decide (HasShape xs point.length 1 ∧
      (restrictPrefixValues xs point).sum = claim))) :=
  SumcheckSourceContracts.check_equation xs point claim vectorBound pointBound

theorem integer_valid : sourceCheck ([1,2,3,4] : List ℤ) [2,3] 8 = .done (boolResult true) := by
  rw [source_check_equation _ _ _ (by decide +kernel) (by decide +kernel)]
  rfl

theorem integer_wrong_claim : sourceCheck ([1,2,3,4] : List ℤ) [2,3] 9 = .done (boolResult false) := by
  rw [source_check_equation _ _ _ (by decide +kernel) (by decide +kernel)]
  rfl

theorem integer_point_order : sourceCheck ([1,2,3,4] : List ℤ) [3,2] 8 = .done (boolResult false) := by
  rw [source_check_equation _ _ _ (by decide +kernel) (by decide +kernel)]
  rfl

theorem malformed_returns_false : sourceCheck ([1,2,3] : List ℤ) [2] 0 = .done (boolResult false) := by
  rw [source_check_equation _ _ _ (by decide +kernel) (by decide +kernel)]
  rfl

theorem zero_dimension_accept : sourceCheck ([9] : List ℤ) [] 9 = .done (boolResult true) := by
  rw [source_check_equation _ _ _ (by decide +kernel) (by decide +kernel)]
  rfl

theorem zero_dimension_reject_claim : sourceCheck ([9] : List ℤ) [] 8 = .done (boolResult false) := by
  rw [source_check_equation _ _ _ (by decide +kernel) (by decide +kernel)]
  rfl

/-- ZMod 4 has zero divisors; the helper formula only needs CommRing. -/
theorem nonfield_accept : sourceCheck ([1,2,3,0] : List (ZMod 4)) [2,3] 0 = .done (boolResult true) := by
  rw [source_check_equation _ _ _ (by decide +kernel) (by decide +kernel)]
  rfl

theorem nonfield_wrong_claim : sourceCheck ([1,2,3,0] : List (ZMod 4)) [2,3] 1 = .done (boolResult false) := by
  rw [source_check_equation _ _ _ (by decide +kernel) (by decide +kernel)]
  rfl

/-- This characteristic-two ring has a coordinate distinct from both Boolean values. -/
def nonBooleanCoordinate : ZMod 2 × ZMod 2 := (0, 1)

theorem coordinate_not_boolean : nonBooleanCoordinate ≠ 0 ∧ nonBooleanCoordinate ≠ 1 := by
  decide +kernel

/-- The public checker accepts at a coordinate distinct from both Boolean values. -/
theorem characteristic_two_nonboolean_accept :
    sourceCheck ([0,1,1,0] : List (ZMod 2 × ZMod 2))
      [nonBooleanCoordinate, nonBooleanCoordinate] 0 = .done (boolResult true) := by
  rw [source_check_equation _ _ _ (by decide +kernel) (by decide +kernel)]
  rfl

theorem characteristic_two_wrong_claim :
    sourceCheck ([0,1,1,0] : List (ZMod 2 × ZMod 2))
      [nonBooleanCoordinate, nonBooleanCoordinate] nonBooleanCoordinate =
        .done (boolResult false) := by
  rw [source_check_equation _ _ _ (by decide +kernel) (by decide +kernel)]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Permuting identically typed captures reaches a rejecting constructor. -/
theorem permuted_capture_lookup :
    invoke (Evaluation.extendMeanings SiteObservations.closed
      (SumcheckSourceContracts.helperMeanings (F := ℤ) (G := ℤ)) checkPermutedDefinition)
      checkHelper (checkInputs [1,2,3,4] [2,3] 8) = .halt .reject := by
  refine (Evaluation.invoke_extended (F := ℤ) (G := ℤ) SiteObservations.closed _
    checkPermutedDefinition (checkInputs [1,2,3,4] [2,3] 8)).trans ?_
  change checkPermutedBody.denote _ _ = _
  rw [check_permuted_expansion, ite_eq_left (by decide +kernel),
    SumcheckSourceContracts.prefix_laws.shape _ _ _
      (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  change invoke (SumcheckSourceContracts.helperMeanings (F := ℤ) (G := ℤ))
    checkTableHelper (checkInputs [2,3] [1,2,3,4] 8) = _
  rw [SumcheckSourceContracts.checkTable_equation _ _ _ (by decide +kernel) (by decide +kernel)]
  rfl

/-- Each original source independently supplies the same ordered message, even at unused width zero. -/
theorem both_original_sums :
    invoke (SumcheckSourceContracts.helperMeanings (F := ℤ) (G := ℤ))
      sumsHelper (inputs [1,2,3,4] 2 0) = .done (messageResult 3 7) ∧
    invoke (SumcheckReduceContracts.helperMeanings (F := ℤ) (G := ℤ))
      sumsHelper (inputs [1,2,3,4] 2 0) = .done (messageResult 3 7) := by
  constructor
  · rw [SumcheckSourceContracts.sums_all]; rfl
  · rw [SumcheckReduceContracts.sums_all]; rfl

/-- The actual source sums cancel pairs of ones; the same integer input sums to two. -/
theorem characteristic_two_sums_cancel :
    invoke (SumcheckSourceContracts.helperMeanings (F := ZMod 2) (G := ZMod 2))
      sumsHelper (inputs [1,1,1,1] 2 7) = .done (messageResult 0 0) ∧
    invoke (SumcheckSourceContracts.helperMeanings (F := ℤ) (G := ℤ))
      sumsHelper (inputs [1,1,1,1] 2 7) = .done (messageResult 2 2) := by
  constructor <;> rw [SumcheckSourceContracts.sums_all] <;> rfl

/-- The actual malformed source checker is also the existing mathematical check. -/
theorem original_malformed_mathematical_check :
    invoke (SumcheckSourceContracts.helperMeanings (F := ℤ) (G := ℤ))
      checkHelper (checkInputs [1,2,3] [2] 0) =
        .done (boolResult (Zkc.Protocols.Sumcheck.Multilinear.check
          (n := 0 + [2].length) ([1,2,3] : List ℤ)
          (Zkc.Polynomial.Quadratic.point [2].length (coordinates [2].length [2]) Fin.elim0) 0)) :=
  SumcheckSourceContracts.check_mathematical _ _ _ (by decide +kernel) (by decide +kernel)

/-- The capture permutation cannot satisfy the actual source's complete-body association. -/
theorem permuted_capture_not_associated :
    ¬ BodyIn SumcheckSourceViews.unit.definitions checkHelper checkPermutedBody := by
  intro association
  have original := SumcheckSourceContracts.check_equation (F := ℤ) (G := ℤ)
    [1,2,3,4] [2,3] 8 (by decide +kernel) (by decide +kernel)
  have originalResult : invoke (SumcheckSourceContracts.helperMeanings (F := ℤ) (G := ℤ))
      checkHelper (checkInputs [1,2,3,4] [2,3] 8) = .done (boolResult true) := by
    rw [original]; rfl
  have body := association.invoke (F := ℤ) (G := ℤ) SumcheckSourceViews.unit.linked
    (checkInputs [1,2,3,4] [2,3] 8)
  have mutation := Evaluation.invoke_extended (F := ℤ) (G := ℤ) SiteObservations.closed
    (SumcheckSourceContracts.helperMeanings (F := ℤ) (G := ℤ)) checkPermutedDefinition
    (checkInputs [1,2,3,4] [2,3] 8)
  have stopped := mutation.symm.trans permuted_capture_lookup
  have impossible := originalResult.symm.trans (body.trans stopped)
  cases impossible

set_option backward.isDefEq.respectTransparency false in
/-- A malformed-input mutant reaches true through the same-name public lookup. -/
theorem accepts_malformed_lookup :
    invoke (Evaluation.extendMeanings SiteObservations.closed
      (SumcheckSourceContracts.helperMeanings (F := ℤ) (G := ℤ)) checkAcceptMalformedDefinition)
      checkHelper (checkInputs [1,2,3] [2] 0) = .done (boolResult true) := by
  refine (Evaluation.invoke_extended (F := ℤ) (G := ℤ) SiteObservations.closed _
    checkAcceptMalformedDefinition (checkInputs [1,2,3] [2] 0)).trans ?_
  change checkAcceptMalformedBody.denote _ _ = _
  rw [check_accept_malformed_expansion, ite_eq_left (by decide +kernel),
    SumcheckSourceContracts.first_laws.shape _ _ _
      (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Normal lookup executes the altered equality and accepts the wrong claim. -/
theorem ignores_claim_lookup :
    invoke (Evaluation.extendMeanings SiteObservations.closed
      (SumcheckSourceContracts.helperMeanings (F := ℤ) (G := ℤ)) checkTableIgnoreClaimDefinition)
      checkTableHelper (checkInputs [1,2,3,4] [2,3] 9) = .done (boolResult true) := by
  refine (Evaluation.invoke_extended (F := ℤ) (G := ℤ) SiteObservations.closed _
    checkTableIgnoreClaimDefinition (checkInputs [1,2,3,4] [2,3] 9)).trans ?_
  change checkTableIgnoreClaimBody.denote _ _ = _
  rw [check_ignore_claim_expansion, ite_eq_left (by decide +kernel),
    SumcheckSourceContracts.prefix_laws.tableLaw _ _ _
      (by decide +kernel) (by decide +kernel) (by decide +kernel),
    ite_eq_left (by decide +kernel)]
  simp only [PIR.Proc.bind]
  change (invoke (SumcheckSourceContracts.helperMeanings (F := ℤ) (G := ℤ)) prefixHelper
    (prefixInputs [1,2,3,4] 2 1 [2,3])).bind _ = _
  rw [SumcheckSourceContracts.prefix_laws.fixPrefix _ _ _ _
    (by decide +kernel) (by decide +kernel) (by decide +kernel), ite_eq_left (by decide)]
  simp only [PIR.Proc.bind]
  change (invoke (SumcheckSourceContracts.helperMeanings (F := ℤ) (G := ℤ)) valuesRealizationHelper
    (inputs (restrictPrefixValues [1,2,3,4] [2,3]) 0 1)).bind _ = _
  rw [SumcheckSourceContracts.prefix_laws.values]
  rfl


/-- The same-name malformed-input mutation cannot be associated with the original source. -/
theorem accepts_malformed_not_associated :
    ¬ BodyIn SumcheckSourceViews.unit.definitions checkHelper checkAcceptMalformedBody := by
  intro association
  have body := association.invoke (F := ℤ) (G := ℤ) SumcheckSourceViews.unit.linked
    (checkInputs [1,2,3] [2] 0)
  have mutation := Evaluation.invoke_extended (F := ℤ) (G := ℤ) SiteObservations.closed
    (SumcheckSourceContracts.helperMeanings (F := ℤ) (G := ℤ)) checkAcceptMalformedDefinition
    (checkInputs [1,2,3] [2] 0)
  have changed := mutation.symm.trans accepts_malformed_lookup
  have impossible := malformed_returns_false.symm.trans (body.trans changed)
  cases impossible

/-- Ignoring the claim contradicts the actual source callback's result. -/
theorem ignores_claim_not_associated :
    ¬ BodyIn SumcheckSourceViews.unit.definitions checkTableHelper checkTableIgnoreClaimBody := by
  intro association
  have original : invoke (SumcheckSourceContracts.helperMeanings (F := ℤ) (G := ℤ))
      checkTableHelper (checkInputs [1,2,3,4] [2,3] 9) = .done (boolResult false) := by
    rw [SumcheckSourceContracts.checkTable_equation _ _ _ (by decide +kernel) (by decide +kernel)]
    rfl
  have body := association.invoke (F := ℤ) (G := ℤ) SumcheckSourceViews.unit.linked
    (checkInputs [1,2,3,4] [2,3] 9)
  have mutation := Evaluation.invoke_extended (F := ℤ) (G := ℤ) SiteObservations.closed
    (SumcheckSourceContracts.helperMeanings (F := ℤ) (G := ℤ)) checkTableIgnoreClaimDefinition
    (checkInputs [1,2,3,4] [2,3] 9)
  have changed := mutation.symm.trans ignores_claim_lookup
  have impossible := original.symm.trans (body.trans changed)
  cases impossible

end Tests.SumcheckSourceControls

module

public import ZkcSecurity.Realizations.Sumcheck.SourceFamilyProperties
public import ZkcSecurity.Realizations.Sumcheck.SourceRootCost
public import ZkcSecurity.Families.Sumcheck.SourceAdmission

@[expose] public section

/-! Unrestricted source inputs for rejection and pathwise costs. A mathematical
control table supplies an all-replies shape invariant even when the actual raw
input is malformed. The terminal helper always sees the actual raw input.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcSecurity.Realizations.Sumcheck.SourceRootBounds
open ZkcSecurity.Families.Sumcheck ZkcSecurity.Realizations.Sumcheck
open Zkc.Source Zkc.Source.Structured ReferenceLibrary Zkc.Transcript Zkc.Obligations
open ZkcExamples.Structured SumcheckReferenceInstallation TableComponent SourceIteration SourceRootProperties
open SumcheckSourceSelections hiding field
open ZkcSecurity.FiatShamir

variable (model : DomainModel) [fieldLaw : Fact (IsField (model.Field field))]
local instance : Field (model.Field field) := fieldLaw.out.toField
variable {Frame E P : Type} {Raw : E → Type}

def controlTable (count : Nat) : List (model.Field field) := List.replicate (2^count) 0

theorem control_shape (count : Nat) : (controlTable model count).length = 2^count := List.length_replicate

theorem maximum_small (selection : Selection) : maximum selection < 64 :=
  (SourceFamilySelections.installed selection).maximum_small

theorem terminal_equation (selection : Selection) (original : List (model.Field field))
    (reference : PrefixState (model.Field field) Frame 0) (small : reference.point.length < 64) :
    terminalCheck model selection original
      (SumcheckVerifierBodies.reduceReturnValues (encode model 0 reference).slots) =
      if original.length < indexLimit then .done (some (decide
        (Multilinear.Admission.HasShape original reference.point.length 1 ∧
          (Zkc.Polynomial.Multilinear.restrictPrefixValues original reference.point).sum = reference.scalar)))
      else .halt .exhausted := by
  exact SourceFamily.terminal_equation model (SourceFamilySelections.installed selection) original reference small

theorem terminal_invalid (selection : Selection) (original : List (model.Field field))
    (reference : PrefixState (model.Field field) Frame 0) (count : Nat)
    (referenceShape : reference.original.length = 2^count) (small : count < 64)
    (invalid : original.length ≠ 2^count) :
    PIR.Yields (fun out => out = some false) (terminalCheck model selection original
      (SumcheckVerifierBodies.reduceReturnValues (encode model 0 reference).slots)) := by
  exact SourceFamily.terminal_invalid model (SourceFamilySelections.installed selection) original reference count referenceShape small invalid

theorem one_unbounded (selection : Selection) (site : String)
    (original : List (model.Field field)) (count handle : Nat) (scalar : model.Field field)
    (unbounded : ¬ count ≤ maximum selection) :
    SourceRootReference.one model selection {} site (some original) (some scalar) (some count) (some handle) =
      .halt .refused := by
  exact SourceFamily.one_unbounded model (SourceFamilySelections.installed selection) site original count handle scalar unbounded

theorem one_invalid_shape (selection : Selection) (site : String)
    (original : List (model.Field field)) (count handle : Nat) (scalar : model.Field field)
    (bounded : count ≤ maximum selection) (invalid : original.length ≠ 2^count) :
    PIR.Yields (fun out => out = some false)
      (SourceRootReference.one model selection {} site (some original) (some scalar) (some count) (some handle)) := by
  exact SourceFamily.one_invalid_shape model (SourceFamilySelections.installed selection) site original count handle scalar bounded invalid

/-- Every successful call returns a present Boolean, including false checks
on malformed raw data. Oversized counts and overflowing lengths may stop. -/
theorem one_present (selection : Selection) (site : String)
    (original : List (model.Field field)) (count handle : Nat) (scalar : model.Field field) :
    PIR.Yields (fun out => ∃ accepted : Bool, out = some accepted)
      (SourceRootReference.one model selection {} site (some original) (some scalar) (some count) (some handle)) := by
  exact SourceFamily.one_present model (SourceFamilySelections.installed selection) site original count handle scalar

/-- All false represented calls, including invalid source admission, reject or
stop outside the explicit collision escape set. No shape premise is discarded. -/
def one_no (selection : Selection) (site : String)
    (original : List (model.Field field)) (count handle : Nat) (scalar : model.Field field)
    (absorb : Interface (Occurrence.signature model.toCarriers) E P Raw)
    (escape : EscapeJudgment E Raw) (empty : ∀ reached event, escape reached event (fun _ => False))
    (steps : RepeatedComponent.NoContract
      (component model (source selection).payload.definitions (Occurrence.table model (source selection).payload)
        (context site) handle) absorb escape (no model original ()))
    (wrong : ¬ (count ≤ maximum selection ∧ original.length = 2^count ∧ scalar = original.sum))
    (history : List E) :
    Derivation absorb escape (fun _ out => out = some false) history
      (SourceRootReference.one model selection {} site (some original) (some scalar) (some count) (some handle)) := by
  exact SourceFamily.one_no model (SourceFamilySelections.installed selection) site original count handle scalar absorb escape empty steps wrong history

/-- Query cost holds for every nominal raw table and every source count. -/
theorem one_cost (selection : Selection) (site : String)
    (original : List (model.Field field)) (count handle : Nat) (scalar : model.Field field)
    (absorb : Interface (Occurrence.signature model.toCarriers) E P Raw)
    (charge : List E → E → ENNReal) (cuts : SourceRound.Cuts model absorb (context site) handle)
    (boundaries : Boundaries model absorb (context site)) (error : ENNReal)
    (price : ∀ reached, charge reached cuts.query ≤ error) (history : List E) :
    Typed.ChargedCostBound absorb charge
      (SourceRootReference.one model selection {} site (some original) (some scalar) (some count) (some handle))
      history (maximum selection • error) := by
  exact SourceFamily.one_cost model (SourceFamilySelections.installed selection) site original count handle scalar absorb charge cuts boundaries error price history

#print axioms one_no
#print axioms one_cost
end ZkcSecurity.Realizations.Sumcheck.SourceRootBounds

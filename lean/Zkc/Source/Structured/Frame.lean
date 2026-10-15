module

public import Zkc.Source.Structured.Laws
public import Zkc.Source.RegionCongruence

@[expose] public section

/-! Helper-table frame laws for structured computations.

Agreement is semantic equality of invocation on the exact helper inventory.
Nested callbacks and stopped suffixes remain in that inventory; no reachability,
table well-formedness, or native execution assumption is needed.
-/

namespace Zkc.Source.Structured

variable {F : Type}

/-- A fold consults its step and, only when present, its predicate helper. -/
theorem foldTransition_table_congr (left right : Meanings F) (spec : FoldSpec)
    (agree : ∀ helper ∈ (Op.fold spec).helpers, invoke left helper = invoke right helper)
    (arguments : Values (scalarAssignment F) spec.domain.inputs)
    (captures : Values (scalarAssignment F) spec.captures) :
    foldTransition left spec arguments captures = foldTransition right spec arguments captures := by
  have step := agree spec.stepHelper (by simp [Op.helpers])
  funext state item
  cases present : spec.predicate.isEmpty with
  | true =>
    rw [foldTransition_unfiltered left spec present,
      foldTransition_unfiltered right spec present, step]
  | false =>
    have predicate := agree spec.predicateHelper (by simp [Op.helpers, present])
    simp only [foldTransition, present, Bool.false_eq_true, ↓reduceIte, predicate, step]

/-- Fold framing preserves domain admission, predicate stops and ordered state. -/
theorem denoteFold_table_congr (left right : Meanings F) (spec : FoldSpec)
    (agree : ∀ helper ∈ (Op.fold spec).helpers, invoke left helper = invoke right helper) :
    denoteFold left spec = denoteFold right spec := by
  funext values
  simp only [denoteFold, foldTransition_table_congr left right spec agree]

/-- With the same callback meanings, an operation observes only its helpers. -/
theorem operation_table_congr [CommRing F] [DecidableEq F]
    (left right : Meanings F) (op : Op)
    (agree : ∀ helper ∈ op.helpers, invoke left helper = invoke right helper) :
    operation left op = operation right op := by
  cases op with
  | fieldConstant | booleanConstant =>
    funext arguments callbacks
    cases arguments
    cases callbacks
    rfl
  | fieldAdd | fieldSubtract | fieldMultiply | fieldEqual | booleanAnd | booleanOr |
      booleanXor | booleanEqual | booleanNotEqual | boundedAt =>
    funext arguments callbacks
    cases arguments with
    | cons a rest =>
      cases rest with
      | cons b rest => cases rest; cases callbacks; rfl
  | select =>
    funext arguments callbacks
    cases arguments with
    | cons condition rest =>
      cases rest with
      | cons yes rest =>
        cases rest with
        | cons no rest => cases rest; cases callbacks; rfl
  | invoke helper =>
    have same := agree helper (by simp [Op.helpers])
    funext arguments callbacks
    cases callbacks
    exact congrFun same arguments
  | fold spec =>
    funext arguments callbacks
    cases callbacks
    exact congrFun (denoteFold_table_congr left right spec agree) arguments
  | branch =>
    funext arguments callbacks
    cases arguments with
    | cons condition captures =>
      cases callbacks with
      | cons yes rest =>
        cases rest with
        | cons no rest => cases rest; rfl
  | loop | loopCondition =>
    funext arguments callbacks
    cases arguments with
    | cons lower rest =>
      cases rest with
      | cons upper rest =>
        cases callbacks with
        | cons body rest => cases rest; rfl
  | guard =>
    funext arguments callbacks
    cases arguments with
    | cons condition rest => cases rest; cases callbacks; rfl

variable [CommRing F] [DecidableEq F]

/-- Agreement over the erased inventory preserves the whole region meaning,
including every nested callback, branch and loop. -/
theorem region_denote_table_congr (left right : Meanings F) {Γ out : List Ty}
    (region : Region dialect Γ out)
    (agree : ∀ helper ∈ region.erase.operations.flatMap Op.helpers,
      invoke left helper = invoke right helper) :
    region.denote (meaning F left) = region.denote (meaning F right) := by
  apply Region.denote_congr
  intro op member
  apply operation_table_congr
  intro helper used
  exact agree helper (List.mem_flatMap.mpr ⟨op, member, used⟩)

/-- Callback-list framing uses the same exact erased inventory as region framing. -/
theorem regions_denote_table_congr (left right : Meanings F) {signatures}
    (bodies : Regions dialect signatures)
    (agree : ∀ helper ∈ bodies.erase.operations.flatMap Op.helpers,
      invoke left helper = invoke right helper) :
    bodies.denote (meaning F left) = bodies.denote (meaning F right) := by
  apply Regions.denote_congr
  intro op member
  apply operation_table_congr
  intro helper used
  exact agree helper (List.mem_flatMap.mpr ⟨op, member, used⟩)

end Zkc.Source.Structured

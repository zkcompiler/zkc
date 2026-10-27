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

namespace Evaluation

variable {F G : Type} {interface : PIR.Signature}
variable (observations : SiteObservations interface)

/-- A fold consults its step and, only when present, its predicate helper. -/
theorem foldTransition_table_congr (left right : HelperTable (assignment F G) interface) (spec : FoldSpec)
    (agree : ∀ helper ∈ (Op.fold spec).helpers, invoke left helper = invoke right helper)
    (arguments : Values (assignment F G) spec.domain.inputs)
    (captures : Values (assignment F G) spec.captures) :
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
theorem denoteFold_table_congr (left right : HelperTable (assignment F G) interface) (spec : FoldSpec)
    (agree : ∀ helper ∈ (Op.fold spec).helpers, invoke left helper = invoke right helper) :
    denoteFold left spec = denoteFold right spec := by
  funext values
  simp only [denoteFold, foldTransition_table_congr left right spec agree]

theorem denoteCollect_table_congr (left right : HelperTable (assignment F G) interface)
    (spec : CollectSpec)
    (agree : ∀ helper ∈ (Op.collect spec).helpers, invoke left helper = invoke right helper) :
    denoteCollect left spec = denoteCollect right spec := by
  have body := agree spec.bodyHelper (by simp [Op.helpers])
  have transition : collectTransition left spec = collectTransition right spec := by
    funext arguments captures collected item
    cases present : spec.predicate.isEmpty with
    | true => simp only [collectTransition, present, ↓reduceIte, body]
    | false =>
      have predicate := agree spec.predicateHelper (by simp [Op.helpers, present])
      simp only [collectTransition, present, Bool.false_eq_true, ↓reduceIte, predicate, body]
  funext values
  simp only [denoteCollect, transition]

/-- With the same callback meanings, an operation observes only its helpers. -/
theorem operation_table_congr [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]
    (left right : HelperTable (assignment F G) interface) (op : Op)
    (agree : ∀ helper ∈ op.helpers, invoke left helper = invoke right helper) :
    operation observations left op = operation observations right op := by
  cases op with
  | makeProduct =>
    funext arguments callbacks
    cases callbacks
    rfl
  | getProduct =>
    funext arguments callbacks
    cases arguments with
    | cons value rest => cases rest; cases callbacks; rfl
  | fieldEmbed | vectorLength =>
    funext arguments callbacks
    cases arguments with
    | cons value rest => cases rest; cases callbacks; rfl
  | indexConstant | fieldConstant | booleanConstant | groupIdentity | mark =>
    funext arguments callbacks
    cases arguments
    cases callbacks
    rfl
  | indexEqual | indexLess | indexPowerOfTwo | fieldAdd | fieldSubtract | fieldMultiply | fieldEqual | booleanAnd | booleanOr |
      booleanXor | booleanEqual | booleanNotEqual | boundedAt | groupAdd | groupScale | groupEqual =>
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
  | exec primitive =>
    funext arguments callbacks
    cases callbacks
    rfl
  | invoke helper =>
    have same := agree helper (by simp [Op.helpers])
    funext arguments callbacks
    cases callbacks
    exact congrFun same arguments
  | map spec =>
    funext arguments callbacks
    cases callbacks
    exact denoteMap_table_congr left right spec
      (agree spec.helper (by simp [Op.helpers])) arguments
  | collect spec =>
    funext arguments callbacks
    cases callbacks
    exact congrFun (denoteCollect_table_congr left right spec agree) arguments
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

variable [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

/-- Agreement over the erased inventory preserves the whole region meaning,
including every nested callback, branch and loop. -/
theorem region_denote_table_congr (left right : HelperTable (assignment F G) interface) {Γ out : List Ty}
    (region : Region dialect Γ out)
    (agree : ∀ helper ∈ region.erase.operations.flatMap Op.helpers,
      invoke left helper = invoke right helper) :
    region.denote (meaning observations left) = region.denote (meaning observations right) := by
  apply Region.denote_congr
  intro op member
  apply operation_table_congr observations
  intro helper used
  exact agree helper (List.mem_flatMap.mpr ⟨op, member, used⟩)

/-- Callback-list framing uses the same exact erased inventory as region framing. -/
theorem regions_denote_table_congr (left right : HelperTable (assignment F G) interface) {signatures}
    (bodies : Regions dialect signatures)
    (agree : ∀ helper ∈ bodies.erase.operations.flatMap Op.helpers,
      invoke left helper = invoke right helper) :
    bodies.denote (meaning observations left) = bodies.denote (meaning observations right) := by
  apply Regions.denote_congr
  intro op member
  apply operation_table_congr observations
  intro helper used
  exact agree helper (List.mem_flatMap.mpr ⟨op, member, used⟩)

end Evaluation

end Zkc.Source.Structured

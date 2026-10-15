module

public import Zkc.Source.Structured.Laws

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
  induction region using Region.rec
      (motive_2 := fun signatures bodies =>
        (∀ helper ∈ bodies.erase.operations.flatMap Op.helpers,
          invoke left helper = invoke right helper) →
        bodies.denote (meaning F left) = bodies.denote (meaning F right)) with
  | ret values => rfl
  | stop reason => rfl
  | letOp op arguments bodies next bodiesIH nextIH =>
    have operationAgree : ∀ helper ∈ op.helpers, invoke left helper = invoke right helper := by
      intro helper member
      apply agree helper
      simp only [Region.erase, RawRegion.operations, List.flatMap_cons, List.mem_append]
      exact Or.inl member
    have bodiesAgree : ∀ helper ∈ bodies.erase.operations.flatMap Op.helpers,
        invoke left helper = invoke right helper := by
      intro helper member
      apply agree helper
      simp only [Region.erase, RawRegion.operations, List.flatMap_cons,
        List.flatMap_append, List.mem_append]
      exact Or.inr (Or.inl member)
    have nextAgree : ∀ helper ∈ next.erase.operations.flatMap Op.helpers,
        invoke left helper = invoke right helper := by
      intro helper member
      apply agree helper
      simp only [Region.erase, RawRegion.operations, List.flatMap_cons,
        List.flatMap_append, List.mem_append]
      exact Or.inr (Or.inr member)
    funext env
    simp only [Region.denote, bodiesIH bodiesAgree, nextIH nextAgree]
    dsimp only [meaning]
    rw [operation_table_congr left right op operationAgree]
  | bind body next bodyIH nextIH =>
    have bodyAgree : ∀ helper ∈ body.erase.operations.flatMap Op.helpers,
        invoke left helper = invoke right helper := by
      intro helper member
      apply agree helper
      simpa only [Region.erase, RawRegion.operations, List.flatMap_append, List.mem_append]
        using Or.inl member
    have nextAgree : ∀ helper ∈ next.erase.operations.flatMap Op.helpers,
        invoke left helper = invoke right helper := by
      intro helper member
      apply agree helper
      simpa only [Region.erase, RawRegion.operations, List.flatMap_append, List.mem_append]
        using Or.inr member
    funext env
    simp only [Region.denote, bodyIH bodyAgree, nextIH nextAgree]
  | nil => rfl
  | cons body tail bodyIH tailIH =>
    rename_i agree
    have bodyAgree : ∀ helper ∈ body.erase.operations.flatMap Op.helpers,
        invoke left helper = invoke right helper := by
      intro helper member
      apply agree helper
      simpa only [Regions.erase, RawRegions.operations, List.flatMap_append, List.mem_append]
        using Or.inl member
    have tailAgree : ∀ helper ∈ tail.erase.operations.flatMap Op.helpers,
        invoke left helper = invoke right helper := by
      intro helper member
      apply agree helper
      simpa only [Regions.erase, RawRegions.operations, List.flatMap_append, List.mem_append]
        using Or.inr member
    simp only [Regions.denote, bodyIH bodyAgree, tailIH tailAgree]

/-- Callback-list framing uses the same exact erased inventory as region framing. -/
theorem regions_denote_table_congr (left right : Meanings F) {signatures}
    (bodies : Regions dialect signatures)
    (agree : ∀ helper ∈ bodies.erase.operations.flatMap Op.helpers,
      invoke left helper = invoke right helper) :
    bodies.denote (meaning F left) = bodies.denote (meaning F right) := by
  induction bodies using Regions.rec (motive_1 := fun _ _ _ => True) with
  | ret => trivial
  | stop => trivial
  | letOp => trivial
  | bind => trivial
  | nil => rfl
  | cons body tail _ tailIH =>
    have bodyAgree : ∀ helper ∈ body.erase.operations.flatMap Op.helpers,
        invoke left helper = invoke right helper := by
      intro helper member
      apply agree helper
      simpa only [Regions.erase, RawRegions.operations, List.flatMap_append, List.mem_append]
        using Or.inl member
    have tailAgree : ∀ helper ∈ tail.erase.operations.flatMap Op.helpers,
        invoke left helper = invoke right helper := by
      intro helper member
      apply agree helper
      simpa only [Regions.erase, RawRegions.operations, List.flatMap_append, List.mem_append]
        using Or.inr member
    simp only [Regions.denote, region_denote_table_congr left right body bodyAgree,
      tailIH tailAgree]

end Zkc.Source.Structured

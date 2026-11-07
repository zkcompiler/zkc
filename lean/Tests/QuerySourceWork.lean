module

public import Zkc.Realization.QuerySourceWork
public import Tests.QueryControllerReturn

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Tests.QuerySourceWork
open Zkc.Source Zkc.Source.Structured Zkc.Realization
open OracleProcessData VirtualStorageInstallation QuerySavedSource
open Zkc.Realization.QuerySourceWork

/-- The fixture's two installed levels distinguish base and virtual children
by the actual immutable registry and captured source anchor. -/
def expansion (entries : OracleEntries model snapshot [] math) (request : OracleRead)
    (shape : QueryWork.Shape) : Prop :=
  (entries = before.entries ∧ request.anchor = anchor 0 ∧ shape = .base) ∨
  (entries = result.state.entries ∧ request.anchor = anchor 9 ∧ shape = Tests.QueryWork.repeated)

theorem inner_body : Body
    (fun child shape ↦ expansion QuerySourceStack.innerContext.older
      ((QuerySourceStack.innerParent.request
        QuerySourceStack.first.location QuerySourceStack.first.expansion).expand child) shape)
    QuerySourceStack.innerParent.body [.base, .base] := by
  change Body _ (QuerySourceContinuation.source (anchor 0) 0) _
  rw [QuerySourceContinuation.source_body]
  apply Body.call
  · exact Or.inl ⟨rfl, rfl, rfl⟩
  · intro first
    apply Body.call
    · exact Or.inl ⟨rfl, rfl, rfl⟩
    · intro second; exact .done _

theorem outer_body : Body
    (fun child shape ↦ expansion QueryNestedSource.outerContext.older
      ((QueryNestedSource.outerParent.request (location 20) []).expand child) shape)
    QueryNestedSource.outerParent.body [Tests.QueryWork.repeated, Tests.QueryWork.repeated] := by
  change Body _ (QuerySourceContinuation.source (anchor 9) 0) _
  rw [QuerySourceContinuation.source_body]
  apply Body.call
  · exact Or.inr ⟨rfl, rfl, rfl⟩
  · intro first
    apply Body.call
    · exact Or.inr ⟨rfl, rfl, rfl⟩
    · intro second; exact .done _

/-- Both saved nesting levels obtain their waiting suffixes from the same
actual bodies and answer indices used by their source continuations. -/
theorem nested : StackSchedule expansion QueryController.leafStack .base
    [[.base], [Tests.QueryWork.repeated]] :=
  ⟨[.base, .base], inner_body, rfl,
    ⟨[Tests.QueryWork.repeated, Tests.QueryWork.repeated], outer_body, rfl, rfl⟩⟩

/-- The newly saved first answer removes exactly the first original child.
The ignored value still consumes an occurrence and cannot be deduplicated. -/
theorem after_first : Body (model := model) (A := Values (Component model.Value) [.index])
    (fun child shape ↦ expansion QuerySourceStack.innerContext.older
      ((QuerySourceStack.innerParent.request
        QuerySourceStack.first.location QuerySourceStack.first.expansion).expand child) shape)
    (.call (QuerySourceContext.child 1) (fun answer ↦ .done (.cons (some answer) .nil)))
    [.base] :=
  remaining inner_body QueryControllerReturn.siblingSaved.cursor

/-- The real sibling save carries the reduced work through both linked
frames; it does not receive a fresh independent schedule. -/
theorem sibling : StackSchedule expansion QueryControllerReturn.siblingStack .base
    [[], [Tests.QueryWork.repeated]] :=
  StackSchedule.sibling QuerySourceStack.innerContext QueryController.savedInner
    QuerySourceStack.first.location QuerySourceStack.first.expansion []
    [.query QuerySourceStack.leaf, .provider 4] 1 2 QueryControllerReturn.outerStack nested
    (currentArenas := QueryController.afterLeaf) (fun _ ↦ List.nil_prefix)
    (answerSlot := 0) (answer := (10 : Nat)) rfl
    (show QueryNestedSource.innerNext (10 : Nat) =
      .call (QuerySourceContext.child 1) (fun answer ↦ .done (.cons (some answer) .nil)) from rfl)
    "inner-second" 1 [] QueryControllerReturn.sibling_encoded

theorem actual_child : expansion QuerySourceStack.innerContext.older
    (QueryNestedSource.leaf 0 1) .base :=
  (StackSchedule.child (QuerySourceStack.innerContext.withAnswers [0])
    QueryControllerReturn.siblingSaved
    QuerySourceStack.first.location QuerySourceStack.first.expansion
    [.query QuerySourceStack.leaf, .provider 4] 2 QueryControllerReturn.outerStack sibling).1

theorem parent : ∃ children, children.length = 2 ∧
    StackSchedule expansion QueryControllerReturn.outerStack (.virtual children)
      [[Tests.QueryWork.repeated]] :=
  StackSchedule.complete_parent (QuerySourceStack.innerContext.withAnswers [0])
    QueryControllerReturn.siblingSaved
    QuerySourceStack.first.location QuerySourceStack.first.expansion
    [.query QuerySourceStack.leaf, .provider 4] 2 QueryControllerReturn.outerStack sibling

theorem missing_second_child : ¬ Body
    (fun child shape ↦ expansion QuerySourceStack.innerContext.older
      ((QuerySourceStack.innerParent.request
        QuerySourceStack.first.location QuerySourceStack.first.expansion).expand child) shape)
    QuerySourceStack.innerParent.body [.base] := by
  intro body
  have suffix := remaining body QueryControllerReturn.siblingSaved.cursor
  obtain ⟨_, _, impossible, _⟩ := Body.call_iff.mp suffix
  contradiction

theorem premature_root : ¬ StackSchedule (self := 1) (S := Nat) (E := Nat) (root := kind)
    expansion .root Tests.QueryWork.repeated [[.base]] := by
  intro scheduled
  have impossible := scheduled.root_frames
  contradiction

#print axioms nested
#print axioms after_first
#print axioms sibling
#print axioms actual_child
#print axioms parent
#print axioms missing_second_child
#print axioms premature_root
end Tests.QuerySourceWork

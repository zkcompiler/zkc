module

public import Tests.QueryController

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Tests.QueryControllerReturn
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Realization
open OracleProcessData VirtualStorageInstallation QueryController
open Zkc.Realization.QuerySavedSource Zkc.Realization.QuerySourceStack

def siblingFrame : QueryContinuation.Frame :=
  {QuerySourceStack.innerFrame with answers := [0]}

def siblingRecord : model.Value (QueryContinuation.layout "inner-second" 1).type :=
  (1, 0, 0, 0, 0, ())

theorem sibling_encoded : QueryContinuation.Encodes "inner-second" 1
    siblingFrame siblingRecord := ⟨(0, ()), rfl, rfl⟩

noncomputable def siblingSaved :=
  QueryController.savedInner.sibling (currentArenas := QueryController.afterLeaf)
    (fun _ ↦ List.nil_prefix) (answerSlot := 0) (answer := (10 : Nat)) rfl
    (show QueryNestedSource.innerNext (10 : Nat) =
      .call (QuerySourceContext.child 1) (fun answer ↦ .done (.cons (some answer) .nil)) from rfl)
    "inner-second" 1 [] sibling_encoded

noncomputable def outerStack : Stack model snapshot [] math 1 Nat Nat kind kind 1 0 :=
  .saved QueryNestedSource.outerContext QueryController.savedOuter (location 20) [] [] 0 .root

noncomputable def siblingStack : Stack model snapshot [] math 1 Nat Nat kind kind 3 0 :=
  .saved (QuerySourceStack.innerContext.withAnswers [0]) siblingSaved
    QuerySourceStack.first.location QuerySourceStack.first.expansion
    [.query QuerySourceStack.leaf, .provider 4] 2 outerStack

theorem sibling_progress :
    PIR.Reaches QueryController.calls QueryController.source 0
      ((QuerySourceStack.innerContext.operations
        QuerySourceStack.first.location QuerySourceStack.first.expansion
        (QuerySourceContext.child 1) (11, 3)).bind siblingStack.restore) 1 := by
  have returned := Zkc.Realization.QuerySourceStack.returned QueryController.calls
    QueryController.leafStack QuerySourceStack.nested_progress _
    (QueryNestedSource.leaf_return 0 0 0 11 2 0 10 4)
  rw [show QueryController.leafStack =
    .saved QuerySourceStack.innerContext QueryController.savedInner
      QuerySourceStack.first.location QuerySourceStack.first.expansion [] 1 outerStack from rfl,
    Stack.restore_sibling QuerySourceStack.innerContext QueryController.savedInner
      QuerySourceStack.first.location QuerySourceStack.first.expansion [] _
      1 2 outerStack (10 : Nat) (11, 3)
      (currentArenas := QueryController.afterLeaf) (fun _ ↦ List.nil_prefix)
      (answerSlot := 0) rfl
      (show QueryNestedSource.innerNext (10 : Nat) =
        .call (QuerySourceContext.child 1)
          (fun answer ↦ .done (.cons (some answer) .nil)) from rfl)
      "inner-second" 1 [] sibling_encoded] at returned
  exact returned

/-- Two actual child executions discharge the enclosing parent continuation.
The parent charge is retained once, and the outer continuation is not run yet.
This uses the dispatcher return equations rather than the old direct inner
execution theorem. -/
theorem parent_progress :
    PIR.Reaches QueryController.calls QueryController.source 0
      (outerStack.restore ⟨.returned (20 : Nat), (22, 4),
        [.query (QueryNestedSource.innerRoot 0),
          .query (QueryNestedSource.leaf 0 0), .provider 4,
          .query (QueryNestedSource.leaf 0 1), .provider 5]⟩) 2 := by
  have returned := Zkc.Realization.QuerySourceStack.returned QueryController.calls
    siblingStack sibling_progress _
    (QueryNestedSource.leaf_return 0 1 11 22 3 1 20 5)
  rw [show siblingStack =
    .saved (QuerySourceStack.innerContext.withAnswers [0]) siblingSaved
      QuerySourceStack.first.location QuerySourceStack.first.expansion
      [.query QuerySourceStack.leaf, .provider 4] 2 outerStack from rfl,
    Stack.restore_parent (QuerySourceStack.innerContext.withAnswers [0]) siblingSaved
      QuerySourceStack.first.location QuerySourceStack.first.expansion _ _ 2 outerStack
      (20 : Nat) (22, 4) (20 : Nat) rfl] at returned
  exact returned

/-- The new saved slot records the answer that actually resumed the source.
An equal-typed slot swap cannot change the installed sibling frame. -/
theorem wrong_saved_answer_refused :
    ¬ QueryContinuation.Stored "inner-second" 1 [siblingRecord] 0
      {siblingFrame with answers := [1]} := by
  intro wrong
  have same := congrArg QueryContinuation.Frame.answers (siblingSaved.decoded wrong)
  contradiction

/-- The complete old frame load and unpack recovers the caller link. This is
the same stored object used by the sibling source transition, not a separately
constructed frame with matching field types. -/
theorem restored_frame (program : Program) (context : Context) :
    let environment : Domain.Environment model.toCarriers :=
      [.data ⟨.sequence (QueryContinuation.layout "inner-second" 1).type, rfl, [siblingRecord]⟩,
        .data (.index 0)]
    ∃ record, QueryContinuation.Encodes "inner-second" 1 siblingFrame record ∧
      Nonempty (Original.Simulation Eq (fun _ live ↦ environment <+: live)
        (.done (environment ++
          [.data ⟨(QueryContinuation.layout "inner-second" 1).type, rfl, record⟩] ++
          siblingFrame.values.map (fun value ↦ Domain.Value.data (.index value))))
        (Domain.evaluate model program context
          (QueryContinuation.loadInstructions "inner-second" 1 2 0 1) environment)) :=
  siblingSaved.stored.load_project _ 0 1 rfl program context

#print axioms sibling_progress
#print axioms parent_progress
#print axioms wrong_saved_answer_refused
#print axioms restored_frame
end Tests.QueryControllerReturn

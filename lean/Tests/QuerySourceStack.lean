module

public import Zkc.Realization.QuerySourceStack
public import Tests.QueryNestedSource

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Tests.QuerySourceStack
open Zkc.Source Zkc.Source.Structured Zkc.Realization
open Zkc.Realization.QuerySavedSource Zkc.Realization.QuerySourceStack
open OracleProcessData VirtualStorageInstallation

abbrev calls := QueryNestedSource.calls
abbrev root := QueryNestedSource.root
abbrev first := QueryNestedSource.innerRoot 0
abbrev leaf := QueryNestedSource.leaf 0 0

noncomputable def outerStack : Stack model snapshot [] math 1 Nat Nat kind kind 1 0 :=
  .saved QueryNestedSource.outerContext QueryNestedSource.savedOuter (location 20) [] [] 0 .root

/-- This inner frame points to the actual outer slot, not the unrelated frame
coordinates used by the standalone inner-body test. The source is unchanged. -/
def innerFrame : QueryContinuation.Frame := ⟨1, 0, 0, 0, []⟩

def innerParent : Parent layout references result.state.entries [record] innerFrame :=
  ⟨location 9, 2, 2, 0, [1], captures, by kernel_rfl, installed⟩

def innerContext : SourceContext innerParent 1 where
  older := before.entries
  located := QuerySourceContext.context.located
  reachable := before_reachable
  smaller := QuerySourceContext.context.smaller

def innerRecord : model.Value (QueryContinuation.layout "inner-frame" 0).type :=
  (1, 0, 0, 0, ())

noncomputable def savedInner : Saved "inner-frame" 0 [innerRecord] 0
    QuerySourceContinuation.arenas innerParent (QuerySourceContext.child 0)
      QueryNestedSource.innerNext :=
  save [] (show QueryContinuation.Encodes "inner-frame" 0 innerFrame innerRecord
    from ⟨(), rfl, rfl⟩) QueryNestedSource.innerStart.cursor

noncomputable def nestedStack : Stack model snapshot [] math 1 Nat Nat kind kind 2 0 :=
  .saved innerContext savedInner first.location first.expansion [] 1 outerStack

theorem outer_progress :
    PIR.Reaches calls
      (OracleProcess.answer model 1 QueryNestedSource.outerResult.state.entries root (0, 0)) 0
      ((QueryNestedSource.outerContext.operations (location 20) []
        (QueryNestedSource.child 0) (0, 1)).bind outerStack.restore) 0 := by
  exact descend QueryNestedSource.outerContext QueryNestedSource.savedOuter
    (location 20) [] [] 0 .root (by decide) (by decide) (by decide) calls
    (initial := (0, 0))
    (initial calls QueryNestedSource.outerResult.state.entries root (0, 0) 0)
    QueryNestedSource.outerStart

/-- The shared descent rule composes both source suspensions with their saved
physical links. No client supplies a stack evaluator or log/phase equation. -/
theorem nested_progress :
    PIR.Reaches calls
      (OracleProcess.answer model 1 QueryNestedSource.outerResult.state.entries root (0, 0)) 0
      ((innerContext.operations first.location first.expansion
        (QuerySourceContext.child 0) (0, 2)).bind nestedStack.restore) 0 := by
  exact descend innerContext savedInner first.location first.expansion [] 1 outerStack
    (by decide) (by decide) (by decide) calls (initial := (0, 1)) outer_progress
    QueryNestedSource.innerStart

/-- The actual first provider reply resumes the same saved stack. Its phase,
query charge and log are obtained from the existing leaf execution theorem. -/
theorem first_reply :
    PIR.Reaches calls
      (OracleProcess.answer model 1 QueryNestedSource.outerResult.state.entries root (0, 0)) 0
      (nestedStack.restore ⟨.returned (10 : Nat), (11, 3),
        [.query leaf, .provider 4]⟩) 1 :=
  Zkc.Realization.QuerySourceStack.returned calls nestedStack nested_progress _
    (QueryNestedSource.leaf_return 0 0 0 11 2 0 10 4)

/-- One stop rule unwinds both frames. The three charged source occurrences,
post-provider state and provider event all survive, without invoking siblings. -/
theorem nested_stopped (reason : PIR.Stop) :
    PIR.Reaches calls
      (OracleProcess.answer model 1 QueryNestedSource.outerResult.state.entries root (0, 0)) 0
      (.done ⟨.stopped reason, (11, 3),
        [.query root, .query first, .query leaf, .provider 4]⟩) 1 := by
  have child : PIR.Reaches calls
      (innerContext.operations first.location first.expansion
        (QuerySourceContext.child 0) (0, 2)) 0
      (.done ⟨.stopped reason, (11, 3), [.query leaf, .provider 4]⟩) 1 := by
    change PIR.Reaches calls
      (.call (I := OracleProcess.Interface model Nat Nat) (.inr leaf, 0)
        (fun reply ↦ .done (⟨reply.outcome, (reply.state, 3),
          .query leaf :: reply.events.map OracleEvent.provider⟩ :
            PIR.Execution (Nat × Nat) (OracleEvent Nat) Nat))) 0 _ 1
    exact .step (P := calls) (.inr leaf, 0) _ 0
      ⟨.stopped reason, 11, [4]⟩ _ _ (.refl _ _)
  exact stopped calls nestedStack nested_progress reason (11, 3)
    [.query leaf, .provider 4] child

/-- An equal-typed outer-instance mutation cannot reuse the saved link. -/
theorem wrong_outer_slot_refused :
    ¬ QueryContinuation.Stored "inner-frame" 0 [innerRecord] 0
      {innerFrame with outerInstance := 1} := by
  intro wrong
  have same := congrArg QueryContinuation.Frame.outerInstance (savedInner.decoded wrong)
  contradiction

/-- A root return cannot retain a nonzero outer slot, even if the answer and
both nominal kinds are unchanged. -/
theorem nonzero_root_slot_refused :
    ¬ Nonempty (Stack model snapshot [] math 1 Nat Nat kind kind 0 1) := by
  rintro ⟨stack⟩
  exact Nat.one_ne_zero stack.zero_root.2

#print axioms outer_progress
#print axioms nested_progress
#print axioms first_reply
#print axioms nested_stopped
#print axioms wrong_outer_slot_refused
#print axioms nonzero_root_slot_refused
end Tests.QuerySourceStack

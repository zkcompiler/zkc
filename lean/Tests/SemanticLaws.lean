module

public import Zkc.Semantics.Provider
public import Zkc.Source.FiniteControl

@[expose] public section

/-! Kernel-checked positive and failure controls for semantic composition.
All providers here are explicit finite deterministic models, not random oracles.
-/

namespace SemanticLawsTests
open PIR
open Zkc.Source.FiniteControl

abbrev tick : Signature := ⟨Unit, fun _ => Unit⟩
abbrev logical : Signature := ⟨Bool, fun _ => Unit⟩

def one : Proc tick Unit := .call () .done

def triple : Proc tick Unit := .call () fun _ => .call () fun _ => .call () .done

def expansion : OperationInterpretation logical tick := fun op => if op then triple else one

def mixed : Proc logical Unit := .call false fun _ => .call true .done

def ticking : Handler tick Nat Nat := fun _ state => ⟨.returned (), state + 1, [state]⟩

def chargeQuery : Cost.Charge tick Nat Nat := fun _ _ _ => 1

def chargeLogical : Cost.Charge logical Nat Nat := fun op _ _ => if op then 3 else 1

example : Within 2 mixed := by simp [mixed, Within]
example : Within 4 (mixed.interpret expansion) := by
  simp [mixed, expansion, one, triple, Proc.interpret, Proc.bind, Within]

theorem expanded_not_source_budget : ¬ Within 2 (mixed.interpret expansion) := by
  change ¬ (∀ _ : Unit, ∀ _ : Unit, False)
  intro impossible
  exact impossible () ()

example : Cost.spent chargeQuery ticking (mixed.interpret expansion) 0 = 4 := rfl
example : (mixed.interpret expansion).run (Cost.handler chargeQuery ticking) (0, 7) =
    ⟨.returned (), (4, 11), [0, 1, 2, 3]⟩ := rfl

/-- A per-operation estimate retains the difference between one and three calls. -/
theorem heterogeneous_bound (state : Nat) :
    Cost.spent chargeQuery ticking (mixed.interpret expansion) state ≤
      Cost.spent chargeLogical (fun op s => (expansion op).run ticking s) mixed state := by
  apply Cost.spent_interpret_le
  intro op s
  cases op <;> simp [Cost.spent, expansion, triple, one, ticking, chargeQuery,
    chargeLogical, Cost.handler, Proc.run, Execution.follow]

example : Cost.spent chargeLogical (fun op s => (expansion op).run ticking s) mixed 0 = 4 := rfl

def stopping : Handler tick Nat Nat := fun _ state =>
  if state = 1 then ⟨.stopped .reject, state + 1, [state]⟩
  else ⟨.returned (), state + 1, [state]⟩

/-- The entered failing call is charged; later calls and the suffix are absent. -/
example : (triple.bind fun _ => triple).run (Cost.handler chargeQuery stopping) (0, 5) =
    ⟨.stopped .reject, (2, 7), [0, 1]⟩ := rfl
example : Cost.spent chargeQuery stopping triple 0 = 2 := rfl
example : Cost.spent chargeQuery stopping triple 0 ≠ 1 := by decide
example : Cost.spent chargeQuery stopping triple 0 ≠ 3 := by decide

def rejectEarly : Proc tick Bool := one.bind fun _ => .halt .reject

def completeFalse : Proc tick Bool := triple.bind fun _ => .done false

def accepts (result : Execution Nat Nat Bool) : Bool :=
  match result.outcome with | .returned true => true | _ => false

/-- Equality of one-shot acceptance does not imply equal traces, cost, state,
or the same kind of terminal outcome. -/
theorem early_same_acceptance : accepts (rejectEarly.run ticking 0) =
    accepts (completeFalse.run ticking 0) := rfl
theorem early_different_state : (rejectEarly.run ticking 0).state ≠
    (completeFalse.run ticking 0).state := by decide
theorem early_different_events : (rejectEarly.run ticking 0).events ≠
    (completeFalse.run ticking 0).events := by decide
theorem early_different_outcome : (rejectEarly.run ticking 0).outcome ≠
    (completeFalse.run ticking 0).outcome := by decide
theorem early_different_cost : Cost.spent chargeQuery ticking rejectEarly 0 ≠
    Cost.spent chargeQuery ticking completeFalse 0 := by decide

/-- A secret-selected count leaks through cost even with identical acceptance. -/
def secretCount (secret : Bool) : Proc tick Bool :=
  (repeatN (if secret then 2 else 1) (fun _ => one) ()).bind fun _ => .done true

example : ((secretCount false).run ticking 0).outcome =
    ((secretCount true).run ticking 0).outcome := rfl
theorem selected_count_leaks_cost : Cost.spent chargeQuery ticking (secretCount false) 0 ≠
    Cost.spent chargeQuery ticking (secretCount true) 0 := by decide

open PIR.Provider

def emptyCache : CacheState Bool Nat := ⟨fun _ => none, [7, 9]⟩

def twice : Proc (cacheSignature Bool Nat) (Nat × Nat) :=
  .call true fun first => .call true fun second => .done (first, second)

example : (twice.run cached emptyCache).outcome = .returned (7, 7) := rfl
example : (twice.run cached emptyCache).state.unused = [9] := rfl
example : (twice.run cached emptyCache).events = [true, true] := rfl
example : Cost.spent queryCharge cached twice emptyCache = 2 := rfl
example : Cost.spent missCharge cached twice emptyCache = 1 := rfl

theorem misses_bounded_by_queries (program : Proc (cacheSignature Bool Nat) Unit)
    (state : CacheState Bool Nat) :
    Cost.spent missCharge cached program state ≤ Cost.spent queryCharge cached program state := by
  apply Cost.spent_mono
  intro op s
  simp only [missCharge, queryCharge]
  split <;> decide

/-- Mutant: clearing the map makes repeated-key calls consume fresh supply. -/
def resampling : Handler (cacheSignature Bool Nat) (CacheState Bool Nat) Bool :=
  fun key state => cached key ⟨fun _ => none, state.unused⟩

example : (twice.run resampling emptyCache).outcome = .returned (7, 9) := rfl
theorem fresh_is_not_cached : (twice.run cached emptyCache).outcome ≠
    (twice.run resampling emptyCache).outcome := by decide

/-- Exhaustion is an inner stop, and its query remains both visible and charged. -/
example : (twice.run (Cost.handler queryCharge cached) (⟨fun _ => none, []⟩, 0)).outcome =
    .stopped .exhausted := rfl
example : (twice.run (Cost.handler queryCharge cached) (⟨fun _ => none, []⟩, 0)).state.2 = 1 := rfl
example : (twice.run cached ⟨fun _ => none, []⟩).events = [true] := rfl

/-- Separate state cells and shared state produce different joint observations. -/
def separateQueries : Proc (jointSignature (cacheSignature Bool Nat) (cacheSignature Bool Nat))
    (Nat × Nat) :=
  .call (.inl true) fun first => .call (.inr true) fun second => .done (first, second)

def otherCache : CacheState Bool Nat := ⟨fun _ => none, [9, 7]⟩
example : (separateQueries.run (joint cached cached) (emptyCache, otherCache)).outcome =
    .returned (7, 9) := rfl

theorem shared_differs_from_separate : (twice.run cached emptyCache).outcome ≠
    (separateQueries.run (joint cached cached) (emptyCache, otherCache)).outcome := by decide

def firstState : Execution Bool Bool Bool := ⟨.returned true, false, []⟩
def secondState : Execution Bool Bool Bool := ⟨.returned true, true, []⟩
def readState (_ : Bool) (state : Bool) : Execution Bool Bool Bool :=
  ⟨.returned state, state, []⟩

example : firstState.outcome = secondState.outcome := rfl
example : (firstState.follow readState).outcome ≠ (secondState.follow readState).outcome := by decide

/-- Hiding private events establishes only the chosen view. -/
def hiddenLeft : Execution Unit Bool Bool := ⟨.returned true, (), [false]⟩
def hiddenRight : Execution Unit Bool Bool := ⟨.returned true, (), [true]⟩
example : Related Eq (fun _ => ([] : List Bool)) (fun _ => []) hiddenLeft hiddenRight :=
  ⟨rfl, rfl, rfl⟩
theorem revealing_hidden_events_fails :
    ¬ Related Eq (fun e => [e]) (fun e => [e]) hiddenLeft hiddenRight := by
  intro related
  have same := related.events
  change [false] = [true] at same
  cases same

/-- Monadic staging retains inner stops but does not manufacture records after
an outer error. This instance exercises the monadic theorem directly. -/
def outerFailure : MonadHandler (Except String) tick Nat Nat :=
  fun _ state => if state = 1 then .error "provider failed" else .ok (ticking () state)

example : triple.runM outerFailure 0 = .error "provider failed" := rfl
example : (mixed.interpret expansion).runM outerFailure 0 =
    mixed.runM (fun op state => (expansion op).runM outerFailure state) 0 :=
  Proc.runM_interpret expansion outerFailure mixed 0

abbrev indexed : Signature := ⟨Nat, fun _ => Unit⟩
def indexHandler : Handler indexed Nat Nat := fun index state => ⟨.returned (), state + 1, [index]⟩
def indexedBody (index value : Nat) : Proc indexed Nat := .call index fun _ => .done (value + 1)
def runtimeLoop : Loop indexed Range Nat := ⟨id, fun _ => indexedBody⟩

example : (runtimeLoop.denote ⟨4, 7⟩ 10).run indexHandler 0 =
    ⟨.returned 13, 3, [4, 5, 6]⟩ := rfl
example : runtimeLoop.denote ⟨7, 4⟩ 10 = .done 10 := rfl
example : runtimeLoop.denote ⟨4, 4⟩ 10 = .done 10 := rfl
example : admitRange 10 100 0 = none := rfl
example : admitRange 10 0 100 = none := rfl
example : admitRange 10 10 10 = some ⟨10, 10⟩ := rfl
example : admitRange 10 7 4 = some ⟨7, 4⟩ := rfl

example : Within 3 (runtimeLoop.denote ⟨4, 7⟩ 10) := by
  apply runtimeLoop.within ⟨4, 7⟩ 10 1
  intro index value
  simp [runtimeLoop, indexedBody, Within]

def finishAtFive (index value : Nat) : Proc indexed (Step Nat) :=
  .call index fun _ => .done (if index = 5 then .finish value else .continue (value + 1))

/-- Normal completion at five permits the suffix but never enters index six. -/
example : ((iterateWhile 10 4 finishAtFive 0).bind fun value =>
    .call 99 fun _ => .done value).run indexHandler 0 =
      ⟨.returned 1, 3, [4, 5, 99]⟩ := rfl

/-- Exhausting the selected iteration count returns the current carried value. -/
example : (iterateWhile 1 4 finishAtFive 0).run indexHandler 0 =
    ⟨.returned 1, 1, [4]⟩ := rfl
example : (iterateWhile 0 4 finishAtFive 0).run indexHandler 0 =
    ⟨.returned 0, 0, []⟩ := rfl

def stopAtFive (index value : Nat) : Proc indexed (Step Nat) :=
  .call index fun _ => if index = 5 then .halt .reject else .done (.continue (value + 1))
example : ((iterateWhile 10 4 stopAtFive 0).bind fun value =>
    .call 99 fun _ => .done value).run indexHandler 0 =
      ⟨.stopped .reject, 2, [4, 5]⟩ := rfl

end SemanticLawsTests

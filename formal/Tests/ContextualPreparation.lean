import Zkc.Semantics.Preparation.Emission

set_option autoImplicit false

namespace Tests.ContextualPreparation

open PIR Zkc.Modules

def provider (key : Nat) : Nat × Nat := (key + 1, 5)
def prices : Preparation.Prices Nat Nat := ⟨fun _ _ => 1, fun _ _ => 2⟩
def externalSignature : Signature := ⟨Unit, fun _ => Nat⟩

def external (failAt : Option Nat) : Handler externalSignature Nat Nat := fun _ state =>
  ⟨if failAt = some state then .stopped .abort else .returned state, state + 1, [state]⟩

def program : Proc (PIR.Preparation.signature Nat Nat externalSignature) (Nat × Nat) :=
  .call (.prepare 2) fun (first : Nat) =>
    .call (.external ()) fun (before : Nat) =>
      .call (.prepare 2) fun (second : Nat) =>
        .call (.external ()) fun (after : Nat) => .done (first + second, before + after)

def run (mode : Preparation.Mode) (failAt : Option Nat) :=
  program.run (PIR.Preparation.handler provider prices mode (external failAt)) (Preparation.empty, 0)

theorem contextual (failAt : Option Nat) :
    Related (PIR.Preparation.StateRel provider) PIR.Preparation.view PIR.Preparation.view
      (run .direct failAt) (run .memo failAt) :=
  PIR.Preparation.contextual_memo provider prices (external failAt) program _ _
    ⟨ImmutableCache.empty_valid provider, ImmutableCache.empty_valid provider, rfl⟩

theorem replies_drive_result :
    (run .memo none).outcome = .returned (6, 1) ∧
    (run .memo none).state.2 = 2 ∧
    observeEvents PIR.Preparation.view (run .memo none).events = [0, 1] := ⟨rfl, rfl, rfl⟩

/-- The prepared value selects whether an external call happens; its reply
selects the next preparation key. Neither operation sequence is fixed. -/
def adaptive (key : Nat) : Proc (PIR.Preparation.signature Nat Nat externalSignature) Nat :=
  .call (.prepare key) fun (value : Nat) =>
    if value % 2 = 0 then
      .call (.external ()) fun (reply : Nat) =>
        .call (.prepare (key + reply)) .done
    else .halt .reject

def runAdaptive (mode : Preparation.Mode) (key state : Nat) (failAt : Option Nat) :=
  (adaptive key).run (PIR.Preparation.handler provider prices mode (external failAt))
    (Preparation.empty, state)

theorem adaptive_observation (key state : Nat) (failAt : Option Nat) :
    let direct := runAdaptive .direct key state failAt
    let memo := runAdaptive .memo key state failAt
    (direct.outcome, direct.state.2, observeEvents PIR.Preparation.view direct.events) =
      (memo.outcome, memo.state.2, observeEvents PIR.Preparation.view memo.events) :=
  PIR.Preparation.contextual_observation provider prices (external failAt) (adaptive key) state

theorem reply_selects_key :
    (runAdaptive .memo 1 0 none).outcome = .returned 2 ∧
    (runAdaptive .memo 1 3 none).outcome = .returned 5 ∧
    (runAdaptive .memo 1 3 none).state.1 4 = some (5, 5) := ⟨rfl, rfl, rfl⟩

theorem prepared_value_selects_stop :
    (runAdaptive .memo 2 3 none).outcome = .stopped .reject ∧
    (runAdaptive .memo 2 3 none).state.2 = 3 ∧
    observeEvents PIR.Preparation.view (runAdaptive .memo 2 3 none).events = [] :=
  ⟨rfl, rfl, rfl⟩

theorem failed_call_keeps_state :
    (run .memo (some 1)).outcome = .stopped .abort ∧
    (run .memo (some 1)).state.2 = 2 ∧
    (run .memo (some 1)).state.1 2 = some (3, 5) ∧
    observeEvents PIR.Preparation.view (run .memo (some 1)).events = [0, 1] :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem cache_observer_distinguishes : (run .direct none).events ≠ (run .memo none).events := by
  decide

def changed (key : Nat) : Nat × Nat := (key + 2, 5)

theorem caller_binding_matters :
    ¬ Preparation.Valid changed (run .memo none).state.1 := by
  intro valid
  have impossible : (3, 5) = (4, 5) := valid 2 (3, 5) rfl
  cases impossible

theorem cold_and_warm_preserve (state : Nat) :
    Related (PIR.Preparation.StateRel provider) PIR.Preparation.view PIR.Preparation.view
      (program.run (PIR.Preparation.handler provider prices .direct (external none))
        (Preparation.empty, state))
      (program.run (PIR.Preparation.handler provider prices .memo (external none))
        ((run .memo none).state.1, state)) :=
  PIR.Preparation.contextual_memo provider prices (external none) program _ _
    ⟨ImmutableCache.empty_valid provider, (contextual none).state.2.1, rfl⟩

/-- A value-preserving provider change may still invalidate stored cost data. -/
theorem price_binding_matters :
    ¬ Preparation.Valid (fun key => (key + 1, 9)) (run .memo none).state.1 := by
  intro valid
  have impossible : (3, 5) = (3, 9) := valid 2 (3, 5) rfl
  cases impossible

end Tests.ContextualPreparation

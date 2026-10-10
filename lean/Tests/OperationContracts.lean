import Zkc.Semantics.Interaction
import Zkc.Semantics.Preparation.Emission

set_option autoImplicit false
namespace Tests.OperationContracts
open PIR

def unitSig : Signature := ⟨Unit, fun _ => Unit⟩
def rejectAfterWrite : Handler unitSig Nat Nat := fun _ s =>
  ⟨.stopped .reject,s+1,[7]⟩
def resetAfterWrite : Handler unitSig Nat Nat := fun _ s =>
  ⟨.stopped .reject,s,[7]⟩
def attempt : Proc unitSig Nat := .call () (fun _ => .done 99)

theorem reject_retains_effects :
    attempt.run rejectAfterWrite 0 = ⟨.stopped .reject,1,[7]⟩ := rfl
theorem equal_terminal_tags_are_insufficient :
    (attempt.run rejectAfterWrite 0).outcome = (attempt.run resetAfterWrite 0).outcome ∧
    (attempt.run rejectAfterWrite 0).events = (attempt.run resetAfterWrite 0).events ∧
    (attempt.run rejectAfterWrite 0).state ≠ (attempt.run resetAfterWrite 0).state := by
  decide

def counted : Handler unitSig Nat Nat := fun _ s => ⟨.returned (),s+1,[8]⟩
def tail : Nat → Proc unitSig Nat := fun _ => .call () (fun _ => .done 100)
theorem stop_does_not_run_suffix :
    (attempt.bind tail).run rejectAfterWrite 0 = ⟨.stopped .reject,1,[7]⟩ := rfl

def boolSig : Signature := ⟨Unit, fun _ => Bool⟩
def recoverable : Handler boolSig Nat Nat := fun _ s => ⟨.returned false,s+1,[7]⟩
def recover : Proc boolSig Nat := .call () (fun b =>
  match (show Bool from b) with | true => .done 10 | false => .done 20)
theorem recoverable_failure_continues :
    recover.run recoverable 0 = ⟨.returned 20,1,[7]⟩ := rfl

open Preparation
def provider : Zkc.Modules.Preparation.Provider Nat Nat := fun k => (k+1,4)
def prices : Zkc.Modules.Preparation.Prices Nat Nat := ⟨fun _ _ => 1,fun _ _ => 1⟩
def twice : Zkc.Modules.Preparation.Program Nat Nat Nat Nat :=
  .request 0 (fun _ => .request 0 (fun v => .emit v (.done v)))

theorem reuse_has_priced_savings :
    let direct := (Emission.embed twice).run (handler provider prices .direct Emission.handler)
      (Zkc.Modules.Preparation.empty, ())
    let memo := (Emission.embed twice).run (handler provider prices .memo Emission.handler)
      (Zkc.Modules.Preparation.empty, ())
    direct.outcome = memo.outcome ∧
    observeEvents view direct.events = observeEvents view memo.events ∧
    work direct.events = 8 ∧ work memo.events = 4 ∧ overhead memo.events = 3 := by
  decide

theorem cost_observer_distinguishes :
    let direct := (Emission.embed twice).run (handler provider prices .direct Emission.handler)
      (Zkc.Modules.Preparation.empty, ())
    let memo := (Emission.embed twice).run (handler provider prices .memo Emission.handler)
      (Zkc.Modules.Preparation.empty, ())
    work direct.events + overhead direct.events ≠ work memo.events + overhead memo.events := by
  decide

end Tests.OperationContracts

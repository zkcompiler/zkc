import Zkc.Semantics.Sessions
import Zkc.Semantics.Continuation

/-! Generic session and continuation controls shared by composition and protocol tests. -/

set_option autoImplicit false

namespace Tests.SessionControls
open PIR

def sig : Signature := ⟨Unit,fun _ => Nat⟩
def once : Interaction sig := ⟨Unit,Bool,fun _ => (),fun phase _ => phase = false,
  fun _ _ _ => true⟩
def step : Proc sig Nat := .call () Proc.done

theorem first_formed : Conforms once step false := ⟨rfl,fun _ => trivial⟩
theorem second_formed_separately : Conforms once step false := first_formed
theorem blind_sequence_invalid : ¬Conforms once (step.bind (fun _ => step)) false := by
  intro h
  have impossible := (h.2 (0 : Nat)).1
  cases impossible

def sessionSig : Signature := Sessions.sig (fun _ : Bool => sig)
def sessions : Interaction sessionSig := Sessions.interaction (fun _ : Bool => sig) (fun _ => once)
def schedule (first second : Bool) : Proc sessionSig (Nat × Nat) :=
  .call ⟨first,()⟩ fun a => .call ⟨second,()⟩ fun b => .done (a,b)

theorem different_sessions_formed : Conforms sessions (schedule false true) (fun _ => false) := by
  refine ⟨rfl,fun _ => ⟨?_,fun _ => trivial⟩⟩
  simp [sessions, Sessions.interaction, once]

theorem repeated_closed_session_invalid :
    ¬Conforms sessions (schedule false false) (fun _ => false) := by
  intro h
  have impossible := (h.2 (0 : Nat)).1
  cases impossible

/-- A shared counter provider is intentionally not independent per session. -/
def shared : Handler sessionSig Nat (Bool × Nat) := fun o n =>
  ⟨.returned n,n+1,[(o.1,n)]⟩

theorem schedule_order_observable :
    ((schedule false true).run shared 0).events = [(false,0),(true,1)] ∧
    ((schedule true false).run shared 0).events = [(true,0),(false,1)] := ⟨rfl,rfl⟩

def resultHandler : Handler sig Nat Nat := fun _ n =>
  ⟨.returned n,n+1,[n]⟩
def rejected : Proc sig (Continuation.Terminal Nat) :=
  .call () fun _ => .done .rejected
def accepted : Proc sig (Continuation.Terminal Nat) :=
  .call () fun n => .done (.accepted n)
def arm (n : Nat) : Proc sig Nat := .call () fun m => .done (n+(show Nat from m))

theorem rejected_retains_without_arm :
    (Continuation.after rejected arm).run resultHandler 3 = ⟨.stopped .reject,4,[3]⟩ := rfl
theorem accepted_uses_retained_state :
    (Continuation.after accepted arm).run resultHandler 3 = ⟨.returned 7,5,[3,4]⟩ := rfl

end Tests.SessionControls

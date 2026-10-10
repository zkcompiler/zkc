import Zkc.Semantics.ResourceView

/-! Kernel-checked controls for an actual heterogeneous restricted handler.
Ticket checks here are an explicit executable model, not native backend evidence.
Two distinct source arguments can carry the same handle; admission is dynamic. -/
set_option autoImplicit false
namespace Tests.ResourceView
open Zkc.Semantics.ResourceView

inductive Slot where
  | ticket | quota | outside
  deriving DecidableEq, Repr

structure Ticket where
  binding : Nat
  generation : Nat
  live : Bool
  deriving DecidableEq, Repr

structure Handle where
  slot : Slot
  binding : Nat
  generation : Nat
  deriving DecidableEq, Repr

abbrev Cell : Slot → Type
  | .ticket => Ticket
  | .quota => Nat
  | .outside => String

abbrev admitted (slot : Slot) : Prop := slot ≠ .outside
instance : DecidablePred admitted := fun slot => inferInstanceAs (Decidable (slot ≠ .outside))

def initial : Store Cell
  | .ticket => ⟨17, 0, true⟩
  | .quota => 8
  | .outside => "retained"

def replaceSelected (ticket : Ticket) (quota : Nat) : Selected Cell admitted
  | ⟨.ticket, _⟩ => ticket
  | ⟨.quota, _⟩ => quota
  | ⟨.outside, impossible⟩ => False.elim (impossible rfl)

def original : Handle := ⟨.ticket, 17, 0⟩

inductive Op where
  | use (handle : Handle) (abortAfterUse : Bool)
  | spend (amount : Nat)
  deriving DecidableEq, Repr

def signature : PIR.Signature where
  Op := Op
  Reply
    | .use _ _ => Unit
    | .spend _ => Nat

/-- No whole-store argument or handle-indexed ambient lookup is available. -/
def handler : PIR.Handler signature (Selected Cell admitted) String
  | .use handle abortAfterUse, state =>
      let ticket := state ⟨.ticket, by decide⟩
      let quota := state ⟨.quota, by decide⟩
      if handle.slot != .ticket || handle.binding != ticket.binding ||
          handle.generation != ticket.generation || !ticket.live then
        ⟨.stopped .refused, state, []⟩
      else
        ⟨if abortAfterUse then .stopped .abort else .returned (),
          replaceSelected {ticket with generation := ticket.generation + 1, live := false} quota,
          ["consumed"]⟩
  | .spend amount, state =>
      let ticket := state ⟨.ticket, by decide⟩
      let quota := state ⟨.quota, by decide⟩
      ⟨if amount ≤ quota then .returned (quota - amount) else .stopped .exhausted,
        replaceSelected ticket (quota - amount), ["spent"]⟩

/-- The second action is selected by the actual reply of the first. -/
def adaptive (abortAfterUse : Bool) : PIR.Proc signature Nat :=
  .call (.spend 3) fun remaining =>
    .call (.use original abortAfterUse) fun _ => .done remaining

def whole (program : PIR.Proc signature Nat) :=
  program.run (scopeHandler admitted handler) initial

theorem adaptive_related (abortAfterUse : Bool) :
    PIR.Related (Frame admitted initial) (fun e => [e]) (fun e => [e])
      ((adaptive abortAfterUse).run handler (restrict admitted initial))
      (whole (adaptive abortAfterUse)) :=
  run_related admitted initial handler (adaptive abortAfterUse)

theorem success_exact : whole (adaptive false) =
    ⟨.returned 5, install admitted initial (replaceSelected ⟨17, 1, false⟩ 5),
      ["spent", "consumed"]⟩ := by
  apply run_returned
  cbv

theorem stopped_exact : whole (adaptive true) =
    ⟨.stopped .abort, install admitted initial (replaceSelected ⟨17, 1, false⟩ 5),
      ["spent", "consumed"]⟩ := by
  apply run_stopped
  cbv

example : (whole (adaptive false)).state .ticket = ⟨17, 1, false⟩ := by cbv
example : (whole (adaptive false)).state .quota = 5 := by cbv
example : (whole (adaptive true)).state .ticket = ⟨17, 1, false⟩ := by cbv
example : (whole (adaptive true)).state .quota = 5 := by cbv
example (abortAfterUse : Bool) : (whole (adaptive abortAfterUse)).state .outside = "retained" :=
  run_frame admitted initial handler (adaptive abortAfterUse) .outside (by decide)
example (abortAfterUse : Bool) : (whole (adaptive abortAfterUse)).state .ticket =
    ((adaptive abortAfterUse).run handler (restrict admitted initial)).state ⟨.ticket, by decide⟩ :=
  run_selected admitted initial handler (adaptive abortAfterUse) .ticket (by decide)
example : ¬ admitted .outside := by decide

def useThen (left right : Handle) : PIR.Proc signature Nat :=
  .call (.use left false) fun _ => .call (.use right false) fun _ => .done 9

example : (whole (useThen original original)).outcome = .stopped .refused := by cbv
example : (whole (useThen original original)).events = ["consumed"] := by cbv
example : (whole (useThen original original)).state .ticket = ⟨17, 1, false⟩ := by cbv
example : (whole (useThen original original)).state .outside = "retained" := by cbv

def oneUse (handle : Handle) : PIR.Proc signature Nat :=
  .call (.use handle false) fun _ => .done 9

example : (whole (oneUse {original with slot := .outside})).outcome = .stopped .refused := by cbv
example : (whole (oneUse {original with slot := .outside})).state .outside = "retained" := by cbv
example : (whole (oneUse {original with binding := 99})).outcome = .stopped .refused := by cbv
example : (whole (oneUse {original with generation := 1})).outcome = .stopped .refused := by cbv
example : (whole (oneUse {original with generation := 1})).events = [] := by cbv
example : (whole (oneUse {original with binding := 99})).state .ticket = initial .ticket := by cbv

/-- Even the current generation cannot revive an already consumed ticket. -/
example : (whole (useThen original {original with generation := 1})).outcome = .stopped .refused := by cbv
/-- Rebinding the name after a stopped operation does not mint a new resource. -/
example : ((oneUse original).run (scopeHandler admitted handler)
    (whole (adaptive true)).state).outcome = .stopped .refused := by cbv

def exhausted : PIR.Proc signature Nat :=
  .call (.spend 20) fun _ => .call (.use original false) fun _ => .done 9
example : (whole exhausted).outcome = .stopped .exhausted := by cbv
example : (whole exhausted).state .quota = 0 := by cbv
example : (whole exhausted).state .ticket = initial .ticket := by cbv
example : (whole exhausted).events = ["spent"] := by cbv
example : (whole (.halt .reject)).state .outside = "retained" := by cbv
example : (whole (.done 4)).outcome = .returned 4 := by cbv

/-- A frame-only check cannot justify rolling back selected failure state. -/
example : ¬ Frame admitted initial
    ((adaptive true).run handler (restrict admitted initial)).state initial := by
  intro related
  have same := congrFun related.1 ⟨.quota, by decide⟩
  change (8 : Nat) = 5 at same
  contradiction

def corruptOutside (store : Store Cell) : Store Cell
  | .ticket => store .ticket
  | .quota => store .quota
  | .outside => "corrupted"

/-- Selected-state agreement alone is too weak: an outside mutation fails Frame. -/
example : ¬ Frame admitted initial (restrict admitted initial) (corruptOutside initial) := by
  intro related
  have impossible := related.2 .outside (by decide)
  contradiction

/-- The boundary does not require a nonempty view or a default cell value. -/
example {S : Type} (Cells : S → Type) (store : Store Cells) :
    install (fun _ : S => False) store (restrict (fun _ => False) store) = store :=
  install_restrict _ store
example {S : Type} (Cells : S → Type) (store : Store Cells) :
    install (fun _ : S => True) store (restrict (fun _ => True) store) = store :=
  install_restrict _ store

abbrev noSlots (_ : Slot) : Prop := False
abbrev allSlots (_ : Slot) : Prop := True
abbrev unitSignature : PIR.Signature := ⟨Unit, fun _ => Unit⟩
def emptyHandler : PIR.Handler unitSignature (Selected Cell noSlots) String :=
  fun _ state => ⟨.stopped .abort, state, ["empty-stop"]⟩
def allHandler : PIR.Handler unitSignature (Selected Cell allSlots) String :=
  fun _ state => ⟨.returned (), (fun slot => match slot with
    | ⟨.ticket, _⟩ => state ⟨.ticket, trivial⟩
    | ⟨.quota, _⟩ => 0
    | ⟨.outside, _⟩ => "admitted-now"), ["all"]⟩
def unitCall : PIR.Proc unitSignature Unit := .call () .done

example : (unitCall.run (scopeHandler noSlots emptyHandler) initial).outcome = .stopped .abort := by cbv
example : (unitCall.run (scopeHandler noSlots emptyHandler) initial).state = initial := by
  funext slot
  exact run_frame noSlots initial emptyHandler unitCall slot (by simp)
example : (unitCall.run (scopeHandler allSlots allHandler) initial).state .outside = "admitted-now" := by cbv
example : (unitCall.run (scopeHandler allSlots allHandler) initial).state .quota = 0 := by cbv

end Tests.ResourceView

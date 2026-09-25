import Zkc.Semantics.ExecutionPath
import Zkc.Protocols.CorrelatedSetup.ServiceCache

set_option autoImplicit false
namespace Zkc.Protocols.CorrelatedSetup.Execution
open PIR
open Zkc.Protocols.CorrelatedSetup Zkc.Probability.AdaptiveTape Zkc.Protocols.CorrelatedSetup.Service

inductive Op (F : Type) where
  | request : Request F → Op F
  | stop

inductive Role where | requester | responder

def Response (F : Type) (cut : Bool) : Type := if cut then F else F × F × F
def sig (F : Type) : Signature := ⟨Op F, fun
  | .request req => Response F req.cutAfterU
  | .stop => Unit⟩

variable {F : Type}

def deliver (cut : Bool) (uv : F × F) (tag : F) : Response F cut :=
  match cut with
  | true => uv.1
  | false => (uv.1,uv.2,tag)

def event (req : Request F) (reply : Response F req.cutAfterU) : Event F :=
  match req.cutAfterU, reply with
  | true, u => .response req u none none
  | false, (u,v,tag) => .response req u (some v) (some tag)

def receive (h : History F) (req : Request F) (reply : Response F req.cutAfterU) : History F :=
  ⟨h.events ++ [event req reply],false⟩

theorem receive_deliver (h : History F) (req : Request F) (uv : F × F) (tag : F) :
    receive h req (deliver req.cutAfterU uv tag) = appendResponse h req uv tag := by
  rcases req with ⟨star,challenge,cut⟩
  cases cut <;> rfl

def source (controller : Controller F) (p : Triple F) : Nat → History F → Proc (sig F) (History F)
  | 0, h => .done h
  | n+1, h => if h.halted then .done h else
      match controller p h with
      | none => .call .stop fun _ => .done ⟨h.events ++ [.stopped],true⟩
      | some req => .call (.request req) fun reply => source controller p n (receive h req reply)

/-- Protocol admission allows every request and every response of the requested
    delivery shape. The controller's honest/source arithmetic is not in enabled. -/
def interaction : Interaction (sig F) where
  Role := Role
  Phase := Nat × History F
  owner := fun _ => .requester
  enabled := fun phase _ => 0 < phase.1 ∧ phase.2.halted = false
  advance := fun phase op reply => match op with
    | .stop => (0,⟨phase.2.events ++ [.stopped],true⟩)
    | .request req => (phase.1-1,receive phase.2 req reply)

theorem formed (controller : Controller F) (p : Triple F) (n : Nat) (h : History F) :
    Conforms interaction (source controller p n h) (n,h) := by
  induction n generalizing h with
  | zero => trivial
  | succ n ih =>
    simp only [source]
    split
    · trivial
    · rename_i active
      have hh : h.halted = false := Bool.eq_false_iff.mpr active
      cases hc : controller p h with
      | none => exact ⟨⟨Nat.zero_lt_succ _,hh⟩,fun _ => trivial⟩
      | some req => exact ⟨⟨Nat.zero_lt_succ _,hh⟩,fun reply => ih _⟩

theorem bounded (controller : Controller F) (p : Triple F) (n : Nat) (h : History F) :
    Within n (source controller p n h) := by
  induction n generalizing h with
  | zero => trivial
  | succ n ih =>
    simp only [source]
    split
    · trivial
    · cases controller p h with
      | none => exact fun _ => by cases n <;> trivial
      | some req => exact fun reply => ih _

variable [CommRing F]

/-- The server owns witness-dependent computation and the residual tape.
    An empty provider is an explicit terminal exhaustion; controller stop
    consumes no randomness. Returned payloads follow the selected cut shape. -/
def handler (s : Setup F) (w : Witness F) (p : Triple F) :
    Handler (sig F) (History F × List F) (Event F)
  | .stop, (h,tape) => ⟨.returned (),(⟨h.events ++ [.stopped],true⟩,tape),[.stopped]⟩
  | .request _, (h,[]) => ⟨.stopped .exhausted,(h,[]),[]⟩
  | .request req, (h,r :: rest) =>
      let reply := deliver req.cutAfterU
        (actualResponse s (byPrefix s w p) req r) (tags s (publicationsOf w p)).2.2
      ⟨.returned reply,(receive h req reply,rest),[event req reply]⟩

def tapeList : (n : Nat) → Tape F n → List F
  | 0, _ => []
  | n+1, (r,rest) => r :: tapeList n rest

/-- The old fixed-horizon observer omits consumed-state information. This
    lemma only relates its History result, not its unrepresented residual tape. -/
theorem halted_history (s : Setup F) (w : Witness F) (controller : Controller F)
    (p : Triple F) (n : Nat) (h : History F) (tape : Tape F n) (halted : h.halted = true) :
    Zkc.Probability.AdaptiveTape.run (realStep s w controller p) n h tape = h := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih =>
    simpa [Zkc.Probability.AdaptiveTape.run,realStep,advance,halted] using ih h tape.2 halted

/-- Exact actual-history correspondence for every finite horizon and actual
    supplied controller, with sufficient tape. No uniformity assumption. -/
theorem history_exact (s : Setup F) (w : Witness F) (controller : Controller F)
    (p : Triple F) (n : Nat) (h : History F) (tape : Tape F n) :
    ((source controller p n h).run (handler s w p) (h,tapeList n tape)).outcome =
      .returned (Zkc.Probability.AdaptiveTape.run (realStep s w controller p) n h tape) := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih =>
    rcases tape with ⟨r,rest⟩
    by_cases hh : h.halted = true
    · simp [source,hh,Proc.run,halted_history s w controller p (n+1) h (r,rest) hh]
    · simp only [source,if_neg hh]
      cases hc : controller p h with
      | none =>
        simp only [Proc.run,handler,Execution.follow,Zkc.Probability.AdaptiveTape.run]
        have step : realStep s w controller p h r =
            ⟨h.events ++ [.stopped],true⟩ := by simp [realStep,advance,hh,hc]
        rw [step]
        rw [halted_history s w controller p n _ rest rfl]
      | some req =>
        simp only [Proc.run,tapeList,handler,Execution.follow]
        rw [ih,receive_deliver]
        simp [Zkc.Probability.AdaptiveTape.run,realStep,advance,hh,hc]

theorem history_retained (s : Setup F) (w : Witness F) (p : Triple F)
    (code : Proc (sig F) (History F)) (h : History F) (tape : List F) :
    (code.run (handler s w p) (h,tape)).state.1.events =
      h.events ++ (code.run (handler s w p) (h,tape)).events := by
  apply ExecutionPath.run_recorded (fun st : History F × List F => st.1.events)
  intro op st
  rcases st with ⟨history,tape⟩
  cases op with
  | stop => rfl
  | request req =>
    cases tape with
    | nil => simp [handler]
    | cons r rest => rfl

omit [CommRing F] in
theorem actual_calls_permitted (controller : Controller F) (p : Triple F) (n : Nat)
    (h : History F) (server : Handler (sig F) (History F × List F) (Event F)) (tape : List F) :
    ∀ phase op, Sum.inl (phase,op) ∈
      ((source controller p n h).run (ExecutionPath.handler interaction server) ((n,h),(h,tape))).events →
        interaction.enabled phase op :=
  ExecutionPath.calls_permitted interaction server _ _ _ (formed controller p n h)

end Zkc.Protocols.CorrelatedSetup.Execution

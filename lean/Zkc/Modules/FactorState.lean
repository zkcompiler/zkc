import Zkc.Modules.Factor


set_option autoImplicit false
namespace Zkc.Modules.FactorState
open Zkc.Modules.Factor

/-- Semantic writes. An adapter must cover every interpreted alias, not merely
    the nominal native handle it was passed. This is not a physical heap model. -/
structure Writes where
  bases : List Key
  views : List Nat
  challenges : List Nat
  deriving DecidableEq, Repr

variable {K : Type}

structure Frames (w : Writes) (before after : State K) : Prop where
  base : ∀ k, k ∉ w.bases → after.base k = before.base k
  view : ∀ h, h ∉ w.views → after.view h = before.view h
  challenge : ∀ i, i ∉ w.challenges → after.challenge i = before.challenge i

def unaffected (w : Writes) (f : Fact) : Bool := decide (
  f.key ∉ w.bases ∧ f.handle ∉ w.views ∧
    ∀ i ∈ f.applied, i ∉ w.challenges)

def keep (w : Writes) (facts : List Fact) : List Fact :=
  facts.filter (unaffected w)

theorem means_frame (w : Writes) (s t : State K) (f : Fact)
    (frame : Frames w s t) (old : Means s f) (safe : unaffected w f = true) :
    Means t f := by
  obtain ⟨hb,hv,hc⟩ := of_decide_eq_true safe
  have hm : f.applied.map t.challenge = f.applied.map s.challenge := by
    apply List.map_congr_left
    intro i hi
    exact frame.challenge i (hc i hi)
  intro tail ht
  rw [frame.view f.handle hv,frame.base f.key hb,hm]
  exact old tail ht

theorem keep_valid (w : Writes) (s t : State K) (facts : List Fact)
    (frame : Frames w s t) (valid : Valid s facts) : Valid t (keep w facts) := by
  intro f hf
  obtain ⟨member,safe⟩ := List.mem_filter.mp hf
  exact means_frame w s t f frame (valid f member) safe

/-- Unknown effects carry no framing premise and retain no facts. -/
def EffectFrame (w : Option Writes) (s t : State K) : Prop :=
  match w with
  | none => True
  | some w => Frames w s t

def survivors (w : Option Writes) (facts : List Fact) : List Fact :=
  match w with
  | none => []
  | some w => keep w facts

theorem survivors_valid (w : Option Writes) (s t : State K) (facts : List Fact)
    (frame : EffectFrame w s t) (valid : Valid s facts) :
    Valid t (survivors w facts) := by
  cases w with
  | none => simp [survivors,Valid]
  | some w => exact keep_valid w s t facts frame valid

def Writes.join (a b : Writes) : Writes :=
  ⟨a.bases ++ b.bases,a.views ++ b.views,a.challenges ++ b.challenges⟩

theorem frames_trans (a b : Writes) (s t u : State K)
    (first : Frames a s t) (second : Frames b t u) : Frames (a.join b) s u := by
  constructor
  · intro k hk
    have hn : k ∉ a.bases ∧ k ∉ b.bases := by simpa [Writes.join] using hk
    exact (second.base k hn.2).trans (first.base k hn.1)
  · intro h hh
    have hn : h ∉ a.views ∧ h ∉ b.views := by simpa [Writes.join] using hh
    exact (second.view h hn.2).trans (first.view h hn.1)
  · intro i hi
    have hn : i ∉ a.challenges ∧ i ∉ b.challenges := by simpa [Writes.join] using hi
    exact (second.challenge i hn.2).trans (first.challenge i hn.1)

/-- Guards are caller obligations for BOTH direct and reused evaluation. -/
def Ready (available : List Nat) (q : Query) : Prop :=
  q.point.length = q.key.axes.length ∧ ∀ i ∈ q.point, i ∈ available

instance (available : List Nat) (q : Query) : Decidable (Ready available q) :=
  inferInstanceAs (Decidable (_ ∧ _))

def checkReady (available : List Nat) (q : Query) : Bool := decide (Ready available q)

def checkPlan (facts : List Fact) (available : List Nat) (q : Query) (p : Plan) : Bool :=
  checkReady available q && check facts available q p

theorem checked_ready (facts : List Fact) (available : List Nat) (q : Query) (p : Plan)
    (accepted : checkPlan facts available q p = true) : Ready available q := by
  have h : checkReady available q = true ∧ check facts available q p = true := by
    simpa [checkPlan] using accepted
  exact of_decide_eq_true h.1

theorem checked_value (s : State K) (facts : List Fact) (available : List Nat)
    (q : Query) (p : Plan) (valid : Valid s facts)
    (accepted : checkPlan facts available q p = true) : runPlan s q p = runQuery s q := by
  have h : checkReady available q = true ∧ check facts available q p = true := by
    simpa [checkPlan] using accepted
  exact Zkc.Modules.Factor.checked_value s facts available q p valid h.2

end Zkc.Modules.FactorState

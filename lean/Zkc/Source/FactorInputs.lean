import Zkc.Modules.FactorState

set_option autoImplicit false

namespace Zkc.Source.FactorInputs
open Zkc.Modules.Factor

inductive Source where
  | base : Key → Source
  | fix : Source → Nat → Source
  deriving DecidableEq, Repr

def Source.key : Source → Key
  | .base k => k
  | .fix e _ => e.key

def Source.prefix : Source → List Nat
  | .base _ => []
  | .fix e i => e.prefix ++ [i]

def Source.eval {K : Type} (s : State K) : Source → List K → K
  | .base k, tail => s.base k tail
  | .fix e i, tail => e.eval s (s.challenge i :: tail)

theorem source_meaning {K : Type} (e : Source) (s : State K) (tail : List K) :
    e.eval s tail = s.base e.key (e.prefix.map s.challenge ++ tail) := by
  induction e generalizing tail with
  | base k => rfl
  | fix e i ih =>
    simpa [Source.eval,Source.key,Source.prefix,List.append_assoc] using
      ih (s.challenge i :: tail)

def Good (available : List Nat) (e : Source) : Prop :=
  e.prefix.length ≤ e.key.axes.length ∧ ∀ i ∈ e.prefix, i ∈ available

instance (available : List Nat) (e : Source) : Decidable (Good available e) :=
  inferInstanceAs (Decidable (_ ∧ _))

def check (available : List Nat) (e : Source) : Bool := decide (Good available e)

def fact (e : Source) (handle : Nat) : Fact :=
  ⟨e.key,handle,e.prefix,e.key.axes.length-e.prefix.length⟩

def install {K : Type} (s : State K) (e : Source) (handle : Nat) : State K :=
  overwrite s handle (e.eval s)

/-- Source-derived equality, with no caller-supplied Means assertion. Physical
    lowering still must implement this pure operation or expose the same law. -/
theorem installed_means {K : Type} (s : State K) (e : Source) (handle : Nat) :
    Means (install s e handle) (fact e handle) := by
  intro tail _
  simpa [Means,install,overwrite,fact] using source_meaning e s tail

theorem installed_valid {K : Type} (s : State K) (e : Source) (handle : Nat)
    (facts : List Fact) (valid : Valid s facts) :
    Valid (install s e handle) (remember (fact e handle) facts) := by
  have hi : install s e handle = retain s (fact e handle) := by
    unfold install retain
    congr 1
    funext tail
    exact source_meaning e s tail
  rw [hi]
  exact remember_valid s facts valid (fact e handle)

/-- Producer synthesis joins the existing checked caller; it does not replace
    the exact origin, ordered point, availability or post-effect checks. -/
theorem installed_caller {K : Type} (s : State K) (e : Source) (handle : Nat)
    (facts : List Fact) (available : List Nat) (q : Query) (plan : Plan)
    (valid : Valid s facts) (sourceOK : check available e = true)
    (accepted : Zkc.Modules.FactorState.checkPlan (remember (fact e handle) facts) available q plan = true) :
    Good available e ∧ Zkc.Modules.FactorState.Ready available q ∧
      runPlan (install s e handle) q plan = runQuery (install s e handle) q :=
  ⟨of_decide_eq_true sourceOK,Zkc.Modules.FactorState.checked_ready _ _ _ _ accepted,
    Zkc.Modules.FactorState.checked_value _ _ _ _ _ (installed_valid s e handle facts valid) accepted⟩

/-- The origin and ordered prefix are constructor indices. Each fix consumes
    one remaining axis and requires an available challenge reference. -/
inductive Typed (available : List Nat) : Key → List Nat → Nat → Type where
  | base (k : Key) : Typed available k [] k.axes.length
  | fix {k : Key} {applied : List Nat} {n : Nat}
      (e : Typed available k applied (n+1)) (i : Nat) (ready : i ∈ available) :
      Typed available k (applied ++ [i]) n

def Typed.erase {a : List Nat} {k : Key} : {p : List Nat} → {n : Nat} →
    Typed a k p n → Source
  | _,_,.base _ => .base k
  | _,_,.fix e i _ => .fix e.erase i

theorem typed_indices {a : List Nat} {k : Key} {p : List Nat} {n : Nat}
    (e : Typed a k p n) :
    e.erase.key = k ∧ e.erase.prefix = p ∧ p.length+n = k.axes.length ∧
      ∀ i ∈ p, i ∈ a := by
  induction e with
  | base => simp [Typed.erase,Source.key,Source.prefix]
  | @fix p n e i ready ih =>
    rcases ih with ⟨hk,hp,hlen,ha⟩
    refine ⟨hk,by simp [Typed.erase,Source.prefix,hp],?_,?_⟩
    · simp only [List.length_append,List.length_singleton]; omega
    · intro j hj
      simp only [List.mem_append,List.mem_singleton] at hj
      rcases hj with h | rfl
      · exact ha j h
      · exact ready

theorem typed_checked {a : List Nat} {k : Key} {p : List Nat} {n : Nat}
    (e : Typed a k p n) : check a e.erase = true := by
  rcases typed_indices e with ⟨hk,hp,hlen,ha⟩
  apply decide_eq_true
  simp only [Good,hk,hp]
  exact ⟨by omega,ha⟩

theorem checked_has_intrinsic (a : List Nat) (e : Source) (good : Good a e) :
    ∃ n, ∃ t : Typed a e.key e.prefix n, t.erase = e := by
  induction e with
  | base k => exact ⟨k.axes.length,.base k,rfl⟩
  | fix e i ih =>
    have ge : Good a e := by
      constructor
      · have h := good.1
        simp only [Source.prefix,Source.key,List.length_append,List.length_singleton] at h
        omega
      · intro j hj; exact good.2 j (by simp [Source.prefix,hj])
    rcases ih ge with ⟨n,t,ht⟩
    have hn := (typed_indices t).2.2.1
    cases n with
    | zero =>
      have h := good.1
      simp only [Source.prefix,Source.key,List.length_append,List.length_singleton] at h
      omega
    | succ n =>
      refine ⟨n,.fix t i (good.2 i (by simp [Source.prefix])),?_⟩
      change Source.fix t.erase i = Source.fix e i
      rw [ht]

theorem checked_iff_intrinsic (a : List Nat) (e : Source) :
    check a e = true ↔ ∃ n, ∃ t : Typed a e.key e.prefix n, t.erase = e := by
  constructor
  · intro h; exact checked_has_intrinsic a e (of_decide_eq_true h)
  · rintro ⟨n,t,ht⟩
    rw [← ht]
    exact typed_checked t

end Zkc.Source.FactorInputs

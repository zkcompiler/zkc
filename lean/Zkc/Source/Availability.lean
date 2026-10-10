import Std

set_option autoImplicit false
namespace Zkc.Source.Availability

/-- A narrow availability/value interface. None is unbound, never a public zero. -/
abbrev Env (F : Type) := Nat → Option F

def fromSlots {F : Type} (known : List Nat) (values : Nat → F) : Env F :=
  fun i => if i ∈ known then some (values i) else none

def Agree {F : Type} (scope : List Nat) (s t : Env F) : Prop :=
  ∀ i ∈ scope, s i = t i

def total {F : Type} [Zero F] (s : Env F) : Nat → F := fun i => (s i).getD 0

def ready {F : Type} (scope : List Nat) (s : Env F) (ds : List Nat) : Bool :=
  ds.all (fun i => decide (i ∈ scope) && (s i).isSome)

theorem ready_iff {F : Type} (scope : List Nat) (s : Env F) (ds : List Nat) :
    ready scope s ds = true ↔ ∀ i ∈ ds, i ∈ scope ∧ (s i).isSome = true := by
  simp [ready,List.all_eq_true]

theorem ready_agreement {F : Type} (scope : List Nat) (s t : Env F)
    (ds : List Nat) (h : Agree scope s t) : ready scope s ds = ready scope t ds := by
  unfold ready
  congr 1
  funext i
  by_cases hi : i ∈ scope
  · simp [hi,h i hi]
  · simp [hi]

/-- Availability is part of allowed agreement, not inferred from equal defaults. -/
theorem slots_agree {F : Type} (scope ks kt : List Nat) (s t : Nat → F)
    (available : ∀ i ∈ scope, i ∈ ks ↔ i ∈ kt)
    (values : ∀ i ∈ scope, i ∈ ks → s i = t i) :
    Agree scope (fromSlots ks s) (fromSlots kt t) := by
  intro i hi
  by_cases hk : i ∈ ks
  · simp [fromSlots,hk,(available i hi).mp hk,values i hi hk]
  · have ht : i ∉ kt := fun ht => hk ((available i hi).mpr ht)
    simp [fromSlots,hk,ht]

end Zkc.Source.Availability

import Zkc.Modules.FactorState


set_option autoImplicit false
namespace Zkc.Modules.FactorState
open Zkc.Modules.Factor
variable {K E : Type}

/-- Interpreted availability, not an epistemic or cryptographic knowledge model. -/
structure World (K : Type) where
  values : State K
  known : List Nat

def Known (s : World K) (available : List Nat) : Prop :=
  ∀ i ∈ available, i ∈ s.known

instance (s : World K) (available : List Nat) : Decidable (Known s available) :=
  inferInstanceAs (Decidable (∀ i ∈ available, i ∈ s.known))

/-- One returned outcome's sufficient analysis summary, not a universal PIR record. -/
structure Summary where
  writes : Option Writes
  exports : List Fact
  revoke : List Nat
  reveal : List Nat
  deriving Repr

def keptKnown (c : Summary) (available : List Nat) : List Nat :=
  match c.writes with
  | none => []
  | some w => available.filter (fun i => decide (i ∉ w.challenges ∧ i ∉ c.revoke))

def nextKnown (c : Summary) (available : List Nat) := c.reveal ++ keptKnown c available
def nextFacts (c : Summary) (facts : List Fact) := c.exports ++ survivors c.writes facts

/-- Contract facts refer to the actual post-state. A summary or a trusted flag
    is not itself a witness of this proposition. Both outcomes need a contract. -/
structure Justifies (c : Summary) (s t : World K) : Prop where
  frame : EffectFrame c.writes s.values t.values
  exports : Valid t.values c.exports
  availability : Known t (keptKnown c s.known)
  revealed : Known t c.reveal

theorem nextFacts_valid (c : Summary) (s t : World K) (facts : List Fact)
    (law : Justifies c s t) (old : Valid s.values facts) :
    Valid t.values (nextFacts c facts) := by
  intro f hf
  rcases List.mem_append.mp hf with hx | hx
  · exact law.exports f hx
  · exact survivors_valid c.writes s.values t.values facts law.frame old f hx

theorem keptKnown_mono (c : Summary) (a b : List Nat) (sub : ∀ i ∈ a, i ∈ b) :
    ∀ i ∈ keptKnown c a, i ∈ keptKnown c b := by
  cases h : c.writes with
  | none => simp [keptKnown,h]
  | some w =>
    intro i hi
    simp only [keptKnown,h] at hi ⊢
    obtain ⟨hm,hp⟩ := List.mem_filter.mp hi
    exact List.mem_filter.mpr ⟨sub i hm,hp⟩

theorem nextKnown_sound (c : Summary) (s t : World K) (available : List Nat)
    (law : Justifies c s t) (old : Known s available) :
    Known t (nextKnown c available) := by
  intro i hi
  rcases List.mem_append.mp hi with hr | hk
  · exact law.revealed i hr
  · exact law.availability i (keptKnown_mono c available s.known old i hk)

theorem ready_actual (s : World K) (available : List Nat) (q : Query)
    (known : Known s available) (ready : Ready available q) : Ready s.known q :=
  ⟨ready.1,fun i hi => known i (ready.2 i hi)⟩

structure Returned (K E : Type) where
  success : Bool
  world : World K
  events : List E

structure Spec (K : Type) where
  pre : World K → Prop
  post : Bool → Summary

abbrev Implementation (K E : Type) := World K → Returned K E

/-- Native implementations may satisfy this by an explicit trust assumption.
    Common compiler theorems take the proposition as a premise. -/
def Satisfies (spec : Spec K) (impl : Implementation K E) : Prop :=
  ∀ s, spec.pre s → Justifies (spec.post (impl s).success) s (impl s).world

theorem call_transfer (spec : Spec K) (impl : Implementation K E)
    (law : Satisfies spec impl) (s : World K) (facts : List Fact) (available : List Nat)
    (legal : spec.pre s) (valid : Valid s.values facts) (known : Known s available) :
    Valid (impl s).world.values (nextFacts (spec.post (impl s).success) facts) ∧
    Known (impl s).world (nextKnown (spec.post (impl s).success) available) :=
  ⟨nextFacts_valid _ _ _ _ (law s legal) valid,
   nextKnown_sound _ _ _ _ (law s legal) known⟩

end Zkc.Modules.FactorState

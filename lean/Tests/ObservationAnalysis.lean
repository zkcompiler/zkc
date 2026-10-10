import Zkc.Compiler.Analysis.Observation
import Zkc.Semantics.Locality
import Zkc.Compiler.Analysis.FactorMerge

namespace Tests.ObservationAnalysis

open Zkc.Compiler.Analysis Zkc.Semantics.Locality

def means (summary : Option Bool) (actual : Bool) : Prop :=
  summary = none ∨ summary = some actual

theorem exact_sound : SummarySound id some means := fun _ => Or.inr rfl

/-- Erasing a Boolean and computing only an unknown summary is sound. -/
theorem unknown_sound :
    SummarySound id ((fun _ : Unit => (none : Option Bool)) ∘ (fun _ : Bool => ())) means :=
  fun _ => Or.inl rfl

theorem weaken_to_unknown : SummarySound id ((fun _ => none) ∘ some) means :=
  exact_sound.weaken (fun _ => none) means (fun _ _ _ => Or.inl rfl)

theorem erased_value_cannot_be_recovered :
    ¬ ∃ recover : Unit → Bool, ∀ actual : Bool, recover () = actual := by
  rintro ⟨recover, law⟩
  have impossible := local_factor_necessary (fun _ : Bool => ()) id recover law false true rfl
  cases impossible

theorem unknown_cannot_justify_false : ¬ ∀ actual, means none actual → actual = false := by
  intro established
  have impossible := established true (Or.inl rfl)
  cases impossible

theorem guessing_is_unsound : ¬ SummarySound id (fun _ => some false) means := by
  intro sound
  have impossible := sound true
  simp [means] at impossible

/-- A fact actually established by an exact summary is usable. -/
theorem exact_summary_justifies_fact : (id false : Bool) = false := by
  apply exact_sound.use false (fun actual => actual = false)
  intro actual h
  simpa [means] using h

/-- The existing conservative merge is a client of the common summary law.
The actual state satisfies one branch's conjunction; retained facts hold there. -/
theorem merged_facts_sound {S : Type} (truth : Nat → S → Prop)
    (left right : List Nat)
    (valid : ∀ s, (∀ a ∈ left, truth a s) ∨ (∀ a ∈ right, truth a s)) :
    SummarySound id (fun _ : S => Zkc.Compiler.FactorMerge.common left right)
      (fun facts s => ∀ a ∈ facts, truth a s) :=
  fun s => Zkc.Compiler.FactorMerge.common_sound (fun a => truth a s) left right (valid s)

open Zkc.Modules.Factor Zkc.Modules.FactorState Zkc.Compiler.FactorMerge in
/-- Facts and availability describe the same reached world. Each list first
merges alternative exits conservatively; their meanings then combine by conjunction. -/
theorem merged_facts_and_availability {K : Type}
    (summaries : Bool → Summary) (before : World K) (after : Bool → World K)
    (law : ∀ outcome, Justifies (summaries outcome) before (after outcome))
    (oldFacts : List Fact) (oldKnown : List Nat)
    (valid : Valid before.values oldFacts) (known : Known before oldKnown) :
    SummarySound after (fun _ => (facts summaries oldFacts, available summaries oldKnown))
      (fun summary world => Valid world.values summary.1 ∧ Known world summary.2) := by
  apply SummarySound.combine
    (firstMeans := fun facts world => Valid world.values facts)
    (secondMeans := fun known world => Known world known)
  · intro outcome
    exact facts_valid summaries before (after outcome) outcome (law outcome) oldFacts valid
  · intro outcome
    exact available_known summaries before (after outcome) outcome (law outcome) oldKnown known

/-- A retained construction parameter permits an exact specialized consumer. -/
theorem retained_configuration (binding value : Bool) :
    (fun p : Bool × Bool => p.1 != p.2) (binding, value) = (binding != value) := rfl

theorem erased_configuration_has_no_uniform_consumer :
    ¬ ∃ consume : Bool → Bool, ∀ p : Bool × Bool, consume p.2 = (p.1 != p.2) := by
  rintro ⟨consume, law⟩
  have impossible := local_factor_necessary Prod.snd (fun p : Bool × Bool => p.1 != p.2)
    consume law (false, false) (true, false) rfl
  cases impossible

/-- Keeping just a modular value supports a modular consumer but cannot serve
a remaining exact integer consumer. Both requirements matter before a split. -/
theorem modular_value_cannot_supply_integer :
    ¬ ∃ consume : Nat → Nat, ∀ n : Nat, consume (n % 7) = n := by
  rintro ⟨consume, law⟩
  have impossible := local_factor_necessary (fun n : Nat => n % 7) id consume law 0 7 (by decide)
  cases impossible

end Tests.ObservationAnalysis

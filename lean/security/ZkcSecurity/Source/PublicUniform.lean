module

public import ZkcSecurity.Source.PublicProperties
public import ZkcSecurity.FiatShamir.OccurrenceReading

@[expose] public section

/-! Uniform field laws at every actual nominal request. Static source sites
never replace dynamic oracle origins: the conclusion quantifies over them. -/
set_option autoImplicit false
namespace ZkcSecurity.Source.PublicUniform
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.FiatShamir OracleComp OracleSpec
variable {F G : Type} [SampleableType F]
attribute [local instance] OccurrenceReading.rawSampleable

theorem bound (price : ENNReal) (site field : String) (handle : Nat)
    (bad : F → Prop) (bounded : Pr{let r ← $ᵗ F}[bad r] ≤ price)
    (history : List (PublicProperties.Event (uniformCarriers F G))) :
    PublicProperties.escape price history (.challenge site field handle) bad := by
  intro origin request
  rcases origin with ⟨entry, events, selected⟩
  dsimp only at request
  subst selected
  exact bounded

theorem empty (price : ENNReal)
    (history : List (PublicProperties.Event (uniformCarriers F G)))
    (event : PublicProperties.Event (uniformCarriers F G)) :
    PublicProperties.escape price history event (fun _ => False) := by
  cases event <;> try trivial
  intro origin request
  simp

end ZkcSecurity.Source.PublicUniform

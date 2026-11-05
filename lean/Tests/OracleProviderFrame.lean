import Zkc.Source.Structured.OracleProviderFrame

set_option autoImplicit false
open Zkc.Source.Structured.OracleProviderFrame Std.Do.Internal

namespace Tests.OracleProviderFrame

/-- Extract an actual complete result's predicate in the deterministic specialization. -/
theorem id_post {A : Type} {post : A → Prop} {value : Id A}
    (law : Ensures post value) : post value := by
  obtain ⟨checked, erase⟩ := law.exists_refinement
  have same : checked.val = value := erase.map_eq
  rw [← same]
  exact checked.property

/-- Every branch, including stopped records, is covered; no chosen representative branch. -/
theorem list_post {A : Type} {post : A → Prop} {values : List A}
    (law : Ensures post values) (value : A) (member : value ∈ values) : post value := by
  obtain ⟨checked, erase⟩ := law.exists_refinement
  have mapped : values = checked.map Subtype.val := by simpa using erase.map_eq.symm
  rw [mapped] at member
  obtain ⟨result, _, same⟩ := List.mem_map.mp member
  exact same ▸ result.property

example : Ensures (m := Except String) (fun value : Nat ↦ value = 0) (.error "outer") :=
  Zkc.MonadicPostcondition.of_refinement (.error "outer") rfl

example : Ensures (m := List) (fun value : Nat ↦ value ≤ 2) [0, 2] :=
  Zkc.MonadicPostcondition.of_refinement [⟨0, by decide⟩, ⟨2, by decide⟩] rfl

example : ∀ value ∈ ([0, 2] : List Nat), value ≤ 2 := by
  intro value member
  apply list_post (values := [0, 2]) _ value member
  exact Zkc.MonadicPostcondition.of_refinement [⟨0, by decide⟩, ⟨2, by decide⟩] rfl

end Tests.OracleProviderFrame

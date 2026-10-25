module

public import Zkc.Source.RegionDecoding

@[expose] public section

/-! Same-value interpretation congruence over the exact stored operation inventory.
Nested callbacks and stopped suffixes remain in that inventory. No reachability
or operation-totality assumption is required.
-/
set_option autoImplicit false
namespace Zkc.Source

abbrev RegionOperations (dialect : Dialect) (Value : dialect.Ty → Type)
    (interface : PIR.Signature) :=
  (op : dialect.Op) → Values Value (dialect.arguments op) →
    Values (RegionFunction Value interface) (dialect.regions op) →
      PIR.Process interface (Values Value (dialect.results op))

variable {dialect : Dialect} {interface : PIR.Signature} {Value : dialect.Ty → Type}

theorem Region.denote_congr (left right : RegionOperations dialect Value interface)
    {Γ out} (region : Region dialect Γ out)
    (agree : ∀ op ∈ region.erase.operations, left op = right op) :
    region.denote ⟨Value, left⟩ = region.denote ⟨Value, right⟩ := by
  induction region using Region.rec
      (motive_2 := fun signatures bodies =>
        (∀ op ∈ bodies.erase.operations, left op = right op) →
        bodies.denote ⟨Value, left⟩ = bodies.denote ⟨Value, right⟩) with
  | ret values => rfl
  | stop reason => rfl
  | letOp op args bodies next bodiesIH nextIH =>
    have operationAgree := agree op (by simp [Region.erase, RawRegion.operations])
    have bodiesAgree : ∀ op ∈ bodies.erase.operations, left op = right op := by
      intro op member
      exact agree op (by
        simp only [Region.erase, RawRegion.operations, List.mem_cons,
          List.mem_append]
        exact Or.inr (Or.inl member))
    have nextAgree : ∀ op ∈ next.erase.operations, left op = right op := by
      intro op member
      exact agree op (by
        simp only [Region.erase, RawRegion.operations, List.mem_cons,
          List.mem_append]
        exact Or.inr (Or.inr member))
    funext env
    simp only [Region.denote, bodiesIH bodiesAgree, nextIH nextAgree, operationAgree]
  | bind body next bodyIH nextIH =>
    have bodyAgree : ∀ op ∈ body.erase.operations, left op = right op := by
      intro op member
      exact agree op (by
        simp only [Region.erase, RawRegion.operations, List.mem_append]
        exact Or.inl member)
    have nextAgree : ∀ op ∈ next.erase.operations, left op = right op := by
      intro op member
      exact agree op (by
        simp only [Region.erase, RawRegion.operations, List.mem_append]
        exact Or.inr member)
    funext env
    simp only [Region.denote, bodyIH bodyAgree, nextIH nextAgree]
  | nil => rfl
  | cons body tail bodyIH tailIH =>
    rename_i agree
    have bodyAgree : ∀ op ∈ body.erase.operations, left op = right op := by
      intro op member
      exact agree op (by
        simp only [Regions.erase, RawRegions.operations, List.mem_append]
        exact Or.inl member)
    have tailAgree : ∀ op ∈ tail.erase.operations, left op = right op := by
      intro op member
      exact agree op (by
        simp only [Regions.erase, RawRegions.operations, List.mem_append]
        exact Or.inr member)
    simp only [Regions.denote, bodyIH bodyAgree, tailIH tailAgree]

theorem Regions.denote_congr (left right : RegionOperations dialect Value interface)
    {signatures} (bodies : Regions dialect signatures)
    (agree : ∀ op ∈ bodies.erase.operations, left op = right op) :
    bodies.denote ⟨Value, left⟩ = bodies.denote ⟨Value, right⟩ := by
  induction bodies using Regions.rec (motive_1 := fun _ _ _ => True) with
  | ret => trivial
  | stop => trivial
  | letOp => trivial
  | bind => trivial
  | nil => rfl
  | cons body tail _ tailIH =>
    have bodyAgree : ∀ op ∈ body.erase.operations, left op = right op := by
      intro op member
      exact agree op (by
        simp only [Regions.erase, RawRegions.operations, List.mem_append]
        exact Or.inl member)
    have tailAgree : ∀ op ∈ tail.erase.operations, left op = right op := by
      intro op member
      exact agree op (by
        simp only [Regions.erase, RawRegions.operations, List.mem_append]
        exact Or.inr member)
    simp only [Regions.denote, Region.denote_congr left right body bodyAgree, tailIH tailAgree]

end Zkc.Source

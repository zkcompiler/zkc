module

public import Zkc.Source.Component
public import Zkc.Source.RegionCongruence

@[expose] public section

/-! Component framing needs agreement on both optional operations and the
nonoptional operations used to interpret their closed callbacks. -/
set_option autoImplicit false
namespace Zkc.Source

variable {dialect : Dialect} {interface : PIR.Signature} {Value : dialect.Ty → Type}

theorem Region.component_congr (left right : RegionOperations dialect Value interface)
    (leftComponent : ComponentOperations ⟨Value, left⟩)
    (rightComponent : ComponentOperations ⟨Value, right⟩)
    {Γ out} (region : Region dialect Γ out)
    (closedAgree : ∀ op ∈ region.erase.operations, left op = right op)
    (componentAgree : ∀ op ∈ region.erase.operations, leftComponent op = rightComponent op) :
    region.component ⟨Value, left⟩ leftComponent =
      region.component ⟨Value, right⟩ rightComponent := by
  induction region using Region.rec (motive_2 := fun _ _ => True) with
  | ret values => rfl
  | stop reason => rfl
  | letOp op args bodies next _ nextIH =>
    have operationAgree := componentAgree op (by simp [Region.erase, RawRegion.operations])
    have bodiesAgree : ∀ op ∈ bodies.erase.operations, left op = right op := by
      intro op member
      exact closedAgree op (by
        simp only [Region.erase, RawRegion.operations, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inl member))
    have nextClosed : ∀ op ∈ next.erase.operations, left op = right op := by
      intro op member
      exact closedAgree op (by
        simp only [Region.erase, RawRegion.operations, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inr member))
    have nextComponent : ∀ op ∈ next.erase.operations, leftComponent op = rightComponent op := by
      intro op member
      exact componentAgree op (by
        simp only [Region.erase, RawRegion.operations, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inr member))
    funext env
    simp only [Region.component, Regions.denote_congr left right bodies bodiesAgree,
      operationAgree, nextIH nextClosed nextComponent]
  | bind body next bodyIH nextIH =>
    have bodyClosed : ∀ op ∈ body.erase.operations, left op = right op := by
      intro op member
      exact closedAgree op (by
        simp only [Region.erase, RawRegion.operations, List.mem_append]
        exact Or.inl member)
    have nextClosed : ∀ op ∈ next.erase.operations, left op = right op := by
      intro op member
      exact closedAgree op (by
        simp only [Region.erase, RawRegion.operations, List.mem_append]
        exact Or.inr member)
    have bodyComponent : ∀ op ∈ body.erase.operations, leftComponent op = rightComponent op := by
      intro op member
      exact componentAgree op (by
        simp only [Region.erase, RawRegion.operations, List.mem_append]
        exact Or.inl member)
    have nextComponent : ∀ op ∈ next.erase.operations, leftComponent op = rightComponent op := by
      intro op member
      exact componentAgree op (by
        simp only [Region.erase, RawRegion.operations, List.mem_append]
        exact Or.inr member)
    funext env
    simp only [Region.component, bodyIH bodyClosed bodyComponent, nextIH nextClosed nextComponent]
  | nil => trivial
  | cons => trivial

end Zkc.Source

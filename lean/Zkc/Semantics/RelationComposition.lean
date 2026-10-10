import Zkc.Semantics.Relation

/-! Connections between component relations at their actual boundary values.

Each component can expose a different type. A connector relates those values;
local witnesses can be hidden inside the component predicates, but a boundary
used by the connector remains free until the connection is formed. These are
predicate laws, not cryptographic composition or witness-generation algorithms.
-/

namespace PIR.Relation

variable {A B U V : Type}

/-- A connection uses jointly compatible boundary values, not independently
closed component validity. Inputs and configuration are fixed by the predicates. -/
def Connected (left : A → Prop) (connect : A → B → Prop) (right : B → Prop) : Prop :=
  ∃ a b, left a ∧ connect a b ∧ right b

/-- Pointwise replacement preserves every connector on these boundary types. -/
theorem Connected.congr {left left' : A → Prop} {right right' : B → Prop}
    (connect : A → B → Prop)
    (leftExact : ∀ a, left a ↔ left' a) (rightExact : ∀ b, right b ↔ right' b) :
    Connected left connect right ↔ Connected left' connect right' := by
  constructor
  · rintro ⟨a, b, ha, hab, hb⟩
    exact ⟨a, b, (leftExact a).mp ha, hab, (rightExact b).mp hb⟩
  · rintro ⟨a, b, ha, hab, hb⟩
    exact ⟨a, b, (leftExact a).mpr ha, hab, (rightExact b).mpr hb⟩

/-- Contextual replacement can remove checks supplied by the connected
component. The second premise uses the already-replaced left component; two
replacements cannot each assume a check removed by the other. This conclusion
is for the linked context, not unconditional interchangeability of a component. -/
theorem Connected.replace {left left' : A → Prop} {right right' : B → Prop}
    (connect : A → B → Prop)
    (leftExact : ∀ a b, connect a b → right b → (left a ↔ left' a))
    (rightExact : ∀ a b, connect a b → left' a → (right b ↔ right' b)) :
    Connected left connect right ↔ Connected left' connect right' := by
  constructor
  · rintro ⟨a, b, ha, hab, hb⟩
    have ha' := (leftExact a b hab hb).mp ha
    exact ⟨a, b, ha', hab, (rightExact a b hab ha').mp hb⟩
  · rintro ⟨a, b, ha, hab, hb⟩
    have hb' := (rightExact a b hab ha).mpr hb
    exact ⟨a, b, (leftExact a b hab hb').mpr ha, hab, hb'⟩

/-- Representation change needs coverage of valid source boundaries and an
exact image of each component. The connector law applies only to valid related
values. Representations need not be functions, bijections or equal layouts. -/
theorem Connected.represented
    (left : A → Prop) (right : B → Prop)
    (targetLeft : U → Prop) (targetRight : V → Prop)
    (leftRep : A → U → Prop) (rightRep : B → V → Prop)
    (connect : A → B → Prop) (targetConnect : U → V → Prop)
    (leftCovered : ∀ a, left a → ∃ u, leftRep a u)
    (rightCovered : ∀ b, right b → ∃ v, rightRep b v)
    (leftImage : ∀ u, targetLeft u ↔ ∃ a, left a ∧ leftRep a u)
    (rightImage : ∀ v, targetRight v ↔ ∃ b, right b ∧ rightRep b v)
    (compatible : ∀ a b u v, left a → right b → leftRep a u → rightRep b v →
      (targetConnect u v ↔ connect a b)) :
    Connected targetLeft targetConnect targetRight ↔ Connected left connect right := by
  constructor
  · rintro ⟨u, v, hu, huv, hv⟩
    obtain ⟨a, ha, hau⟩ := (leftImage u).mp hu
    obtain ⟨b, hb, hbv⟩ := (rightImage v).mp hv
    exact ⟨a, b, ha, (compatible a b u v ha hb hau hbv).mp huv, hb⟩
  · rintro ⟨a, b, ha, hab, hb⟩
    obtain ⟨u, hau⟩ := leftCovered a ha
    obtain ⟨v, hbv⟩ := rightCovered b hb
    exact ⟨u, v, (leftImage u).mpr ⟨a, ha, hau⟩,
      (compatible a b u v ha hb hau hbv).mpr hab, (rightImage v).mpr ⟨b, hb, hbv⟩⟩

end PIR.Relation

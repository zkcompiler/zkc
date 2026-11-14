module

public import Zkc.Core.Endpoints

public section

/-! The values of a part of a side.

A side that is the union of two disjoint sides holds every value that either holds. The
restriction of a held value to a part is the value when the part holds it and the unit
value otherwise (`Held.left`, `Held.right`); `restrictLeft` and `restrictRight` are the
restrictions of the value of a located type. The lemmas say that restriction commutes
with the operations on value lists that the meaning of a protocol operation uses.
-/

set_option autoImplicit false

namespace Zkc.Source

variable {Ty : Type} {V W : Ty → Type}

namespace Values

@[simp] theorem map_nil (f : {ty : Ty} → V ty → W ty) :
    (Values.nil : Values V []).map f = .nil := rfl

@[simp] theorem map_cons (f : {ty : Ty} → V ty → W ty) {ty : Ty} {Γ : List Ty} (value : V ty)
    (rest : Values V Γ) : (Values.cons value rest).map f = .cons (f value) (rest.map f) := rfl

theorem map_get (f : {ty : Ty} → V ty → W ty) :
    ∀ {Γ : List Ty} (values : Values V Γ) {ty : Ty} (position : Var Γ ty),
      (values.map f).get position = f (values.get position)
  | _, .nil, _, position => position.elimNil
  | _, .cons value rest, _, position => by
      cases position with
      | here => rfl
      | there position => exact map_get f rest position

theorem map_tail (f : {ty : Ty} → V ty → W ty) {ty : Ty} {Γ : List Ty}
    (values : Values V (ty :: Γ)) : (values.map f).tail = values.tail.map f := by
  cases values; rfl

theorem map_append (f : {ty : Ty} → V ty → W ty) :
    ∀ {Γ Δ : List Ty} (first : Values V Γ) (second : Values V Δ),
      (first.append second).map f = (first.map f).append (second.map f)
  | _, _, .nil, _ => rfl
  | _, _, .cons value rest, second => by
      show Values.cons (f value) ((rest.append second).map f) = _
      rw [map_append f rest second]
      rfl

theorem map_split (f : {ty : Ty} → V ty → W ty) :
    ∀ (added : List Ty) {Γ : List Ty} (values : Values V (added ++ Γ)),
      (values.map f).split added =
        ((values.split added).1.map f, (values.split added).2.map f)
  | [], _, _ => rfl
  | _ :: added, _, .cons value values => by
      have tail := map_split f added values
      show (Values.cons (f value) (Values.split added (values.map f)).1,
        (Values.split added (values.map f)).2) = _
      rw [tail]
      rfl

end Values

/-- An environment whose values are those of another one under a map. -/
structure Restricts {Γ : List Ty} (f : {ty : Ty} → V ty → W ty) (env : Environment V Γ)
    (part : Environment W Γ) : Prop where
  value : ∀ {ty : Ty} (reference : Var Γ ty), part reference = f (env reference)

namespace Restricts

variable {f : {ty : Ty} → V ty → W ty}

theorem eval {Γ : List Ty} {env : Environment V Γ} {part : Environment W Γ}
    (restricts : Restricts f env part) :
    ∀ {types : List Ty} (operands : Operands Γ types),
      Operands.eval part operands = (Operands.eval env operands).map f
  | _, .nil => rfl
  | _, .cons reference rest =>
      congr (congrArg Values.cons (restricts.value reference)) (eval restricts rest)

theorem push {Γ : List Ty} {env : Environment V Γ} {part : Environment W Γ}
    (restricts : Restricts f env part) {ty : Ty} (value : V ty) :
    Restricts f (env.push value) (part.push (f value)) := by
  refine ⟨?_⟩
  intro other reference
  cases reference with
  | here => rfl
  | there reference => exact restricts.value reference

theorem bindAll :
    ∀ {added Γ : List Ty} {env : Environment V Γ} {part : Environment W Γ},
      Restricts f env part → ∀ (values : Values V added),
        Restricts f (Environment.bindAll env values) (Environment.bindAll part (values.map f))
  | _, _, _, _, restricts, .nil => restricts
  | _, _, _, _, restricts, .cons value rest => bindAll (restricts.push value) rest

theorem ofValues {Γ : List Ty} (values : Values V Γ) :
    Restricts f (Environment.ofValues values) (Environment.ofValues (values.map f)) :=
  bindAll ⟨fun reference => reference.elimNil⟩ values

end Restricts

end Zkc.Source

namespace Zkc.Core

open Zkc.Source

theorem unmapValues_map {α β : Type} {F G : β → Type} (g : α → β) (f : {item : β} → F item → G item) :
    ∀ (items : List α) (values : Values F (items.map g)),
      unmapValues g items (values.map f) =
        (unmapValues g items values).map (fun {item} value => f (item := g item) value)
  | [], _ => rfl
  | _ :: rest, .cons value values =>
      congrArg (Values.cons (Value := fun item => G (g item)) (f value))
        (unmapValues_map g f rest values)

theorem remapValues_map {α β : Type} {F G : β → Type} (g : α → β) (f : {item : β} → F item → G item) :
    ∀ (items : List α) (values : Values (fun item => F (g item)) items),
      (remapValues g items values).map f =
        remapValues g items (values.map (fun {item} value => f (item := g item) value))
  | [], _ => rfl
  | _ :: rest, .cons value values => by
      have tail := remapValues_map (F := F) (G := G) g f rest values
      exact congrArg (Values.cons (Value := G) (f value)) tail

theorem split_map {Ty : Type} {V W : Ty → Type} (f : {ty : Ty} → V ty → W ty) :
    ∀ (added : List Ty) {Γ : List Ty} (values : Values V (added ++ Γ)),
      Values.split added (values.map f) =
        ((Values.split added values).1.map f, (Values.split added values).2.map f)
  | [], _, _ => rfl
  | _ :: added, _, .cons value values => by
      show (Values.cons (f value) (Values.split added (values.map f)).1,
        (Values.split added (values.map f)).2) = _
      rw [split_map f added values]
      rfl

/-- The union of two sides. -/
@[expose, reducible] def Side.union (first second : Side) : Side := fun role => first role || second role

/-- No role is in both sides. -/
@[expose] def Side.Disjoint (first second : Side) : Prop := ∀ role, (first role && second role) = false

namespace Held

variable {X : Type}

/-- The first part's share of a value held by a union. -/
@[expose] def left : (first second : Bool) → Held X (first || second) → Held X first
  | true, _, value => value
  | false, _, _ => PUnit.unit

/-- The second part's share of a value held by a union. -/
@[expose] def right : (first second : Bool) → Held X (first || second) → Held X second
  | true, true, value => value
  | false, true, value => value
  | _, false, _ => PUnit.unit

/-- A holder outside a side has one value. -/
theorem absent_unique : ∀ (present : Bool), present = false → ∀ (one other : Held X present),
    one = other
  | false, _, _, _ => rfl

theorem left_of : ∀ (first second : Bool) (value : X),
    left first second (Held.of (first || second) value) = Held.of first value
  | true, _, _ => rfl
  | false, _, _ => rfl

theorem right_of : ∀ (first second : Bool) (value : X),
    right first second (Held.of (first || second) value) = Held.of second value
  | true, true, _ => rfl
  | false, true, _ => rfl
  | true, false, _ => rfl
  | false, false, _ => rfl

theorem left_map {Y : Type} (f : X → Y) :
    ∀ (first second : Bool) (held : Held X (first || second)),
      Held.map f first (left first second held) =
        left first second (Held.map f (first || second) held)
  | true, _, _ => rfl
  | false, _, _ => rfl

theorem right_map {Y : Type} (f : X → Y) :
    ∀ (first second : Bool) (held : Held X (first || second)),
      Held.map f second (right first second held) =
        right first second (Held.map f (first || second) held)
  | true, true, _ => rfl
  | false, true, _ => rfl
  | true, false, _ => rfl
  | false, false, _ => rfl

theorem left_map₂ {Y Z : Type} (f : X → Y → Z) :
    ∀ (first second : Bool) (one : Held X (first || second)) (other : Held Y (first || second)),
      Held.map₂ f first (left first second one) (left first second other) =
        left first second (Held.map₂ f (first || second) one other)
  | true, _, _, _ => rfl
  | false, _, _, _ => rfl

theorem right_map₂ {Y Z : Type} (f : X → Y → Z) :
    ∀ (first second : Bool) (one : Held X (first || second)) (other : Held Y (first || second)),
      Held.map₂ f second (right first second one) (right first second other) =
        right first second (Held.map₂ f (first || second) one other)
  | true, true, _, _ => rfl
  | false, true, _, _ => rfl
  | true, false, _, _ => rfl
  | false, false, _, _ => rfl

theorem value_left : ∀ (first second : Bool) (member : first = true)
    (whole : (first || second) = true) (held : Held X (first || second)),
    Held.value first member (left first second held) = Held.value (first || second) whole held
  | true, _, _, _, _ => rfl

theorem value_right : ∀ (first second : Bool) (member : second = true)
    (whole : (first || second) = true) (held : Held X (first || second)),
    Held.value second member (right first second held) = Held.value (first || second) whole held
  | true, true, _, _, _ => rfl
  | false, true, _, _, _ => rfl

end Held

section Lists

variable {X : Ty → Type}

/-- Values that the first part holds are their own share. -/
theorem map_left_present (second : Bool) :
    ∀ {types : List Ty} (values : Values (fun type => Held (X type) (true || second)) types),
      values.map (fun {type} value => Held.left (X := X type) true second value) = values
  | _, .nil => rfl
  | _, .cons value rest =>
      congrArg (Values.cons (Value := fun type => Held (X type) true) value)
        (map_left_present second rest)

/-- Values that the second part holds are their own share. -/
theorem map_right_present :
    ∀ {types : List Ty} (values : Values (fun type => Held (X type) (false || true)) types),
      values.map (fun {type} value => Held.right (X := X type) false true value) = values
  | _, .nil => rfl
  | _, .cons value rest =>
      congrArg (Values.cons (Value := fun type => Held (X type) true) value)
        (map_right_present rest)

/-- Values of a holder outside a side are equal. -/
theorem absent_values_unique :
    ∀ {types : List Ty} (one other : Values (fun type => Held (X type) false) types), one = other
  | _, .nil, .nil => rfl
  | _, .cons value rest, .cons other others =>
      congr (congrArg Values.cons (Held.absent_unique false rfl value other))
        (absent_values_unique rest others)

end Lists

section Sides

variable (model : Model) (first second : Side)

/-- The first part's share of a value of a located type. -/
@[expose, reducible] def restrictLeft {located : Located}
    (value : SideValue model (first.union second) located) : SideValue model first located :=
  Held.left (first located.holder) (second located.holder) value

/-- The second part's share. -/
@[expose, reducible] def restrictRight {located : Located}
    (value : SideValue model (first.union second) located) : SideValue model second located :=
  Held.right (first located.holder) (second located.holder) value

/-- The first part's shares of values of located types. -/
abbrev leftValues {types : List Located} (values : Values (SideValue model (first.union second)) types) :
    Values (SideValue model first) types :=
  values.map (fun {located} value => restrictLeft model first second (located := located) value)

/-- The second part's shares. -/
abbrev rightValues {types : List Located}
    (values : Values (SideValue model (first.union second)) types) :
    Values (SideValue model second) types :=
  values.map (fun {located} value => restrictRight model first second (located := located) value)

variable {model} {first second}

/-- Values held by roles outside a side are equal. -/
theorem outside_values_unique {side : Side} :
    ∀ {types : List Located}, (∀ located ∈ types, side located.holder = false) →
      ∀ (one other : Values (SideValue model side) types), one = other
  | _, _, .nil, .nil => rfl
  | located :: _, outside, .cons value rest, .cons otherValue others =>
      congr
        (congrArg Values.cons
          (Held.absent_unique (side located.holder) (outside located (List.mem_cons_self ..)) value
            otherValue))
        (outside_values_unique (fun other member => outside other (List.mem_cons_of_mem _ member))
          rest others)

theorem any_union (roles : List Nat) :
    roles.any (first.union second) = (roles.any first || roles.any second) := by
  induction roles with
  | nil => rfl
  | cons role rest ih =>
      show ((first role || second role) || rest.any (first.union second)) =
        ((first role || rest.any first) || (second role || rest.any second))
      rw [ih]
      cases first role <;> cases second role <;> cases rest.any first <;>
        cases rest.any second <;> rfl

theorem absent_of_any {side : Side} {roles : List Nat} (none : roles.any side = false) :
    ∀ role ∈ roles, side role = false := by
  intro role member
  simp only [List.any_eq_false] at none
  simpa using none role member

/-- The copies of a coin held in a part are the part's shares of the copies held in the
union. -/
theorem heldCopies_left (type : Ty) (reply : model.Value type) :
    ∀ (roles : List Nat),
      leftValues model first second (heldCopies model (first.union second) type reply roles) =
        heldCopies model first type reply roles
  | [] => rfl
  | role :: rest => by
      have head := Held.left_of (X := model.Value type) (first role) (second role) reply
      have tail := heldCopies_left type reply rest
      exact congr (congrArg (Values.cons (Value := SideValue model first) (ty := ⟨type, role⟩)) head)
        tail

theorem heldCopies_right (type : Ty) (reply : model.Value type) :
    ∀ (roles : List Nat),
      rightValues model first second (heldCopies model (first.union second) type reply roles) =
        heldCopies model second type reply roles
  | [] => rfl
  | role :: rest => by
      have head := Held.right_of (X := model.Value type) (first role) (second role) reply
      have tail := heldCopies_right type reply rest
      exact congr (congrArg (Values.cons (Value := SideValue model second) (ty := ⟨type, role⟩)) head)
        tail

end Sides

end Zkc.Core

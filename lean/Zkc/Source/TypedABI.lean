module

public import Zkc.Source.Component

@[expose] public section

/-! A typed product view of an ordered ABI. Products are presentation data;
the heterogeneous values and their source positions remain authoritative. -/
set_option autoImplicit false
namespace Zkc.Source.TypedABI
variable {Ty : Type} {Value : Ty → Type}

@[simp] theorem get_cons_here {types : List Ty} {ty : Ty} (value : Value ty)
    (rest : Values Value types) : (Values.cons value rest).get .here = value := rfl

@[simp] theorem get_cons_there {types : List Ty} {ty head : Ty} (value : Value head)
    (rest : Values Value types) (ref : Var types ty) :
    (Values.cons value rest).get (.there ref) = rest.get ref := rfl

/-- Curried functions over an ordered typed row. Repeated carrier types retain
row order; semantic correspondence is still a separate checked obligation. -/
@[implicit_reducible] def Curried (Value : Ty → Type) (Result : Type) : List Ty → Type
  | [] => Result
  | ty :: types => Value ty → Curried Value Result types

def apply {Result : Type} : {types : List Ty} →
    Curried Value Result types → Values Value types → Result
  | [], result, .nil => result
  | _ :: _, function, .cons value rest => apply (function value) rest

def Fields (Value : Ty → Type) : List Ty → Type
  | [] => Unit
  | ty :: types => Value ty × Fields Value types

def pack : {types : List Ty} → Fields Value types → Values Value types
  | [], _ => .nil
  | _ :: _, (value, rest) => .cons value (pack rest)

def unpack : {types : List Ty} → Values Value types → Fields Value types
  | [], .nil => ()
  | _ :: _, .cons value rest => (value, unpack rest)

@[simp] theorem pack_unpack {types : List Ty} (values : Values Value types) :
    pack (unpack values) = values := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      change Values.cons value (pack (unpack rest)) = Values.cons value rest
      rw [ih]

@[simp] theorem unpack_pack {types : List Ty} (fields : Fields Value types) :
    unpack (pack fields) = fields := by
  induction types with
  | nil => cases fields; rfl
  | cons ty types ih =>
      rcases fields with ⟨value, rest⟩
      change (value, unpack (pack rest)) = (value, rest)
      rw [ih]

theorem pack_surjective {types : List Ty} (values : Values Value types) :
    ∃ fields, values = pack fields := ⟨unpack values, (pack_unpack values).symm⟩

/-- Completeness is required only at the selected coordinates. In particular,
unselected capabilities and private gaps retain arbitrary optional values. -/
def Slot (required : Ty → Bool) (Value : Ty → Type) (ty : Ty) : Type :=
  if required ty then Value ty else Option (Value ty)

def optional (required : Ty → Bool) : {types : List Ty} →
    Values (Slot required Value) types → Values (Component Value) types
  | [], .nil => .nil
  | ty :: _, .cons value rest =>
      .cons (if h : required ty then some (cast (by simp [Slot, h]) value)
        else cast (by simp [Slot, h]) value) (optional required rest)

def complete (required : Ty → Bool) : {types : List Ty} →
    Values (Component Value) types → Option (Values (Slot required Value) types)
  | [], .nil => some .nil
  | ty :: _, .cons value rest => do
      let head ← if h : required ty then value.map (cast (by simp [Slot, h]))
        else some (cast (by simp [Slot, h]) value)
      let tail ← complete required rest
      pure (.cons head tail)

@[simp] theorem complete_optional (required : Ty → Bool) {types : List Ty}
    (values : Values (Slot required Value) types) :
    complete required (optional required values) = some values := by
  induction values with
  | nil => rfl
  | @cons ty types value rest ih =>
      by_cases h : required ty <;> simp [optional, complete, h, ih]

theorem optional_of_complete (required : Ty → Bool) {types : List Ty}
    (values : Values (Component Value) types) (actual : Values (Slot required Value) types)
    (found : complete required values = some actual) : optional required actual = values := by
  induction values with
  | nil => simp only [complete, Option.some.injEq] at found; subst actual; rfl
  | @cons ty types value rest ih =>
      by_cases h : required ty
      · cases value with
        | none => simp [complete, h] at found
        | some value =>
            cases tail : complete required rest with
            | none => simp [complete, h, tail] at found
            | some tailValues =>
                simp [complete, h, tail] at found
                subst actual
                simp [optional, h, ih tailValues tail]
      · cases tail : complete required rest with
        | none => simp [complete, h, tail] at found
        | some tailValues =>
            simp [complete, h, tail] at found
            subst actual
            simp [optional, h, ih tailValues tail]

theorem complete_eq_some_iff (required : Ty → Bool) {types : List Ty}
    (values : Values (Component Value) types) (actual : Values (Slot required Value) types) :
    complete required values = some actual ↔ values = optional required actual := by
  constructor
  · exact fun found => (optional_of_complete required values actual found).symm
  · rintro rfl; exact complete_optional required actual

end Zkc.Source.TypedABI

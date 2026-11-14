module

public import Zkc.Core.Types

public section

/-! The operations the core owns.

The values of `bool`, `nat`, `fin`, sequences, tuples and variants are fixed by the core,
so the operations on them have one meaning, given here, and no model chooses it. An
operation is total, or it has a domain: outside its domain it has no value, and the
process of its application stops `undefined`. The admission checks that every application
of an operation with a domain is justified; the meaning does not read the justification.
-/

set_option autoImplicit false

namespace Zkc.Core

open Zkc.Source

/-- The size of the concatenation of two sequences: known when both sizes are. -/
@[expose, reducible] def concatSize : Option Nat → Option Nat → Option Nat
  | some left, some right => some (left + right)
  | _, _ => none

/-- An operation the core owns. -/
inductive Builtin where
  /-- `a + b`, `a * b`, `a ^ b`, `a == b`, `a < b` on naturals. -/
  | natAdd | natMul | natPow | natEqual | natLess
  /-- `a - b`, on `b ≤ a`. -/
  | natSub
  /-- `a / b` rounded down and `a % b`, on `1 ≤ b`. -/
  | natDiv | natRem
  | boolAnd | boolOr | boolNot | boolEqual
  /-- The number of elements. -/
  | seqLength (element : Ty) (size : Option Nat)
  /-- The element at a position, on `position < length`. -/
  | seqAt (element : Ty) (size : Option Nat)
  /-- The elements from `first` up to `last`, on `first ≤ last ≤ length`; when the result
  is sized, also on `last - first` being that size. -/
  | seqSlice (element : Ty) (size result : Option Nat)
  /-- The elements of the first sequence, then those of the second. -/
  | seqConcat (element : Ty) (left right : Option Nat)
  /-- `count` copies of one value. -/
  | seqFill (element : Ty) (count : Nat)
  /-- The given elements, in order. -/
  | seqMake (element : Ty) (count : Nat)
  /-- A sequence at a size, on its length being that size. -/
  | seqSized (element : Ty) (size : Nat)
  /-- A sized sequence without its size. -/
  | seqUnsized (element : Ty) (size : Nat)
  /-- A natural below a bound, on its being below. -/
  | natBelow (bound : Nat)
  /-- A natural below a bound as a natural. -/
  | finToNat (bound : Nat)
  /-- A natural below a bound, below a larger one. -/
  | finWiden (bound wider : Nat) (fits : Nat.ble bound wider = true)
  /-- The tuple of the given components. -/
  | tupleMake (components : List Ty)
  /-- One component of a tuple. -/
  | tupleGet (components : List Ty) (type : Ty) (position : Var components type)
  /-- The record of a declaration from its fields. -/
  | recordMake (declaration : Nat) (use : Use) (fields : List Ty)
  /-- One field of a record. -/
  | recordGet (declaration : Nat) (use : Use) (fields : List Ty) (type : Ty)
      (position : Var fields type)
  /-- A payload as one alternative of a variant. -/
  | variantMake (declaration : Nat) (alternatives : List Ty) (payload : Ty)
      (position : Var alternatives payload)

namespace Builtin

@[expose, reducible] def arguments : Builtin → List Ty
  | .natAdd | .natMul | .natPow | .natEqual | .natLess | .natSub | .natDiv | .natRem =>
      [.nat, .nat]
  | .boolAnd | .boolOr | .boolEqual => [.bool, .bool]
  | .boolNot => [.bool]
  | .seqLength element size => [.seq element size]
  | .seqAt element size => [.seq element size, .nat]
  | .seqSlice element size _ => [.seq element size, .nat, .nat]
  | .seqConcat element left right => [.seq element left, .seq element right]
  | .seqFill element _ => [element]
  | .seqMake element count => List.replicate count element
  | .seqSized element _ => [.seq element none]
  | .seqUnsized element size => [.seq element (some size)]
  | .natBelow _ => [.nat]
  | .finToNat bound => [.fin bound]
  | .finWiden bound _ _ => [.fin bound]
  | .tupleMake components => components
  | .tupleGet components _ _ => [.tuple components]
  | .recordMake _ _ fields => fields
  | .recordGet declaration use fields _ _ => [.record declaration use fields]
  | .variantMake _ _ payload _ => [payload]

@[expose, reducible] def results : Builtin → List Ty
  | .natAdd | .natMul | .natPow | .natSub | .natDiv | .natRem => [.nat]
  | .natEqual | .natLess => [.bool]
  | .boolAnd | .boolOr | .boolEqual | .boolNot => [.bool]
  | .seqLength _ _ => [.nat]
  | .seqAt element _ => [element]
  | .seqSlice element _ result => [.seq element result]
  | .seqConcat element left right => [.seq element (concatSize left right)]
  | .seqFill element count => [.seq element (some count)]
  | .seqMake element count => [.seq element (some count)]
  | .seqSized element size => [.seq element (some size)]
  | .seqUnsized element _ => [.seq element none]
  | .natBelow bound => [.fin bound]
  | .finToNat _ => [.nat]
  | .finWiden _ wider _ => [.fin wider]
  | .tupleMake components => [.tuple components]
  | .tupleGet _ type _ => [type]
  | .recordMake declaration use fields => [.record declaration use fields]
  | .recordGet _ _ _ type _ => [type]
  | .variantMake declaration alternatives _ _ => [.variant declaration alternatives]

/-- The operation has a domain: an application of it needs a justification. -/
@[expose] def restricted : Builtin → Bool
  | .natSub | .natDiv | .natRem | .seqAt .. | .seqSlice .. | .seqSized .. | .natBelow _ => true
  | _ => false

end Builtin

section Values

variable {Carrier : Nat → Type}

/-- The elements of a sequence, whatever its size. -/
@[expose] def Ty.elements {element : Ty} :
    (size : Option Nat) → Ty.Value Carrier (.seq element size) → List (Ty.Value Carrier element)
  | none, values => values
  | some _, values => values.val

/-- A list as a sequence of a size: any list as an unsized one, a list of that length as
a sized one. -/
@[expose] def Ty.sequence {element : Ty} :
    (size : Option Nat) → List (Ty.Value Carrier element) →
      Option (Ty.Value Carrier (.seq element size))
  | none, values => some values
  | some size, values =>
      if same : values.length = size then some ⟨values, same⟩ else none

/-- The concatenation of two sequences, at the size of the concatenation. -/
@[expose] def Ty.concat {element : Ty} :
    (left right : Option Nat) → Ty.Value Carrier (.seq element left) →
      Ty.Value Carrier (.seq element right) →
        Ty.Value Carrier (.seq element (concatSize left right))
  | some _, some _, first, second =>
      ⟨first.val ++ second.val, by rw [List.length_append, first.property, second.property]⟩
  | some _, none, first, second => first.val ++ second
  | none, some _, first, second => first ++ second.val
  | none, none, first, second => first ++ second

/-- Values of one type as a list. -/
@[expose] def Ty.collect {element : Ty} :
    (count : Nat) → Values (Ty.Value Carrier) (List.replicate count element) →
      { values : List (Ty.Value Carrier element) // values.length = count }
  | 0, _ => ⟨[], rfl⟩
  | count + 1, .cons value rest =>
      ⟨value :: (Ty.collect count rest).val,
        congrArg (· + 1) (Ty.collect count rest).property⟩

/-- Values as a tuple. -/
@[expose] def Ty.pack :
    (components : List Ty) → Values (Ty.Value Carrier) components → Ty.Tuple Carrier components
  | [], _ => PUnit.unit
  | _ :: rest, .cons value values => (value, Ty.pack rest values)

/-- One component of a tuple. -/
@[expose] def Ty.component :
    (components : List Ty) → Ty.Tuple Carrier components → {type : Ty} →
      Var components type → Ty.Value Carrier type
  | [], _, _, position => position.elimNil
  | _ :: rest, values, _, position =>
      Var.cases (motive := fun type _ => Ty.Value Carrier type) values.1
        (fun position => Ty.component rest values.2 position) position

/-- A payload as the alternative at a position. -/
@[expose] def Ty.alternative :
    (alternatives : List Ty) → {payload : Ty} → Var alternatives payload →
      Ty.Value Carrier payload → Ty.Variant Carrier alternatives
  | [], _, position, _ => position.elimNil
  | _ :: rest, _, position, value =>
      Var.cases (motive := fun payload _ => Ty.Value Carrier payload → Ty.Variant Carrier (_ :: rest))
        (fun value => .inl value)
        (fun position value => .inr (Ty.alternative rest position value)) position value

/-- The value of an operation the core owns: its results, or none outside its domain. -/
@[expose] def Builtin.eval :
    (operation : Builtin) → Values (Ty.Value Carrier) operation.arguments →
      Option (Values (Ty.Value Carrier) operation.results)
  | .natAdd, .cons a (.cons b .nil) => some (.cons (a + b : Nat) .nil)
  | .natMul, .cons a (.cons b .nil) => some (.cons (a * b : Nat) .nil)
  | .natPow, .cons a (.cons b .nil) => some (.cons (a ^ b : Nat) .nil)
  | .natEqual, .cons a (.cons b .nil) => some (.cons (Nat.beq a b) .nil)
  | .natLess, .cons a (.cons b .nil) => some (.cons (Nat.blt a b) .nil)
  | .natSub, .cons a (.cons b .nil) =>
      if Nat.ble b a then some (.cons (a - b : Nat) .nil) else none
  | .natDiv, .cons a (.cons b .nil) =>
      if Nat.ble 1 b then some (.cons (a / b : Nat) .nil) else none
  | .natRem, .cons a (.cons b .nil) =>
      if Nat.ble 1 b then some (.cons (a % b : Nat) .nil) else none
  | .boolAnd, .cons a (.cons b .nil) => some (.cons (a && b) .nil)
  | .boolOr, .cons a (.cons b .nil) => some (.cons (a || b) .nil)
  | .boolEqual, .cons a (.cons b .nil) => some (.cons (a == b) .nil)
  | .boolNot, .cons a .nil => some (.cons (!a) .nil)
  | .seqLength _ size, .cons values .nil => some (.cons (Ty.elements size values).length .nil)
  | .seqAt _ size, .cons values (.cons position .nil) =>
      ((Ty.elements size values)[position]?).map fun value => .cons value .nil
  | .seqSlice _ size result, .cons values (.cons first (.cons last .nil)) =>
      if Nat.ble first last && Nat.ble last (Ty.elements size values).length then
        (Ty.sequence result (((Ty.elements size values).drop first).take (last - first))).map
          fun slice => .cons slice .nil
      else none
  | .seqConcat _ left right, .cons first (.cons second .nil) =>
      some (.cons (Ty.concat left right first second) .nil)
  | .seqFill _ count, .cons value .nil =>
      some (.cons ⟨List.replicate count value, List.length_replicate⟩ .nil)
  | .seqMake _ count, values => some (.cons (Ty.collect count values) .nil)
  | .seqSized _ size, .cons values .nil =>
      (Ty.sequence (some size) values).map fun sized => .cons sized .nil
  | .seqUnsized _ _, .cons values .nil => some (.cons values.val .nil)
  | .natBelow bound, .cons value .nil =>
      if below : value < bound then some (.cons (⟨value, below⟩ : Fin bound) .nil) else none
  | .finToNat _, .cons value .nil => some (.cons value.val .nil)
  | .finWiden _ _ fits, .cons value .nil =>
      some (.cons ⟨value.val, Nat.lt_of_lt_of_le value.isLt (Nat.le_of_ble_eq_true fits)⟩ .nil)
  | .tupleMake components, values => some (.cons (Ty.pack components values) .nil)
  | .tupleGet components _ position, .cons values .nil =>
      some (.cons (Ty.component components values position) .nil)
  | .recordMake _ _ fields, values => some (.cons (Ty.pack fields values) .nil)
  | .recordGet _ _ fields _ position, .cons values .nil =>
      some (.cons (Ty.component fields values position) .nil)
  | .variantMake _ alternatives _ position, .cons value .nil =>
      some (.cons (Ty.alternative alternatives position value) .nil)

/-- An operation without a domain has a value on every input. -/
theorem Builtin.eval_isSome (operation : Builtin) (total : operation.restricted = false)
    (arguments : Values (Ty.Value Carrier) operation.arguments) :
    (operation.eval arguments).isSome = true := by
  cases operation <;> first
    | exact Bool.noConfusion total
    | rfl
    | (cases arguments with | cons a rest => cases rest with
        | nil => rfl)
    | (cases arguments with | cons a rest => cases rest with
        | cons b rest => cases rest with
          | nil => rfl)

end Values

end Zkc.Core

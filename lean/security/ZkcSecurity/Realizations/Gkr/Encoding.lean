module

public import ZkcSecurity.Families.Gkr.Circuit
public import Zkc.Polynomial.Multilinear.ListRestriction
public import Zkc.Source.Structured.Vocabulary

@[expose] public section

/-! A fixed mathematical reading of the public GKR circuit encoding. Shape is
independent of the output claim. The zero extension of an unused wiring block
is a definition of the reference, never evidence for a malformed input. Every
used block has an exact, non-padding decode under `Shape`.
-/

set_option autoImplicit false

namespace ZkcSecurity.Realizations.Gkr
open Zkc.Polynomial.Multilinear ZkcSecurity.Families.Gkr

structure CircuitEncoding (F : Type) where
  inputs : List F
  add : List F
  mul : List F
  layers : Nat
  selector : Nat
  width : Nat

namespace CircuitEncoding
variable {F : Type} [CommRing F]

def block (values : List F) (position size : Nat) : List F :=
  (values.drop (position * size)).take size

def Shape (encoding : CircuitEncoding F) : Prop :=
  encoding.inputs.length = 2 ^ encoding.width ∧
  encoding.add.length = 2 ^ encoding.selector * 2 ^ (encoding.width + encoding.width + encoding.width) ∧
  encoding.mul.length = 2 ^ encoding.selector * 2 ^ (encoding.width + encoding.width + encoding.width) ∧
  encoding.layers ≤ 2 ^ encoding.selector

/-- The runtime admits these bounds before entering any challenge or layer.
They are part of the honest input policy, independently of target truth. -/
def Admitted (maximumLayers maximumWidth : Nat) (encoding : CircuitEncoding F)
    (outputs : List F) : Prop :=
  encoding.Shape ∧ outputs.length = 2 ^ encoding.width ∧
  encoding.width ≤ maximumWidth ∧ encoding.layers ≤ maximumLayers ∧
  encoding.selector + encoding.width + encoding.width + encoding.width < 64

def circuit (encoding : CircuitEncoding F) : Circuit F encoding.width where
  inputs := (ofList? encoding.width encoding.inputs).getD 0
  add layer := (ofList? (encoding.width + encoding.width + encoding.width)
    (block encoding.add layer (2 ^ (encoding.width + encoding.width + encoding.width)))).getD 0
  mul layer := (ofList? (encoding.width + encoding.width + encoding.width)
    (block encoding.mul layer (2 ^ (encoding.width + encoding.width + encoding.width)))).getD 0

/-- A malformed circuit has no true target. A valid target compares against
independent mathematical circuit evaluation, not a run of the producer. -/
def Outputs (encoding : CircuitEncoding F) (outputs : List F) : Prop :=
  encoding.Shape ∧ ofList? encoding.width outputs = some (encoding.circuit.wires encoding.layers 0)

theorem decode_getD {n : Nat} (values : List F) (shape : values.length = 2 ^ n) :
    ofList? n values = some ((ofList? n values).getD 0) := by
  have present := (ofList?_isSome_iff (n := n) values).mpr shape
  cases selected : ofList? n values with
  | none => simp [selected] at present
  | some table => rfl

omit [CommRing F] in
theorem block_length (values : List F) (position size : Nat)
    (inside : (position + 1) * size ≤ values.length) :
    (block values position size).length = size := by
  simp only [block, List.length_take, List.length_drop]
  rw [Nat.min_eq_left]
  simp only [Nat.add_mul, Nat.one_mul] at inside
  omega

theorem inputs_decode (encoding : CircuitEncoding F) (shape : encoding.Shape) :
    ofList? encoding.width encoding.inputs = some encoding.circuit.inputs :=
  decode_getD encoding.inputs shape.1

theorem add_decode (encoding : CircuitEncoding F) (shape : encoding.Shape)
    (layer : Nat) (inside : layer < encoding.layers) :
    ofList? (encoding.width + encoding.width + encoding.width)
      (block encoding.add layer (2 ^ (encoding.width + encoding.width + encoding.width))) =
        some (encoding.circuit.add layer) := by
  apply decode_getD
  apply block_length
  rw [shape.2.1]
  exact Nat.mul_le_mul_right _ ((Nat.succ_le_of_lt inside).trans shape.2.2.2)

theorem mul_decode (encoding : CircuitEncoding F) (shape : encoding.Shape)
    (layer : Nat) (inside : layer < encoding.layers) :
    ofList? (encoding.width + encoding.width + encoding.width)
      (block encoding.mul layer (2 ^ (encoding.width + encoding.width + encoding.width))) =
        some (encoding.circuit.mul layer) := by
  apply decode_getD
  apply block_length
  rw [shape.2.2.1]
  exact Nat.mul_le_mul_right _ ((Nat.succ_le_of_lt inside).trans shape.2.2.2)

theorem outputs_shape (encoding : CircuitEncoding F) (outputs : List F)
    (correct : encoding.Outputs outputs) : outputs.length = 2 ^ encoding.width :=
  ofList?_length outputs _ correct.2

theorem invalid_shape (encoding : CircuitEncoding F) (outputs : List F)
    (invalid : ¬ encoding.Shape) : ¬ encoding.Outputs outputs :=
  fun correct => invalid correct.1

omit [CommRing F] in
theorem outputs_unique (encoding : CircuitEncoding F) (first second : Table F encoding.width)
    (outputs : List F) (left : ofList? encoding.width outputs = some first)
    (right : ofList? encoding.width outputs = some second) : first = second :=
  Option.some.inj (left.symm.trans right)

end CircuitEncoding
end ZkcSecurity.Realizations.Gkr

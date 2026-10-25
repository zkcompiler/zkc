import ZkcSecurity.Claims.HonestInput
import Mathlib.Tactic.NormNum

/-! Typed shape/bound controls on source-ABI values. No root producer proof or
discovery candidate is instantiated. -/
set_option autoImplicit false
namespace TestsSecurity.HonestInput
open Zkc.Source Zkc.Source.Structured ZkcSecurity.Claims.HonestPair

def carriers : Carriers := uniformCarriers Unit Unit
abbrev Types := [Ty.vector "field", Ty.index]

def tablePolicy : InputPolicy Types :=
  ⟨[.boundedIndex (.there .here) 2, .cubeTable .here (.there .here) 1]⟩

def inputs (table : List Unit) (rounds : Nat) : Values (Component carriers.Value) Types :=
  .cons (some table) (.cons (some rounds) .nil)

theorem positive : tablePolicy.Holds (inputs [(), (), (), ()] 2) := by
  norm_num [tablePolicy, InputPolicy.Holds, InputRule.Holds, inputs, Values.get, indexLimit]
  exact ⟨_, rfl, by decide +kernel, rfl⟩

theorem wrong_shape : ¬ tablePolicy.Holds (inputs [()] 2) := by
  norm_num [tablePolicy, InputPolicy.Holds, InputRule.Holds, inputs, Values.get, indexLimit]
  intro table same _ length
  cases Option.some.inj same
  cases length

theorem above_maximum : ¬ tablePolicy.Holds (inputs (List.replicate 8 ()) 3) := by
  norm_num [tablePolicy, InputPolicy.Holds, InputRule.Holds, inputs, Values.get, indexLimit]

theorem illegal_index : ¬ tablePolicy.Holds (inputs [] indexLimit) := by
  simp [tablePolicy, InputPolicy.Holds, InputRule.Holds, inputs, Values.get]

theorem absent_rounds : ¬ tablePolicy.Holds
    (.cons (some [(), (), (), ()]) (.cons none .nil) : Values (Component carriers.Value) Types) := by
  simp [tablePolicy, InputPolicy.Holds, InputRule.Holds, Values.get]

theorem zero_width : ¬ (InputPolicy.mk [.cubeTable .here (.there .here) 0]).Holds
    (inputs [] 0) := by
  simp [InputPolicy.Holds, InputRule.Holds, inputs, Values.get]

-- A narrower bound is explicit claim data, and changes the admitted domain.
theorem changed_contract : ¬ (InputPolicy.mk [.boundedIndex (.there .here) 1]).Holds
    (inputs [(), (), (), ()] 2) := by
  norm_num [InputPolicy.Holds, InputRule.Holds, inputs, Values.get]

example : tablePolicy.checkParameters tablePolicy.parameters = .ok () :=
  tablePolicy.parameters_checked

example : tablePolicy.checkParameters none =
    .error (.schema "honest input policy does not match the typed request") := by rfl

def smallerMaximum : InputPolicy Types :=
  ⟨[.boundedIndex (.there .here) 1, .cubeTable .here (.there .here) 1]⟩

example : tablePolicy.checkParameters smallerMaximum.parameters =
    .error (.schema "honest input policy does not match the typed request") := by rfl

def swappedSelectors : Zkc.Claims.Wire.Expr := .application "honest.input_policy" (some 0)
  [(some "rules", .list
    [(.boundedIndex (.there .here) 2 : InputRule Types).wire,
     .application "honest.cube_table" (some 0)
       [(some "domain", .reference "field"), (some "table", .natural 1),
        (some "rounds", .natural 0), (some "width", .natural 1)]])]

example : tablePolicy.checkParameters (some swappedSelectors) =
    .error (.schema "honest input policy does not match the typed request") := by rfl

example : tablePolicy.checkParameters (some (.application "honest.input_policy" (some 1) [])) =
    .error (.schema "honest input policy does not match the typed request") := by rfl

example : tablePolicy.checkParameters (some (.application "honest.input_policy" (some 0)
    [(some "rules", .list ((tablePolicy.rules ++ tablePolicy.rules).map InputRule.wire))])) =
    .error (.schema "honest input policy does not match the typed request") := by rfl

example : (InputPolicy.mk ([] : List (InputRule Types))).checkParameters none = .ok () := by rfl

#print axioms positive
#print axioms wrong_shape
#print axioms above_maximum
#print axioms illegal_index
#print axioms ZkcSecurity.Claims.HonestPair.InputRule.wire_eq_of_accepted
#print axioms ZkcSecurity.Claims.HonestPair.InputPolicy.parameters_eq_of_checked
end TestsSecurity.HonestInput

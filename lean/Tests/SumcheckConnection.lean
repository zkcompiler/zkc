import Zkc.Protocols.Sumcheck.Connection
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false

namespace Tests.SumcheckConnection

open PIR Zkc.Polynomial Zkc.Protocols.Sumcheck

abbrev Field := ZMod 7

def variableY : Quadratic Field 2 :=
  .node (.node (.constant 0) (.constant 1) (.constant 0))
    (.node (.constant 0) (.constant 0) (.constant 0))
    (.node (.constant 0) (.constant 0) (.constant 0))

def input := Acceptance.honestInput variableY (2, 3, ())
def actual : Connection.Residual Field 2 := ⟨![2, 3], 3⟩
def swapped : Connection.Residual Field 2 := ⟨![3, 2], 3⟩

theorem actual_connected :
    Connection.roundConstraints Security.honestSend Security.honestReact input actual () ∧
    Connection.evaluates input actual := by
  constructor
  · constructor
    · funext i; fin_cases i <;> rfl
    · decide +kernel
  · unfold Connection.evaluates
    decide +kernel

/-- The changed point is neither produced nor accepted with the retained value. -/
theorem swapped_point_rejected :
    ¬ Connection.produces Security.honestSend Security.honestReact input swapped ∧
    Connection.evaluate input swapped = false := by
  constructor
  · intro h
    have wrong : (3 : Field) = 2 := congrFun h.1 (0 : Fin 2)
    revert wrong
    decide +kernel
  · decide +kernel

theorem wrong_object_rejected :
    Connection.evaluate { input with polynomial := (.node
      (.node (.constant 0) (.constant 0) (.constant 0))
      (.node (.constant 1) (.constant 0) (.constant 0))
      (.node (.constant 0) (.constant 0) (.constant 0))) } actual = false := by decide +kernel

/-- The common connection needs no odd-characteristic restriction. This is
perfect completeness over F2, not a useful numerical soundness bound. -/
theorem characteristic_two {n : Nat} (p : Quadratic (ZMod 2) n)
    (coins : Zkc.Probability.AdaptiveTape.Tape (ZMod 2) n) :
    Relation.Connected
      (Connection.produces Security.honestSend Security.honestReact (Acceptance.honestInput p coins))
      Eq (Connection.evaluates (Acceptance.honestInput p coins)) :=
  Connection.honest_connected p coins

end Tests.SumcheckConnection

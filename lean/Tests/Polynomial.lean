import Zkc.Compiler.Analysis.FactorReuse
import Zkc.Modules.PolynomialPreparation
import Mathlib.Data.ZMod.Basic

/-! Nonzero squared terms and a two-coordinate materialization prefix. -/

set_option autoImplicit false

open Zkc.Compiler.FactorReuse

namespace Tests.Polynomial

open Zkc.Polynomial Zkc.Modules.PolynomialPreparation
open Zkc.Modules.Factor Zkc.Modules.FactorState

abbrev F := ZMod 17

def lastVariable : Quadratic F 1 := .node (.constant 3) (.constant 1) (.constant 1)
def zeroVariable : Quadratic F 1 := .node (.constant 0) (.constant 0) (.constant 0)
def middleVariables : Quadratic F 2 :=
  .node (Quadratic.scale 2 lastVariable) zeroVariable lastVariable

/-- (1+x+x²)(2+y²)(3+z+z²), with the displayed coordinate order. -/
def polynomial : Quadratic F 3 := .node middleVariables middleVariables middleVariables

def binding : Binding F 3 := ⟨⟨200, [10, 20, 30]⟩, rfl, by decide, polynomial⟩
def request : Request 2 := ⟨9, [0, 1], rfl⟩
def world : World F := bind binding
  ⟨⟨fun _ _ => 0, fun _ _ => 0, fun i => if i = 0 then 2 else if i = 1 then 3 else 4⟩,
    [0, 1, 2]⟩

example : Quadratic.recompute (n := 1) 2 polynomial (coordinates 2 [2, 3])
    (coordinates 1 [4]) = 3 := by decide
example : (polynomial.materialize (n := 1) 2 (coordinates 2 [2, 3])).eval
    (coordinates 1 [4]) = 3 := by decide
example : (polynomial.materialize (n := 1) 2 (coordinates 2 [2, 3])).eval
    (coordinates 1 [5]) = 8 := by decide

example : (polynomial.materialize (n := 1) 2 (coordinates 2 [3, 2])).eval
    (coordinates 1 [4]) = 9 := by decide

/-- The actual installed view, produced before selecting the later query. -/
example : (execute (n := 1) binding (.prepare request) world).world.values.view 9 [4] = 3 := by
  decide
example : (execute (n := 1) binding (.prepare request) world).world.values.view 9 [5] = 8 := by
  decide

example : Means (install binding request world).values (fact binding request) :=
  install_means binding request world (bind_bound binding _)

example : runPlan (install binding request world).values ⟨binding.key, [0, 1, 2]⟩
    (infer [fact binding request] [0, 1, 2] ⟨binding.key, [0, 1, 2]⟩) = 3 := by decide

/-- Omitting the residual squared term produces a different result. -/
example : (10 : F) + 9 * 4 = 12 ∧ (12 : F) ≠ 3 := by decide

end Tests.Polynomial

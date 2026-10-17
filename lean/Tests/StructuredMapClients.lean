import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Module.Basic
import ZkcExamples.Structured.MapCombination
import ZkcExamples.Structured.MapConstant

namespace Tests.StructuredMapClients

open Zkc.Source Zkc.Source.Structured
open ZkcExamples.Structured
set_option smartUnfolding false

-- The exact two-role source keeps interleaved scalar broadcasts asymmetric.
example : MapCombinationViews.program.participant Int Int 0
    (MapCombination.inputs 2 [3, 5] 7 [11, 13] [17, 19] 23).present =
    .done (.cons (some [-68, -78]) .nil) := by
  rw [MapCombination.owner_equation (G := Int) 2 [3, 5] 7 [11, 13] [17, 19] 23 (by decide +kernel) rfl rfl]
  rfl

example : MapCombinationViews.program.participant Int Int 0
    (MapCombination.inputs 7 [3, 5] 2 [11, 13] [17, 19] 23).present =
    .done (.cons (some [2, 12]) .nil) := by
  rw [MapCombination.owner_equation (G := Int) 7 [3, 5] 2 [11, 13] [17, 19] 23 (by decide +kernel) rfl rfl]
  rfl

-- The formula ignores this row's values, but its shape still precedes execution.
example : MapCombinationViews.program.participant Int Int 0
    (MapCombination.inputs 2 [] 3 [] [99] 0).present = .halt .refused :=
  MapCombination.owner_shape_failure _ _ _ _ _ _ _ (by decide +kernel)

example : MapCombinationViews.program.participant Int Int 0
    (MapCombination.inputs 2 [] 3 [] [] 0).present = .done (.cons (some []) .nil) := by
  rw [MapCombination.owner_equation _ _ _ _ _ _ (by decide +kernel) rfl rfl]
  rfl

example : MapCombinationViews.program.participant Int Int 1
    (.cons none (.cons none (.cons none (.cons none (.cons none (.cons none .nil)))))) =
    .done (.cons none .nil) := MapCombination.nonowner_equation

example : MapCombinationViews.program.participant Int Int 0
    (.cons (some 2) (.cons (some []) (.cons (some 3)
      (.cons (some []) (.cons (some []) (.cons none .nil)))))) = .halt .incomplete :=
  MapCombination.missing_unused_scalar [] []

-- An input-independent helper still produces exactly one result per valid row.
example : MapConstantViews.program.participant Int Int 0
    (MapConstant.inputs [1, 2, 3] [10, 20, 30] 41).present =
    .done (.cons (some [7, 7, 7]) .nil) := by
  rw [MapConstant.owner_equation (G := Int) [1, 2, 3] [10, 20, 30] 41 (by decide +kernel) rfl]
  rfl

example : MapConstantViews.program.participant Int Int 0
    (MapConstant.inputs [] [] 41).present = .done (.cons (some []) .nil) := by
  rw [MapConstant.owner_equation _ _ _ (by decide +kernel) rfl]
  rfl

example : MapConstantViews.program.participant Int Int 0
    (MapConstant.inputs [] [10] 41).present = .halt .refused :=
  MapConstant.owner_shape_failure _ _ _ _ (by decide +kernel)

example : MapConstantViews.program.participant Int Int 0
    (.cons (some []) (.cons (some []) (.cons none .nil))) = .halt .incomplete :=
  MapConstant.missing_unused_scalar [] []

example : MapConstantViews.program.participant Int Int 1
    (.cons none (.cons none (.cons none .nil))) = .done (.cons none .nil) :=
  MapConstant.nonowner_equation

end Tests.StructuredMapClients

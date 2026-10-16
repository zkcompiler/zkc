module

public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Module.Basic
public import ZkcExamples.Structured.MapFirst
public import ZkcExamples.Structured.MapPrefix

@[expose] public section

namespace Tests.StructuredMapRestrictions

open Zkc.Source Zkc.Source.Structured
open ZkcExamples.Structured PrimitiveLibrary MapFirstLaws MapPrefixLaws
set_option smartUnfolding false

-- Complete retained First process, interpreted over a commutative ring.
theorem first_contiguous_halves : MapFirstViews.program.denote Int Int (firstInputs [0, 10, 20, 30] 2 1 2) =
    .done (inputs [40, 50] 1 1) := by
  rw [MapFirst.process_equation _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  rfl

-- The returned triple retains two independent columns in row-major order.
theorem first_two_columns : MapFirstViews.program.denote Int Int (firstInputs [1, 2, 10, 20] 1 2 2) =
    .done (inputs [19, 38] 0 2) := by
  rw [MapFirst.process_equation _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  rfl

theorem first_zero_dimension_rejects : MapFirstViews.program.denote Int Int (firstInputs [7] 0 1 2) = .halt .reject := by
  rw [MapFirst.process_equation _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  rfl

theorem first_zero_columns_rejects : MapFirstViews.program.denote Int Int (firstInputs [7] 0 0 2) = .halt .reject := by
  rw [MapFirst.process_equation _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  rfl

theorem first_invalid_shape_rejects : MapFirstViews.program.denote Int Int (firstInputs [7, 8, 9] 1 1 2) = .halt .reject := by
  rw [MapFirst.process_equation _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  rfl

-- Empty point does not reach First's positive-dimension guard.
theorem prefix_empty_zero_dimension : MapPrefixViews.program.denote Int Int (prefixInputs [7] 0 1 []) =
    .done (inputs [7] 0 1) := by
  exact MapPrefix.process_empty _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)

-- Ordered composition differs if coordinates are swapped.
theorem prefix_ordered_coordinates : MapPrefixViews.program.denote Int Int (prefixInputs [0, 1, 2, 4] 2 1 [2, 3]) =
    .done (inputs [13] 0 1) := by
  rw [MapPrefix.process_equation _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  rfl

theorem prefix_swapped_coordinates : MapPrefixViews.program.denote Int Int (prefixInputs [0, 1, 2, 4] 2 1 [3, 2]) =
    .done (inputs [14] 0 1) := by
  rw [MapPrefix.process_equation _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  rfl

theorem prefix_too_long_rejects : MapPrefixViews.program.denote Int Int (prefixInputs [0, 1, 2, 4] 2 1 [2, 3, 4]) =
    .halt .reject := by
  exact MapPrefix.process_too_long _ _ _ _ (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

-- Prefix validates the original table even when the point is empty.
theorem prefix_empty_invalid_table_rejects : MapPrefixViews.program.denote Int Int (prefixInputs [7] 0 0 []) = .halt .reject := by
  rw [MapPrefix.process_equation _ _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  rfl

end Tests.StructuredMapRestrictions

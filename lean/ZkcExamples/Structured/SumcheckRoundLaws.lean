module

public import ZkcExamples.Structured.SumcheckVerifierHelpers
public import ZkcExamples.Structured.SumcheckUnitContracts

@[expose] public section

/-! Laws of the round's Local helpers in a complete unit's plain participant
tables: the half sums and the first-coordinate fold of a shaped table. They are
the helper laws the generated prover normal form of the round callback cites;
`SumcheckVerifierHelpers.append_plain` supplies the append. -/
namespace ZkcExamples.Structured.SumcheckProverLaws
open Zkc.Source Zkc.Source.Structured PrimitiveLibrary
open SumcheckVerifierHelpers
open Zkc.Polynomial.Multilinear (restrictValues)

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

section Helpers
variable (U : UnitPayload) (bodies : SumcheckUnitContracts.Bodies U.definitions)
include bodies

/-- The actual sums helper on a shaped positive-dimensional table. -/
theorem sums_present (xs : List F) (dimension width : Nat)
    (shape : HasShape xs dimension width) (positive : 0 < dimension) :
    invoke (plainHelpers (F := F) (G := G) U).closed SumcheckHelperBodies.sumsHelper
      (inputs xs dimension width) =
      .done (SumcheckHelperLaws.messageResult (xs.take (xs.length / 2)).sum
        (xs.drop (xs.length / 2)).sum) := by
  rw [closed_invoke_plain, SumcheckUnitContracts.sums_all U.linked bodies]
  have dimensionBound : dimension < indexLimit := Nat.lt_trans shape.2.1 (by decide +kernel)
  simp only [dimensionBound, positive, shape.split_valid positive, and_self, ↓reduceIte]
  rfl

/-- The actual sums helper rejects a zero-dimensional table before any send. -/
theorem sums_zero (xs : List F) (width : Nat) :
    invoke (plainHelpers (F := F) (G := G) U).closed SumcheckHelperBodies.sumsHelper
      (inputs xs 0 width) = .halt .reject := by
  rw [closed_invoke_plain, SumcheckUnitContracts.sums_all U.linked bodies]
  simp only [show 0 < indexLimit by decide +kernel, Nat.lt_irrefl, ↓reduceIte]
  rfl

/-- The actual fold helper on a shaped positive-dimensional table. -/
theorem first_present (xs : List F) (dimension width : Nat) (r : F)
    (shape : HasShape xs dimension width) (bound : xs.length < indexLimit)
    (positive : 0 < dimension) :
    invoke (plainHelpers (F := F) (G := G) U).closed MapFirstBodies.firstHelper
      (MapFirstLaws.firstInputs xs dimension width r) =
      .done (inputs (restrictValues xs r) (dimension - 1) width) := by
  rw [closed_invoke_plain,
    (SumcheckUnitContracts.first_laws U.linked bodies).first xs dimension width r shape bound]
  simp only [positive, ↓reduceIte]
  rfl

end Helpers

end ZkcExamples.Structured.SumcheckProverLaws

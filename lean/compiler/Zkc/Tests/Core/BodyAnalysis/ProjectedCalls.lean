import Zkc.Core.Admission.CheckedTables
import Zkc.Tests.Core.Shapes

namespace Zkc.Core.BodyAnalysis.RoleExamples
open Shapes RoleContracts

private def emptyCatalog := (FunctionContracts.check ([] : List (FnHeader plain))).toOption.get (by decide)

/-- A real projected caller loops and invokes a previous protocol. Cover both participants
and every outside role in the same table theorem. -/
private theorem checksRound (r : Role) : ∃ bs, checkRole emptyCatalog r roundHeader
    (inputs := Names.counting 0 _) (project r round) = .ok bs := by
  match r with
  | 0 | 1 | _+2 => exact ⟨[], by rfl'⟩

private theorem checksRounds (r : Role) : ∃ bs, checkRole emptyCatalog r roundsHeader
    (inputs := Names.counting 0 _) (project r rounds) = .ok bs := by
  match r with
  | 0 | 1 | _+2 => exact ⟨[], by rfl'⟩

theorem roundsRoleTable (M : Model plain) : RCallees M (Defs.rTable M roundsProgram) :=
  (checkedTables M roundsProgram (by simp)
    ⟨⟨emptyCatalog, fun r _ => checksRounds r⟩, ⟨emptyCatalog, fun r _ => checksRound r⟩, trivial⟩).2

#print axioms roundsRoleTable
end Zkc.Core.BodyAnalysis.RoleExamples

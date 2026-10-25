import TestsSecurity.GenerateSubjects
import TestsSecurity.GenerateCompletenessClaims
import TestsSecurity.GenerateClaimLibraries

/-! Generator entry points are separate from their audited library modules. -/
def main (args : List String) : IO Unit := do
  match args with
  | "bindings" :: rest => ZkcSecurity.Generation.Roots.generateStage "bindings" rest
  | "subjects" :: rest => TestsSecurity.GenerateSubjects.main rest
  | "completeness" :: rest => TestsSecurity.GenerateCompletenessClaims.main rest
  | "claim-libraries" :: rest => TestsSecurity.GenerateClaimLibraries.main rest
  | _ => throw (IO.userError "expected bindings, subjects, completeness or claim-libraries")

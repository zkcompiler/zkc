module

public import Zkc.Tests.Verification.Construction.ActualCalls
public meta import Zkc.Tools.Program.Companions.Assembly
public meta import Zkc.Tools.Program.Companions.Report

/-! Law coverage and direct proof are distinct. The request is the independently fixed
actual-body theorem type; registry lookup cannot choose a weaker proposition. -/

@[expose] public section
namespace ActualSourceConstruction.LawRequests
open Twice

@[zkc "actual.difference"] theorem registered : DifferenceLaw := difference_law
@[zkc "actual.wrong-law"] theorem wrong : True := True.intro

/-- A direct kernel-checked proof has no registry prerequisite. -/
theorem direct : DifferenceLaw := difference_law

/-- Registered installation checks exactly the same actual-body proposition. -/
theorem selected : DifferenceLaw := zkc_companion ["actual.difference"[]]

open Lean Elab Command Term Meta ZkcTools.Companions in
run_elab do
  let expected ← elabTerm (← `(term| DifferenceLaw)) none
  let absent ← resolve #[⟨"actual.missing-law", #[]⟩] expected
  unless (match absent with | .missing => true | _ => false) do
    throwError "missing actual-source law was not reported"
  let invalid ← assemble #[⟨"actual.wrong-law", #[]⟩] expected
    #[⟨"valid-direct-proof", ← `(term| direct)⟩]
  unless (match invalid with | .refused _ _ => true | _ => false) do
    throwError "a direct proof concealed an invalid explicitly selected law"
  let uncovered ← report
    { identity := "actual.missing-law", responsibility := "required mathematical promise",
      expected := expected } (.openObligation "required law omitted" #[])
  unless (uncovered.getObjValAs? String "status").toOption == some "open" do
    throwError "an unproved required declaration was reported as covered"

#print axioms direct
#print axioms selected
end ActualSourceConstruction.LawRequests

module

public import ZkcSecurity.Examples.TableMembership.Subject
public meta import ZkcSecurity.Examples.TableMembership.Subject
public meta import ZkcSecurity.Generation.SubjectABI.Command
public meta import ZkcSecurity.Generation.OriginalEndpoint

@[expose] public section

/-! Reproducible source-driven ABI entry point. This module imports no solution
and emits kernel-checked structural proofs through the shared generator. -/
namespace ZkcSecurity.Generation.TableMembership
open ZkcSecurity.Generation.SubjectABI
open ZkcSecurity.Examples.TableMembership.Subject
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000

derive_subject_abi abiSource for subject
  module "ZkcSecurity.Examples.TableMembership.ABI"
  from "ZkcSecurity.Examples.TableMembership.Subject"

run_cmd do
  let metadata ← Lean.Elab.Command.liftTermElabM do
    let expression ← Lean.Elab.Term.elabTerm (← `(metadata subject)) none
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let reduced ← Lean.Meta.withTransparency .all <| Lean.Meta.reduce (← Lean.instantiateMVars expression)
    Lean.Meta.evalExpr Metadata (Lean.mkConst ``Metadata) reduced
  let output : ZkcSecurity.Generation.OriginalEndpoint.Output := {
    moduleName := "ZkcSecurity.Examples.TableMembership.Endpoint"
    subjectModule := "ZkcSecurity.Examples.TableMembership.Subject"
    methodModule := "ZkcSecurity.Examples.TableMembership.Method"
    sampling := "ZkcSecurity.Examples.TableMembership.Subject.samples"
    capabilities := "ZkcSecurity.Examples.TableMembership.Subject.capabilities"
    schedule := "ZkcSecurity.Examples.TableMembership.Method.schedule"
    validatorCost := "ZkcSecurity.Examples.TableMembership.Method.validatorCost"
    chargedExport := "ZkcSecurity.Examples.TableMembership.Method.reductionExport"
    scalar := some ⟨"ZkcSecurity.Examples.TableMembership.Method.scalarBound",
      "ZkcSecurity.Examples.TableMembership.Method.scalar_bound"⟩ }
  match ZkcSecurity.Generation.OriginalEndpoint.soundnessSource metadata artifacts.validator output with
  | .error reason => Lean.throwError reason
  | .ok generated => do
      let name := Lean.mkIdent `endpointSource
      let declaration ← `(def $name : String := $(Lean.quote generated))
      Lean.Elab.Command.elabCommand declaration

def main (arguments : List String) : IO Unit := do
  let [directory] := arguments | throw (IO.userError "expected output directory")
  for (name, source) in [("ABI", abiSource), ("Endpoint", endpointSource)] do
    let path := System.FilePath.mk directory / ("ZkcSecurity/Examples/TableMembership/" ++ name ++ ".lean")
    IO.FS.createDirAll path.parent.get!
    IO.FS.writeFile path source

end ZkcSecurity.Generation.TableMembership

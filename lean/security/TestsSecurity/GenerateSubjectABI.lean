import ZkcSecurity.Generation.SubjectABI.Command
import ZkcSecurity.Examples.Generated.SmallSumcheck
import ZkcSecurity.Examples.Generated.TwoSums

/-! Configuration selects actual subjects and output modules. No source fields,
roles, positions, helper indices or policy numbers are supplied by the author. -/
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
namespace TestsSecurity.GenerateSubjectABI
open ZkcSecurity.Generation.SubjectABI

derive_subject_abi smallSource for ZkcSecurity.Examples.Generated.SmallSumcheck.subject
  module "ZkcSecurity.Examples.Generated.Components.SmallSumcheckABI"
  from "ZkcSecurity.Examples.Generated.SmallSumcheck"

derive_subject_abi twoSource for ZkcSecurity.Examples.Generated.TwoSums.subject
  module "ZkcSecurity.Examples.Generated.Components.TwoSumsABI"
  from "ZkcSecurity.Examples.Generated.TwoSums"

def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "expected output directory")
  for (name, text) in [("SmallSumcheck", smallSource), ("TwoSums", twoSource)] do
    let path := System.FilePath.mk directory / "ZkcSecurity/Examples/Generated/Components" /
      (name ++ "ABI.lean")
    IO.FS.createDirAll path.parent.get!
    IO.FS.writeFile path text
    IO.println s!"generated {name}ABI"

end TestsSecurity.GenerateSubjectABI

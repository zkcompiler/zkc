import Zkc.Tests.Formal.Receipts
import Zkc.Tests.Core.Files

/-! The tool `zkc-formal-receipts`: the receipts of the statements at packages, as JSON.

It reads the texts that the subjects were read from, prints each receipt with the digest of
each text and the result of each executable check, and fails when a check does not hold.
-/

open Zkc.Core Zkc.Formal

/-- The files of the texts of the receipts, in the order of `receipts`. -/
def textFiles : List (List String) :=
  [[package_file "../compiler/fixtures/construction/schnorr-frontend-scheme.json",
      package_file "../compiler/fixtures/construction/schnorr-frontend-scheme.declaration.json"],
    [package_file "fixtures/sumcheck-ten-rounds.json"]]

def main : IO UInt32 := do
  let mut printed : Array String := #[]
  let mut held := true
  for (receipt, files) in receipts.zip textFiles do
    let digests ← files.mapM fun (file : String) => do
      let bytes ← IO.FS.readBinFile file
      pure (Concrete.hex (Concrete.bytesOf (Concrete.Sha256.digest bytes)))
    printed := printed.push (receipt.render digests)
    unless receipt.checked do
      held := false
  IO.println ("[" ++ ",\n".intercalate printed.toList ++ "]")
  return if held then 0 else 1

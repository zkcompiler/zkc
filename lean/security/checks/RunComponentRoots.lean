import TestsSecurity.GenerateSumcheckCompleteness
import TestsSecurity.GenerateSumcheckSoundness

/-! Regenerate the maintained complete component roots into a supplied directory.
Every emitted proof must be compiled before it can supply a claim receipt. -/
def main (args : List String) : IO Unit := do
  TestsSecurity.GenerateSumcheckCompleteness.main args
  TestsSecurity.GenerateSumcheckSoundness.main args

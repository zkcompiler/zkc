import Zkc.Claims.ReceiptAudit

/-! Pure-policy controls and JSON driver for explicitly mocked audit exports.
This test driver is never used by the production receipt reporter. -/
set_option autoImplicit false
open ReceiptAudit

example : classify ⟨true, .available, []⟩ = .certified := rfl
example : classify ⟨true, .available, [⟨.kernel, false, "extra premise"⟩]⟩ = .open := rfl
example : classify ⟨false, .undefined ["registered meaning"], []⟩ = .incomplete := rfl
example : classify ⟨true, .undefined ["registered meaning"], []⟩ = .open := rfl
example : classify ⟨false, .refused, []⟩ = .open := rfl
example : classify ⟨true, .refused, []⟩ = .open := rfl

/-- Every individual admission and kernel condition is necessary for a positive
result, independently of how the proof was constructed or attributed. -/
example (audit : Envelope) (check : Check)
    (positive : classify audit = .certified) (member : check ∈ audit.checks) :
    check.passed = true := by
  exact certified_check audit check positive member

#print axioms ReceiptAudit.certified_iff
#print axioms ReceiptAudit.certified_check

def main : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    let result := Lean.Json.parse line >>= ReceiptAudit.run
    let value := match result with
      | .ok value => value
      | .error error => Lean.Json.mkObj [("error", .str error)]
    output.putStrLn value.compress
    output.flush

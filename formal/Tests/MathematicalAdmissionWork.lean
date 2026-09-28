import Zkc.Source.Mathematical.AdmissionWork
import Tests.MathematicalGraphResolution
import Tests.MathematicalProtocolResolution
import Tests.Checks

set_option autoImplicit false
namespace Tests.MathematicalAdmissionWork
open Zkc.Source.Mathematical

inductive Error where
  | resource | callback
  deriving DecidableEq, BEq, Repr

def sequential : AdmissionWork.Meter Error Nat := do
  let count ← AdmissionWork.length .resource [0, 1, 2]
  AdmissionWork.before .resource 2 (fun _ => .ok count)

example {amount available remaining : Nat}
    (accepted : AdmissionWork.consume Error.resource amount available = .ok ((), remaining)) :
    remaining + amount = available := AdmissionWork.consume_residual _ accepted

example {values : List Nat} {available count remaining : Nat}
    (accepted : AdmissionWork.length Error.resource values available = .ok (count, remaining)) :
    count = values.length ∧ remaining + count = available := by
  obtain ⟨same, exact⟩ := AdmissionWork.length_residual Error.resource values accepted
  exact ⟨same, same ▸ exact⟩

def run : IO Unit := do
  let checks ← Checks.start
  checks.holds (match sequential 5 with | .ok (3, 0) => true | _ => false)
    "list measurement and next action share exact allowance"
  checks.holds (match sequential 4 with | .error .resource => true | _ => false)
    "later action cannot reset exhausted allowance"
  checks.holds (match (AdmissionWork.before Error.resource 2 (fun _ => .error .callback) 1 :
    Except Error (Nat × Nat)) with | .error .resource => true | _ => false)
    "charge refusal precedes callback failure"
  checks.holds (match (AdmissionWork.before Error.resource 2 (fun _ => .error .callback) 2 :
    Except Error (Nat × Nat)) with | .error .callback => true | _ => false)
    "affordable callback retains its own refusal"
  checks.holds (match AdmissionWork.length Error.resource (List.replicate 100000 ()) 3 with
    | .error .resource => true | _ => false)
    "length measurement refuses at its allowance before scanning the long remainder"
  checks.holds (match AdmissionWork.checked Error.resource id
      (fun available => .ok ((), available + 1)) 5 with
    | .error .resource => true | _ => false) "callback cannot replenish the allowance"
  checks.holds (match AdmissionWork.checked Error.resource id
      (fun _ => .ok ((), 2)) 5 with
    | .ok ((), 2) => true | _ => false) "callback returns its exact smaller allowance"
  checks.holds (match AdmissionWork.checked (Value := Unit) Error.resource (fun (_ : Unit) => Error.callback)
      (fun _ => .error ()) 5 with
    | .error .callback => true | _ => false) "callback error mapping preserves the refusal"
  let captures : List (Raw.Reference .value) := List.replicate 100000 ⟨0⟩
  checks.holds (match (GraphResolution.region MathematicalGraphResolution.resolver 65
    (.mk captures [] [])).run' 3 with
    | .error .resource => true | _ => false) "carrier capture-list measurement is bounded"
  checks.holds (match (ProtocolResolution.body MathematicalProtocolResolution.resolver 65
    (.mk [] (.ret captures))).run' 3 with
    | .error .resource => true | _ => false) "carrier return-list measurement is bounded"
  checks.finish "mathematical shared admission work"

#eval run
end Tests.MathematicalAdmissionWork

import Zkc.Source.Mathematical.DataBounds
import Tests.MathematicalProtocol
import Tests.Checks

set_option autoImplicit false
namespace Tests.MathematicalRootRequirements
open Zkc.Source.Mathematical
open MathematicalGraph (privatePort)
open MathematicalProtocol (vocabulary capabilities)

def form (body : Protocol.Raw Nat vocabulary) := Protocol.form [0, 1] capabilities []
  Data.capacity MathematicalGraph.countValid 64 [privatePort] [privatePort] 0 body

def localBody (second : Nat) : Protocol.Raw Nat vocabulary :=
  .local 0 0 .distinct [0, second] [0] (.ret [0])

def repeated (count : Nat) : Protocol.Raw Nat vocabulary :=
  .repeat 0 count [privatePort] [0] []
    (.local 1 0 .distinct [0, 1] [1] (.ret [0])) (.ret [0])

def requirements (body : Protocol.Raw Nat vocabulary) : Except Protocol.Error (List Protocol.RootRequirement) :=
  return (← form body).program.rootRequirements

def discharge (body : Protocol.Raw Nat vocabulary) : Bool :=
  match form body with
  | .ok result => result.dischargeRoots.isOk
  | .error _ => false

-- Admission proves every retained local obligation, including those in an
-- indexed body that executes zero times. This is a general certificate theorem.
example {Role : Type} [DecidableEq Role] {vocabulary : Protocol.Vocabulary}
    {parties capabilities scope Γ results start raw}
    (result : Protocol.Decoded (Role := Role) parties vocabulary capabilities scope Γ results start raw)
    {requirement : Protocol.RootRequirement} (member : requirement ∈ result.program.rootRequirements) :
    requirement.valid = true := result.program.requirement_valid result.roots member

def run : IO Unit := do
  let checks ← Checks.start
  checks.holds ((form (localBody 1)).isOk) "template formation retains an unresolved root requirement"
  checks.holds (match requirements (localBody 1) with
    | .ok [⟨0, [7, 7], [(0, 1)]⟩] => true | _ => false) "operation site, selected roots and exact pairs retained"
  checks.holds (!(discharge (localBody 1))) "closed admission rejects aliased actual roots"
  checks.holds (discharge (localBody 2)) "closed admission accepts distinct actual roots"
  checks.holds (match requirements (repeated 0), requirements (repeated 1000000000) with
    | .ok a, .ok b => a == [⟨1, [7, 7], [(0, 1)]⟩] && a == b
    | _, _ => false) "repeat keeps one obligation independent of count"
  checks.holds (!(discharge (repeated 0))) "zero iterations do not erase a reachable instance obligation"
  checks.holds (!(form (.local 0 1 .distinct [0, 1] [0] (.ret [0]))).isOk) "formation still checks permissions"
  checks.holds (!(form (.local 0 0 .distinct [0, 3] [0] (.ret [0]))).isOk) "formation still checks service signatures"
  checks.holds (!(form (.local 1 0 .distinct [0, 1] [0] (.ret [0]))).isOk) "formation still checks dense sites"
  checks.holds (discharge (.local 0 0 .shared [0, 0] [0] (.ret [0]))) "aliasing remains valid without a distinct requirement"
  checks.finish "mathematical root obligations"

#eval run
end Tests.MathematicalRootRequirements

import Examples.TableProtocol.Endpoint

/-! Shared consumer selection and certificate checking for the table policies.
Both direct and physical tools apply this to their checked logical region. -/
set_option autoImplicit false
namespace Zkc.Tools.TableAdmission
open Lean Zkc.Source Zkc.Compiler TableProtocol

structure Request where
  profile : String
  certificate : Json
  entry : Option Json := none

def check {Γ : List Ty} {ty : Ty} (actor : String)
    (region : Region Protocol.language Γ ty) (request : Option Request) :
    Except String (Option Endpoint.Entry) := do
  let some request := request | return none
  let (start, entry) ← match request.entry with
    | none =>
      if request.profile != Admission.profile then throw "unsupported-phase-profile"
      if actor != "trace" then throw "unsupported-phase-role"
      pure (Admission.Phase.ready, none)
    | some json =>
      if request.profile != Endpoint.profile then throw "unsupported-phase-profile"
      let entry ← Endpoint.decodeEntry json
      if entry.actor != Endpoint.role || actor != entry.actor then throw "endpoint-role-mismatch"
      pure (entry.phase, some entry)
  let certificate ← Admission.certificateCodec.decode request.certificate |>.mapError (·.code)
  let some exits := PhaseAdmission.checkRegion Admission.policy region certificate [start]
    | throw "phase-not-admitted"
  if !exits.all (· == .ready) then throw "phase-not-admitted"
  return entry

end Zkc.Tools.TableAdmission

module

public import Zkc.Claims.Receipt

@[expose] public section

/-! A method export can produce only a receipt of the already evaluated
meaning. A refused or unavailable attempt never changes the request's meaning
or invents a missing semantic definition. -/

set_option autoImplicit false
namespace Zkc.Claims
universe u
variable {Subject : Type u} {registry : Registry (PropertyExport Subject)}
  {reference : Subject → SubjectRef} {subject : Subject} {request : Wire.Request}
  {resolved : Resolved registry reference subject request}

inductive ProofAttempt (meaning : Evaluated resolved) where
  | refused (reason : String)
  | proved (receipt : Receipt meaning)

structure MethodExport (meaning : Evaluated resolved) where
  discharge : Wire.Application → Except ResolutionError (ProofAttempt meaning)

def runMethod {meaning : Evaluated resolved} (methods : Registry (MethodExport meaning))
    (application : Wire.Application) : Except ResolutionError (ProofAttempt meaning) := do
  let entry ← methods.lookup application.identifier
  match entry.definition with
  | none => return .refused ("method definition unavailable: " ++ application.identifier.name)
  | some method => method.discharge application

end Zkc.Claims

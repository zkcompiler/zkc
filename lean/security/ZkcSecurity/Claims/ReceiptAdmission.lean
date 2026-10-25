module

public import ZkcSecurity.Claims.Resolution
public import Zkc.Claims.Receipt

@[expose] public section

/-! Security admission belongs to the exact interpreted subject and request,
independently of a property elaborator. In particular, an extension returning
`True` cannot bypass target/acceptance or full model elaboration. The generic
core receipt remains independent of security models. -/

set_option autoImplicit false
namespace ZkcSecurity.Claims
open Zkc.Claims ZkcSecurity.Endpoint

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
  [Fintype F] {art : Artifacts} {endpoint : Semantics}
  {propertyRegistry : Registry (PropertyExport (Subject F G art endpoint))}
  {reference : Subject F G art endpoint → SubjectRef}
  {subject : Subject F G art endpoint} {request : Wire.Request}
  {resolved : Resolved propertyRegistry reference subject request}

/-- A model registry is a typed index, not a provenance label or a generated
declaration name. The certificate binds structural and full model admission to
the very same subject/request as the enclosed receipt. Report extraction also
recomputes these two checks; conditional equations do not establish admission. -/
structure AdmittedReceipt (modelRegistry : ModelRegistry) (meaning : Evaluated resolved) where
  receipt : Receipt meaning
  checked : subject.check request = .ok ()
  modelAdmitted : ∃ actual, resolveModel modelRegistry F art.original endpoint request.model = .ok (.ok actual)

end ZkcSecurity.Claims

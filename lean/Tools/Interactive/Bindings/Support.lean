import Tools.Interactive.Bindings.Registry

set_option autoImplicit false

namespace Tools.Interactive.Bindings.Support

/-! Shared full-type construction and port selection. Domain modules decide
applicability and implementation eligibility; these helpers do not dispatch names. -/

abbrev Shape := List String × List String

/-- Finite names are authored here and in each domain, independently of the
native compiler and runtime. Resolution determines closed applicability. -/
def implementations (providers : List String) (contract : String) : List String :=
  providers.map (· ++ "/" ++ contract)

def scalarArgument (binding : Declaration) : Result String := do
  let [field] := binding.arguments | throw "binding-static-arity"
  ensure (scalarDomain field) "binding-static-arguments"
  return field

def scalarBackend (field : String) : String :=
  if field == ristrettoScalar then "dalek/"
  else if field == koalaBear || field == koalaBearExt8 then "plonky3/"
  else if field == fr || field == bn254Fr then "arkworks/"
  else ""

def typed (kind : String) (field : String := fr) (group : String := g1)
    (transcript : String := transcriptIdentity) : ValueType :=
  let identity := if domainIndependent kind then ""
    else if ["group", "groups"].contains kind then group
    else if ["commitment", "proof", "opening_state", "prover_key", "verifier_key"].contains kind then pcs
    else if kind == "transcript" then transcript else field
  ValueType.mk kind identity ""

def signature (shape : Shape) (field : String := fr) (group : String := g1)
    (transcript : String := transcriptIdentity) : Signature :=
  ⟨shape.1.map (fun kind => typed kind field group transcript),
    shape.2.map (fun kind => typed kind field group transcript)⟩

/-- Preserve logical validation before implementation refusal, and validate an
explicit implementation even when the requested ports are logical. -/
def realize (physical : Bool) (binding : Declaration) (logical : Signature)
    (backend : String) (alternatives : List String := [])
    (representation : Bool → Nat → ValueType → String := fun _ _ ty => ty.defaultRepresentation) : Result Signature := do
  ensure ((logical.inputs ++ logical.outputs).all (·.valid false)) "binding-domain-not-supported"
  ensure ((!physical && binding.implementation.isEmpty) ||
    (!backend.isEmpty && binding.implementation == backend ++ binding.contract) ||
    alternatives.contains binding.implementation) "binding-implementation"
  let port := fun output i (ty : ValueType) =>
    { ty with representation := if physical then representation output i ty else "" }
  return ⟨logical.inputs.zipIdx |>.map (fun (ty, i) => port false i ty),
    logical.outputs.zipIdx |>.map (fun (ty, i) => port true i ty)⟩

end Tools.Interactive.Bindings.Support

module

public import ZkcSecurity.FiatShamir.Binding
public import Zkc.Construction.DomainPublicBinding
public import ZkcSecurity.Endpoint.DomainCompiled

@[expose] public section

/-! The adaptive codec reuses the core public binding used by honest preparation.
Determination covers every raw typed statement, independently of shape validity.
Source coordinates and application identity remain explicit request choices. -/
set_option autoImplicit false
namespace ZkcSecurity.FiatShamir.DomainReduction
open Zkc.Source Zkc.Construction
variable {carriers : Structured.Carriers}

/-- The checked selection proves exact public-coordinate arity. -/
theorem policyArity {art : ZkcSecurity.Endpoint.Domain.Artifacts}
    (compiled : ZkcSecurity.Endpoint.Domain.Compiled art) :
    art.participant.policy.publicInputs.length = art.publics.length := by
  rw [← compiled.publics]
  exact Domain.PublicBinding.selectionArity compiled.imported art.participant
    compiled.selection compiled.checked

/-- Raw vectors and counts remain injectively bound, including malformed ones. -/
def policyCodec (tys : List Structured.Ty) (positions : List Nat)
    (arity : positions.length = tys.length) (application : String) :
    BindingCodec (Values carriers.Value tys) (Domain.Event carriers) :=
  BindingCodec.single Domain.Event.publicBinding (fun _ _ same => by cases same; rfl)
    application (fun values => Domain.PublicBinding.row positions values arity)
    (Domain.PublicBinding.row_injective positions arity)

theorem policyCodec_encode (tys : List Structured.Ty) (positions : List Nat)
    (arity : positions.length = tys.length) (application : String)
    (values : Values carriers.Value tys) :
    (policyCodec tys positions arity application).encode values =
      Domain.PublicBinding.history application positions values arity := rfl

theorem policyCodec_determined (tys : List Structured.Ty) (positions : List Nat)
    (arity : positions.length = tys.length) (application : String) :
    Typed.Determined (policyCodec (carriers := carriers) tys positions arity application).encode :=
  (policyCodec tys positions arity application).determined

end ZkcSecurity.FiatShamir.DomainReduction

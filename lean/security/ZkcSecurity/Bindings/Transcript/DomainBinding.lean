module

public import ZkcSecurity.Transformations.FiatShamir.Binding
public import Zkc.Construction.DomainPublicBinding
public import ZkcSecurity.Bindings.Participants.DomainCompiled

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

/-- Public eligibility follows from the same checked selection as public arity. -/
theorem policyData {art : ZkcSecurity.Endpoint.Domain.Artifacts}
    (compiled : ZkcSecurity.Endpoint.Domain.Compiled art) :
    Domain.PublicBinding.DataSchema art.publics := by
  rw [← compiled.publics]
  exact Domain.PublicBinding.selectionData compiled.imported art.participant
    compiled.selection compiled.checked

/-- Every raw data value is bound directly, including malformed relation inputs. -/
def publicCodec (tys : List Structured.Ty) (positions : List Nat)
    (arity : positions.length = tys.length) (data : Domain.PublicBinding.DataSchema tys)
    (application : String) : BindingCodec (Values carriers.Value tys) (Domain.Event carriers) :=
  BindingCodec.singleton
    (fun values => .publicBinding ⟨application, Domain.PublicBinding.encodeRow positions values arity data⟩)
    (by
      intro first second same
      exact Domain.PublicBinding.encodeRow_injective positions arity data
        (congrArg Domain.PublicBinding.row (Domain.Event.publicBinding.inj same)))

/-- The compiled policy owns its schema, source coordinates and admissibility.
Callers cannot supply an unrelated row or truncate its arity. -/
def policyCodec {art : ZkcSecurity.Endpoint.Domain.Artifacts}
    (compiled : ZkcSecurity.Endpoint.Domain.Compiled art) (application : String) :
    BindingCodec (Values carriers.Value art.publics) (Domain.Event carriers) :=
  publicCodec art.publics art.participant.policy.publicInputs (policyArity compiled)
    (policyData compiled) application

theorem policyCodec_encode {art : ZkcSecurity.Endpoint.Domain.Artifacts}
    (compiled : ZkcSecurity.Endpoint.Domain.Compiled art) (application : String)
    (values : Values carriers.Value art.publics) :
    (policyCodec compiled application).encode values =
      Domain.PublicBinding.history application art.participant.policy.publicInputs values
        (policyArity compiled) (policyData compiled) := rfl

theorem policyCodec_determined {art : ZkcSecurity.Endpoint.Domain.Artifacts}
    (compiled : ZkcSecurity.Endpoint.Domain.Compiled art) (application : String) :
    Typed.Determined (policyCodec (carriers := carriers) compiled application).encode :=
  (policyCodec compiled application).determined

end ZkcSecurity.FiatShamir.DomainReduction

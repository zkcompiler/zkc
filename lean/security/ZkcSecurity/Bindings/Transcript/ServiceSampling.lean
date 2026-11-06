module

public import VCVio.OracleComp.Constructions.SampleableType.Basic
public import Zkc.Construction.DomainTranscript

@[expose] public section

/-! Honest finite ideal samplers reuse the pinned VCVio Fin and Fin-function
instances, including their uniformity proofs. Source service behavior remains
adversarial; these declarations do not install an honest source interpreter. -/
set_option autoImplicit false
namespace ZkcSecurity.FiatShamir.ServiceSampling
open Zkc.Source Zkc.Construction

@[instance_reducible] def index (carriers : Structured.Carriers) (bound : Nat) :
    SampleableType (Request.Raw carriers (.sampleIndex bound)) := by
  change SampleableType (Fin (Request.replyBound bound))
  letI : NeZero (Request.replyBound bound) := ⟨Nat.ne_of_gt (Request.replyBound_positive bound)⟩
  exact inferInstance

@[instance_reducible] noncomputable def block (carriers : Structured.Carriers) (bound count : Nat) :
    SampleableType (Request.Raw carriers (.sampleIndices bound count)) := by
  change SampleableType (Fin count → Fin (Request.replyBound bound))
  letI : NeZero (Request.replyBound bound) := ⟨Nat.ne_of_gt (Request.replyBound_positive bound)⟩
  exact inferInstance

/-- A finite honest oracle family for the existing generic transcript adapter.
Field samplers remain explicit nominal assumptions; no sampler for Nat is used.
Malformed/nonquery keys have their finite inert carriers and are never promoted
to valid source or constructed requests by supplying this family. -/
@[instance_reducible] noncomputable def request (carriers : Structured.Carriers)
    (fields : ∀ field, SampleableType (carriers.Field field))
    (value : Request) : SampleableType (Request.Raw carriers value) := by
  rcases value with ⟨method, operands, sort⟩
  cases sort <;> try (change SampleableType Unit; exact inferInstance)
  case field field => exact fields field
  case index => exact index carriers (operands.headD 0)
  case indices => exact block carriers (operands.headD 0) (operands[1]?.getD 0)

@[instance_reducible] noncomputable def raw (carriers : Structured.Carriers)
    (fields : ∀ field, SampleableType (carriers.Field field)) :
    (event : Domain.Event carriers) → SampleableType (Domain.Raw event)
  | .challenge ⟨_, _, some value⟩ => request carriers fields value
  | .challenge ⟨_, _, none⟩ => inferInstanceAs (SampleableType Unit)
  | .message .. | .publicBinding .. => inferInstanceAs (SampleableType Unit)

end ZkcSecurity.FiatShamir.ServiceSampling

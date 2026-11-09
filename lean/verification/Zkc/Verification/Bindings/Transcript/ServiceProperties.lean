module

public import Zkc.Verification.Bindings.Transcript.DomainSourceReading
public import Zkc.Verification.ProgramLogic.Derivation
public import Zkc.Protocol.Logic.Transcript.CostComposition

@[expose] public section

/-! Reusable property rules for the ordinary nominal request kernel. The caller
supplies its existing escape law and all decoded continuations. No sampler or
probability semantics is installed by these rules. -/
set_option autoImplicit false
namespace ZkcSecurity.FiatShamir.ServiceProperties
open PIR Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Transcript Zkc.Obligations
open OracleComp OracleSpec
variable {carriers : Carriers} {A : Type}

/-- Transport only along the exact request equality; host carriers confer no
nominal service identity. -/
def rawReply {origin : Origin} {request : Request} (same : origin.request = some request)
    (raw : Domain.Raw (.challenge origin : Domain.Event carriers)) : Request.Raw carriers request :=
  by simpa only [Domain.Raw, same] using raw

variable [∀ event : Domain.Event carriers, SampleableType (Domain.Raw event)]

/-- One query rule for field, scalar and block requests, with every refusal and
every raw-dependent continuation. The caller retains the complete return state. -/
noncomputable def derivation (state : Original.State carriers) (origin : Origin) (request : Request)
    (price : ENNReal) (Post : Domain.History carriers → A → Prop)
    (next : carriers.Value request.sort × Original.State carriers → PIR.Process (NominalDomain.signature carriers) A)
    (bad : Request.Raw carriers request → Prop)
    (bounded : ∀ same : origin.request = some request,
      Pr{let raw ← $ᵗ (Domain.Raw (.challenge origin : Domain.Event carriers))}[bad (rawReply same raw)] ≤ price)
    (continuations : ∀ raw value, request.decode raw = some value → ¬ bad raw →
      Derivation NominalDomain.interface (ZkcSecurity.Obligations.boundedEscape (fun _ _ => price))
        Post (state.history ++ [.challenge origin])
        (next (value, { state with history := state.history ++ [.challenge origin] }))) :
    Derivation NominalDomain.interface (ZkcSecurity.Obligations.boundedEscape (fun _ _ => price))
      Post state.history ((DomainSourceReading.queryRequest state origin request).bind next) := by
  unfold DomainSourceReading.queryRequest
  by_cases valid : request.valid = true
  · simp only [valid, ↓reduceDIte]
    by_cases same : origin.request = some request
    · simp only [same, ↓reduceDIte, PIR.Process.bind]
      refine .query rfl (fun raw => bad (rawReply same raw)) (bounded same) ?_
      intro raw reply decoded outside
      cases decoded
      cases decoded : request.decode (carriers := carriers)
          (by simpa only [Domain.Raw, same] using raw) with
      | none => exact .halt .refused
      | some value => exact continuations _ value decoded outside
    · simp only [same, ↓reduceDIte, PIR.Process.bind]
      exact .halt .refused
  · simp only [valid]
    exact .halt .refused

omit [∀ event : Domain.Event carriers, SampleableType (Domain.Raw event)] in
/-- Pathwise cost uses the same decoder and one charge for the whole block. -/
theorem cost (state : Original.State carriers) (origin : Origin) (request : Request)
    (price budget remaining : ENNReal) (charged : price + remaining ≤ budget)
    (next : carriers.Value request.sort × Original.State carriers → PIR.Process (NominalDomain.signature carriers) A)
    (continuations : ∀ raw value, request.decode raw = some value →
      Typed.ChargedCostBound NominalDomain.interface (fun _ _ => price)
        (next (value, { state with history := state.history ++ [.challenge origin] }))
        (state.history ++ [.challenge origin]) remaining) :
    Typed.ChargedCostBound NominalDomain.interface (fun _ _ => price)
      ((DomainSourceReading.queryRequest state origin request).bind next) state.history budget := by
  unfold DomainSourceReading.queryRequest
  by_cases valid : request.valid = true
  · simp only [valid, ↓reduceDIte]
    by_cases same : origin.request = some request
    · simp only [same, ↓reduceDIte, PIR.Process.bind, Typed.ChargedCostBound, NominalDomain.interface]
      refine ⟨remaining, charged, fun raw => ?_⟩
      cases decoded : request.decode (carriers := carriers)
          (by simpa only [Domain.Raw, same] using raw) with
      | none => trivial
      | some value => exact continuations _ value decoded
    · simp only [same, ↓reduceDIte, PIR.Process.bind]
      trivial
  · simp only [valid]
    trivial

end ZkcSecurity.FiatShamir.ServiceProperties

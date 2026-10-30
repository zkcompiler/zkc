module

public import Zkc.Claims.Registry
public import ZkcSecurity.Bindings.Extraction.Profile
public import ZkcSecurity.Endpoint.Contract

@[expose] public section

/-! Request-owned extraction interfaces. These are registered semantic inputs,
not evidence. Version zero fixes structural response-difference recovery. -/

set_option autoImplicit false
namespace ZkcSecurity.Claims
open OracleComp OracleSpec
open Zkc.Claims Zkc.Source Zkc.Source.Structured Zkc.Construction ZkcSecurity.Endpoint

def responseDifference : Identifier := ⟨"extractors.response_difference", 0⟩

namespace ExtractionProfile
variable {F G : Type} {art : Artifacts} {compiled : Compiled art}
  (profile : ExtractionProfile compiled F G)

variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

def registry (target : SoundnessTarget compiled F G) (selected : target = .retained profile.target profile.formula) :
    Registry { other : ExtractionProfile compiled F G // target = .retained other.target other.formula } :=
  ⟨[⟨responseDifference, "zkc.extractor.response-difference/0", some ⟨profile, selected⟩⟩]⟩

end ExtractionProfile
end ZkcSecurity.Claims

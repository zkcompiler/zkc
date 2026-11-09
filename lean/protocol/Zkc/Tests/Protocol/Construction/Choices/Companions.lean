module

public import Zkc.Tests.Protocol.Construction.Choices.Templates
public meta import Zkc.Tools.Program.Companions

/-! Author mathematics and typed values. This module imports templates, never assembly. -/

@[expose] public section
noncomputable section
open ProtocolProofExamples.AdaptiveChecks

namespace ProtocolProofExamples.ConstructionChoices

@[zkc "adaptive.scale"] def scale (e : Environment) : Scale :=
  fun remaining => factor e.residual ^ remaining

@[zkc "adaptive.scale-law"] theorem scaleLaw (e : Environment) : ScaleLaw e (scale e) :=
  ⟨pow_zero _, fun _ => pow_succ' _ _⟩

@[zkc "adaptive.budget"] theorem budget (e : Environment) (count : Nat) :
    Budget e count (scale e) := rfl

-- An explicitly selected bad value or law must never fall back to these valid registrations.
@[zkc "adaptive.invalid-scale"] def invalidScale : Bool := true
@[zkc "adaptive.invalid-law"] theorem invalidLaw : True := trivial

end ProtocolProofExamples.ConstructionChoices

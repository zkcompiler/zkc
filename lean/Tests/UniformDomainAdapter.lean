import Zkc.Construction.ScalarAdapter

/-! Controls for the partial scalar operand adapter and nominal execution. -/
set_option autoImplicit false
namespace Tests.UniformDomainAdapter
open Zkc.Source Zkc.Construction
open Zkc.Construction.Uniform.DomainAdapter
variable {F G : Type}

example : embedData (F := F) (G := G) .unsupported = none := rfl
example (history : History F G) : embedData (.transcript history) = none := rfl

-- Indices remain arbitrary data, without an artificial relation-validity bound.
example (index : Nat) : embedData (F := F) (G := G) (.index index) =
    some (.data (.index index)) := rfl

example (value : F) :
    Domain.Value.decode (.field "other")
        (.data (.field "selected" value) : Domain.Value (Structured.uniformCarriers F G)) = none := by
  simp [Domain.Value.decode, Domain.Payload.value]

example (values : List F) :
    embedData (G := G) (.vector "selected" values) =
      Domain.Value.encode (.vector "selected") values :=
  encode_embed (F := F) (G := G) (.vector "selected") rfl values

-- Aggregate support in Domain does not silently extend the legacy ABI.
example (values : List Bool) :
    readbackData (F := F) (G := G) (.data ⟨.sequence .boolean, rfl, values⟩) = none := rfl

section Execution
variable [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

-- The runner theorem applies to a malformed nominal operand as well as returns.
example (value : F) :
    Domain.calculate (Structured.ringModel F G) (.fieldAdd "selected")
        [.data (.field "selected" value), .data (.field "other" value)] =
      embedOutcome (Zkc.Construction.calculate (.fieldAdd "selected")
        [.data (.field "selected" value), .data (.field "other" value)]) :=
  calculate_embed _ rfl (by simp [embedData, embedValues])

example (values : List F) (index : Nat) :
    Domain.calculate (Structured.ringModel F G) (.boundedAt "selected")
        [.data (.vector "selected" values), .data (.index index)] =
      embedOutcome (Zkc.Construction.calculate (.boundedAt "selected")
        [.vector "selected" values, .index index]) :=
  calculate_embed _ rfl (by simp [embedData, embedValues])

example :
    Zkc.Construction.calculate (F := F) (G := G) (.boundedAt "selected")
        [.vector "selected" [], .index 0] = .stopped .refused := rfl

example :
    Zkc.Construction.calculate (F := F) (G := G) (.indexConstant 0) [.index 0] =
      .stopped .refused := rfl

-- A guard with an invalid result declaration must refuse even on a true input.
example (program : Structured.Program) (context : Context) :
    Domain.step (Structured.ringModel F G) program context
        ⟨.guard "guard", [0], [.data .boolean], []⟩ [.data (.boolean true)] =
      .halt .refused := by
  simp [Domain.step]

end Execution
end Tests.UniformDomainAdapter

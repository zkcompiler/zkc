module

public import Zkc.Semantics.Interaction

@[expose] public section
set_option autoImplicit false
namespace PIR
variable {I : Signature} {A B : Type} {P : Interaction I}

/-- A returned-response prefix is preserved when the same continuation is
attached at both ends. The interaction phase and every reply stay unchanged. -/
theorem Reaches.bind {first last : Process I A} {initial final : P.Phase}
    (path : Reaches P first initial last final) (next : A → Process I B) :
    Reaches P (first.bind next) initial (last.bind next) final := by
  induction path with
  | refl => exact .refl _ _
  | step operation continuation phase reply residual finish rest ih =>
      exact .step operation (fun value ↦ (continuation value).bind next) phase reply
        (residual.bind next) finish ih

end PIR

import ZkcSecurityTools.Components

/-! A separate consumer checks that the facade exports elaborator code as well
as theorem declarations through the public module interface. -/
namespace Client
open Zkc.Transcript Zkc.Obligations ZkcSecurity.Obligations

noncomputable def rejected {I : PIR.Signature} {E P : Type} {Raw : E → Type}
    [∀ event, SampleableType (Raw event)]
    (absorb : Interface I E P Raw) (charge : List E → E → ENNReal)
    (history : List E) :
    Derivation absorb (boundedEscape charge) (fun _ (value : Bool) => value = false)
      history (.done false) := by
  derive_component_rejection [] unfolding [] finishing rfl

end Client

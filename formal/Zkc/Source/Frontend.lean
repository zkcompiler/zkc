import Zkc.Source.Endpoint
import Zkc.Source.Elaboration

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace PIR.Source
open Zkc.Source.Expressions
open Zkc.Source.Availability

variable {F : Type} [Ring F] [DecidableEq F]
variable {I : Signature} {Role H : Type} [DecidableEq Role]

/-- The pure frontend uses the actual ordered role input reader and checks
    every declared capture before returning the elaborated computation. -/
def pureFrontend : Frontend I Role F where
  Source := Closure Nat
  Binding := List (SourceView.Slot Role) × SourceView.World Role F H
  inputs := fun c binding actor =>
    ready (List.range binding.1.length) (SourceView.env actor binding.1 binding.2)
      (captureDeps c) = true
  elaborate := fun c binding actor =>
    (admit actor binding.1 binding.2 c).map (elaborate (I := I))

def pureContract (P : Interaction I) (phase : P.Phase) (value : F) :
    EndpointContract P F := ⟨phase, 0, fun result after => result = value ∧ after = phase⟩

theorem pure_admitted (P : Interaction I) [DecidableEq P.Role] (phase : P.Phase)
    (actor : P.Role) (bindings : List (SourceView.Slot P.Role))
    (world : SourceView.World P.Role F H) (c : Closure Nat) (b : Bound c.size F)
    (accepted : admit actor bindings world c = some b) :
    Admitted pureFrontend (pureContract P phase b.value)
      c (bindings, world) actor (elaborate b) := by
  have hb := elaboration_boundary b P phase
  refine ⟨?_, ?_, hb.1, hb.2.1, hb.2.2⟩
  · change (admit actor bindings world c).map _ = _
    rw [accepted]
    rfl
  · change ready (List.range bindings.length) (SourceView.env actor bindings world)
      (captureDeps c) = true
    unfold admit issue at accepted
    split at accepted
    · assumption
    · contradiction

end PIR.Source

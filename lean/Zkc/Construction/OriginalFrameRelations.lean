module

public import Zkc.Construction.OriginalABI
public import Zkc.Construction.ArtifactBinding

@[expose] public section
/-! Strengthen structural certificates with complete original input locations.
Every optional component is checked, including absent values and capabilities. -/
set_option autoImplicit false
namespace Zkc.Construction.Original
open Zkc.Source
variable {carriers : Structured.Carriers} {A B : Type}

noncomputable def Simulation.mapRelations
    {returns nextReturns : A → B → Prop}
    {live nextLive : PIR.Process (Domain.effects carriers) A → Domain.Environment carriers → Prop}
    {source : PIR.Process (Domain.effects carriers) A} {target : PIR.Process (Domain.effects carriers) B}
    (certificate : Simulation returns live source target)
    (returned : ∀ a b, returns a b → nextReturns a b)
    (frames : ∀ process frame, live process frame → nextLive process frame) :
    Simulation nextReturns nextLive source target := by
  induction certificate with
  | done related => exact .done (returned _ _ related)
  | halt reason => exact .halt reason
  | call operation next ih => exact .call operation ih
  | checkpoint frame related next ih => exact .checkpoint frame (frames _ _ related) ih

def LocationsBound (size : Nat) (locations : List Location) : Prop :=
  ∀ reference, Location.data reference ∈ locations → reference < size

theorem valuesHolds_of_captures
    {captured frame : Domain.Environment carriers} {locations : List Location} {types : List Structured.Ty}
    (values : Values (Component carriers.Value) types)
    (bound : LocationsBound captured.length locations)
    (related : ValuesHolds captured locations values)
    (retained : ArtifactBinding.Captures captured frame) :
    ValuesHolds frame locations values := by
  have split : frame = captured ++ frame.drop captured.length := by
    calc
      frame = frame.take captured.length ++ frame.drop captured.length :=
        (List.take_append_drop captured.length frame).symm
      _ = captured ++ frame.drop captured.length := by rw [retained]
  rw [split]
  induction values generalizing locations with
  | nil => cases locations <;> exact related
  | @cons ty types value rest ih =>
    cases locations with
    | nil => exact False.elim related
    | cons location locations =>
      obtain ⟨head, tail⟩ := related
      refine ⟨?_, ih (fun reference present => bound reference (by simp [present])) tail⟩
      cases location with
      | absent => exact head
      | capability handle => cases ty <;> exact head
      | data reference =>
        have inside := bound reference (by simp)
        simpa only [ComponentHolds, List.getElem?_append_left inside] using head

/-- This fixes the full original input tuple and physical input schema before
certificate search. Every source input has a location; no free location exists. -/
def InputLive (abi : InputABI) {types : List Structured.Ty}
    (values : Values (Component carriers.Value) types) (captured : Domain.Environment carriers)
    (_source : PIR.Process (Domain.effects carriers) A) (frame : Domain.Environment carriers) : Prop :=
  Domain.sortsMatch abi.sorts captured = true ∧
    ArtifactBinding.Captures captured frame ∧ ValuesHolds frame abi.locations values

theorem inputLive_of_captures (abi : InputABI) {types : List Structured.Ty}
    (values : Values (Component carriers.Value) types) (captured frame : Domain.Environment carriers)
    (process : PIR.Process (Domain.effects carriers) A)
    (sorts : Domain.sortsMatch abi.sorts captured = true)
    (bound : LocationsBound captured.length abi.locations)
    (related : ValuesHolds captured abi.locations values)
    (retained : ArtifactBinding.Captures captured frame) :
    InputLive abi values captured process frame :=
  ⟨sorts, retained, valuesHolds_of_captures values bound related retained⟩

end Zkc.Construction.Original

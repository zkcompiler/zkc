module

public import Zkc.Construction.OriginalFrameRelations
public import Zkc.Construction.DomainView

@[expose] public section

/-! Complete participant installation from a full body certificate. The return
selector, declared sorts, original optional ABI and live frame relation are all
checked at the boundary. This rule is independent of protocol and property. -/
set_option autoImplicit false
namespace Zkc.Construction.Original
open Zkc.Source
variable {carriers : Structured.Carriers} {A : Type}

noncomputable def Simulation.participant
    (abi : InputABI) {types : List Structured.Ty}
    (values : Values (Component carriers.Value) types)
    (inputs : Domain.Environment carriers)
    (outputSorts : List ValueSort) (returned : List Nat)
    (body : Domain.View.Block carriers)
    (source : PIR.Process (Domain.effects carriers) A)
    (bodyReturns : A → Domain.Environment carriers → Prop)
    (returns : A → Domain.Result carriers → Prop)
    (sorts : Domain.sortsMatch abi.sorts inputs = true)
    (bound : LocationsBound inputs.length abi.locations)
    (inputValues : ValuesHolds inputs abi.locations values)
    (certificate : Simulation bodyReturns
      (fun _ frame => ArtifactBinding.Captures inputs frame) source (body inputs))
    (readback : ∀ original frame, bodyReturns original frame →
      ∃ output, Domain.read frame returned = some output ∧
        Domain.sortsMatch outputSorts output = true ∧ returns original ⟨output, frame⟩) :
    Simulation returns (InputLive abi values inputs) source
      (Domain.View.participant abi.sorts outputSorts returned body inputs) := by
  have raw : Simulation returns (fun _ frame => ArtifactBinding.Captures inputs frame)
      source (Domain.View.participant abi.sorts outputSorts returned body inputs) := by
    unfold Domain.View.participant
    refine .checkpoint _ (by simp [ArtifactBinding.Captures]) ?_
    simp only [sorts, ↓reduceIte]
    have assembled := certificate.bind
      (returnRelation := returns)
      (nextLive := fun _ frame => ArtifactBinding.Captures inputs frame)
      (sourceNext := fun value => .done value)
      (targetNext := fun frame =>
        match Domain.read frame returned with
        | some output => if Domain.sortsMatch outputSorts output then
            .done ⟨output, frame⟩ else .halt .refused
        | none => .halt .refused)
      (fun _ _ retained => retained) (by
        intro original frame related
        apply Classical.choice
        obtain ⟨output, read, valid, result⟩ := readback original frame related
        refine ⟨?_⟩
        simp only [read, valid, ↓reduceIte]
        exact .done result)
    simp only [PIR.Process.bind_done] at assembled
    exact assembled
  exact raw.mapRelations (fun _ _ related => related) fun process frame retained =>
    inputLive_of_captures abi values inputs frame process sorts bound inputValues retained

end Zkc.Construction.Original

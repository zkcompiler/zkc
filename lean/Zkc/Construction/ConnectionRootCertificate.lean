module

public import Zkc.Construction.ConnectionRoot
public import Zkc.Construction.ConnectionInputLayout
public import Zkc.Construction.ConnectionInputFrames

@[expose] public section

/-! A single reusable root connection. Finite input, body and output certificates
assemble the complete nominal simulation for every physical input row. This
is source-to-artifact correspondence; source/profile admission and reached-route
coverage remain separate gates, and no cryptographic property follows alone.
-/
set_option autoImplicit false
namespace Zkc.Construction.ConnectionRoot
open Zkc.Source Zkc.Source.Structured NormalForm ConnectionFrame ConnectionInputs

attribute [local implicit_reducible] CheckedProtocol.signature

/-- A root uses the actual admitted entry and actual constructed instructions.
The generated instruction correspondence is independent of protocol mathematics;
the source correspondence is obtained only from the finite alignment below. -/
structure RootCertificate (program : Program) (routing : Original.Routing) (role : Nat)
    (artifact : Participant) where
  library : ConnectionLibrary.Bundle program.payload := .empty program.payload
  snapshot : routing.snapshot = program.snapshot
  roleValid : role < program.payload.entry.roles.length
  distinct : RosterDistinct {} role program.payload.entry.roles.length
  inputs : InputLayout program.payload.entry.signature routing.context role artifact.inputs
  output : ConnectionInstallation.ReturnLayout program.payload.entry.signature routing.context role artifact
  target : ConnectionCertificate.Block
  correspondence : ∀ model, Domain.Correspondence.Block (model := model) (program := program)
    (context := routing.context) artifact.instructions (target model)
  alignment : ConnectionCertificate.Certificate routing {} program.payload.definitions
    role program.payload.entry.roles.length program.payload.entry inputs.pattern
    output.locations output.historyReference [] inputs.layout target
    library.keys (.selected program.payload rfl library.library)

namespace RootCertificate
variable {program : Program} {routing : Original.Routing} {role : Nat} {artifact : Participant}

/-- The source root, including full ABI refusal and the actual initial history. -/
def source (root : RootCertificate program routing role artifact) (model : DomainModel)
    (physical : Domain.Environment model.toCarriers) :=
  Original.participantFromABI model program routing role root.inputs.abi physical (root.inputs.initial physical)

/-- Every accepted finite root certificate yields the complete actual simulation.
No equality of whole programs, chosen return relation or runtime input restriction
is a premise. This includes malformed input rows and all adversarial replies. -/
@[no_expose] noncomputable def simulation
    (root : RootCertificate program routing role artifact) (model : DomainModel)
    (physical : Domain.Environment model.toCarriers) :
    Original.Simulation
      (Original.CompleteReturns program.payload.entry.signature routing.context role artifact)
      (InputFrames root.inputs.abi program.payload.entry.inputs physical)
      (root.source model physical)
      (Domain.participant model program routing.context artifact physical) := by
  by_cases sorted : Domain.sortsMatch artifact.inputs physical = true
  · apply Classical.choice
    obtain ⟨binders, decoded, related⟩ := root.inputs.prepare model physical sorted
    have found : root.inputs.abi.read physical program.payload.entry.inputs =
        some (root.inputs.pattern.environment model binders) :=
      (Original.InputABI.read_iff _ _ _ _).mpr ⟨sorted, decoded⟩
    have aligned := fromCertificate program routing role artifact root.inputs.abi root.snapshot
      root.inputs.pattern root.inputs.layout root.output root.target root.library root.alignment root.distinct
      root.inputs.visible rfl model (root.correspondence model) binders physical
      (root.inputs.initial physical) rfl sorted
      (root.inputs.shape.physicalBounds root.inputs.sorted sorted) decoded related
    refine ⟨?_⟩
    rw [source, Original.participantFromABI_found model program routing role root.inputs.abi
      physical (root.inputs.initial physical) _ found]
    exact aligned.mapRelations (fun _ _ returned => returned) (by
      intro process frame live
      refine ⟨live.2.1, ?_⟩
      intro values read
      have same := Option.some.inj (found.symm.trans read)
      rw [← same]
      exact live.2.2)
  · have malformed : Domain.sortsMatch artifact.inputs physical = false := Bool.eq_false_iff.mpr sorted
    exact Original.Simulation.malformedABI routing role root.inputs.abi artifact physical
      (root.inputs.initial physical) _ _ rfl malformed ⟨by simp [ArtifactBinding.Captures], by
        intro values found
        simp only [InputLayout.abi, Original.InputABI.read, malformed,
          Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at found⟩

end RootCertificate
end Zkc.Construction.ConnectionRoot

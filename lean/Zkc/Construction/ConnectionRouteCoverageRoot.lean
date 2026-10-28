module

public import Zkc.Construction.ConnectionRouteCoverage
public import Zkc.Construction.ConnectionRootCertificate

@[expose] public section

/-! Produced root facts from the one finite connection certificate. Coverage
is proved on the actual occurrence source before construction can refuse.
The complete ABI and full simulation retain their existing meanings. -/
set_option autoImplicit false
namespace Zkc.Construction.ConnectionRoot
open Zkc.Source Zkc.Source.Structured NormalForm ConnectionFrame ConnectionInputs

attribute [local implicit_reducible] CheckedProtocol.signature

namespace RootCertificate
variable {program : Program} {routing : Original.Routing} {role : Nat} {artifact : Participant}

/-- The original occurrence process with the same full input ABI as source.
Malformed physical rows refuse before any source action. -/
def occurrenceSource (root : RootCertificate program routing role artifact) (model : DomainModel)
    (physical : Domain.Environment model.toCarriers) :
    PIR.Process (Occurrence.signature model.toCarriers)
      (Values (Component model.Value) program.payload.entry.outputs) :=
  match root.inputs.abi.read physical program.payload.entry.inputs with
  | none => .halt .refused
  | some values => Occurrence.participant model program role values

/-- This covered process is exactly the existing root source before folding,
including its original initial state and malformed-ABI refusal. -/
theorem source_eq_fold (root : RootCertificate program routing role artifact) (model : DomainModel)
    (physical : Domain.Environment model.toCarriers) :
    root.source model physical = Original.fold routing (root.occurrenceSource model physical)
      (root.inputs.initial physical) := by
  have snapshot : { routing with snapshot := program.snapshot } = routing := by rw [← root.snapshot]
  unfold source Original.participantFromABI occurrenceSource
  cases found : root.inputs.abi.read physical program.payload.entry.inputs with
  | none => rfl
  | some values => simp only [Original.participant, snapshot]

/-- A produced fact, requiring no extra instance proof or semantic premise. -/
@[no_expose] noncomputable def routeCoverage
    (root : RootCertificate program routing role artifact) (model : DomainModel)
    (physical : Domain.Environment model.toCarriers) :
    Original.RouteCoverage routing [] [] (root.occurrenceSource model physical) := by
  by_cases sorted : Domain.sortsMatch artifact.inputs physical = true
  · apply Classical.choice
    obtain ⟨binders, decoded, related⟩ := root.inputs.prepare model physical sorted
    have found : root.inputs.abi.read physical program.payload.entry.inputs =
        some (root.inputs.pattern.environment model binders) := by
      simpa only [CheckedProtocol.signature] using
        (Original.InputABI.read_iff root.inputs.abi physical _ _).mpr ⟨sorted, decoded⟩
    rw [occurrenceSource, found]
    change Nonempty (Original.RouteCoverage routing [] []
      (invokeProtocol (Occurrence.table model program.payload) program.payload.entry.signature {} role
        (root.inputs.pattern.environment model binders)))
    rw [Occurrence.invoke_body model program.payload _ program.payload.entry_mem]
    simp only [CheckedProtocol.denoteWithOn, ProtocolContext.mapScopes_root]
    have masked : maskValues role program.payload.entry.inputScopes
        (root.inputs.pattern.environment model binders) = root.inputs.pattern.environment model binders := by
      simpa only [CheckedProtocol.signature] using inputScopes_mask _ root.inputs.visible decoded
    rw [masked]
    have body := root.alignment.routeCoverage root.distinct model (Occurrence.helpers model program.payload)
      (fun _ => rfl) (Occurrence.table model program.payload) binders
      (root.inputs.initial physical).history physical related
    refine ⟨body.bind ?_⟩
    intro values
    exact .done _ _
  · have malformed : Domain.sortsMatch artifact.inputs physical = false := Bool.eq_false_iff.mpr sorted
    have missing : root.inputs.abi.read physical program.payload.entry.inputs = none := by
      simp only [InputLayout.abi, Original.InputABI.read, malformed, Bool.false_eq_true, ↓reduceIte]
    rw [occurrenceSource, missing]
    exact .halt _ _ .refused

/-- Reusable produced facts retain the complete ordinary nominal model and
all physical inputs. The coverage field is not inferred from simulation. -/
structure Facts (root : RootCertificate program routing role artifact) where
  sourceEquation : ∀ (model : DomainModel) (physical : Domain.Environment model.toCarriers),
    root.source model physical = Original.fold routing (root.occurrenceSource model physical)
      (root.inputs.initial physical)
  simulation : ∀ (model : DomainModel) (physical : Domain.Environment model.toCarriers),
    Original.Simulation
      (Original.CompleteReturns program.payload.entry.signature routing.context role artifact)
      (InputFrames root.inputs.abi program.payload.entry.inputs physical)
      (root.source model physical) (Domain.participant model program routing.context artifact physical)
  coverage : ∀ (model : DomainModel) (physical : Domain.Environment model.toCarriers),
    Original.RouteCoverage routing [] [] (root.occurrenceSource model physical)

@[no_expose] noncomputable def facts (root : RootCertificate program routing role artifact) : Facts root :=
  ⟨root.source_eq_fold, root.simulation, root.routeCoverage⟩

end RootCertificate
end Zkc.Construction.ConnectionRoot

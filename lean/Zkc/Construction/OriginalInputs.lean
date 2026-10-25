module

public import Zkc.Construction.OriginalABI

@[expose] public section

/-! Full input-ABI normalization of the actual original participant. Malformed
physical inputs refuse before any source effect. Successful decoding recovers
the exact independently admitted source tuple, including optional components
and runtime service capabilities. No artifact instructions supply this view. -/
set_option autoImplicit false
namespace Zkc.Construction.Original
open Zkc.Source
variable {carriers : Structured.Carriers}

def InputABI.read (abi : InputABI) (frame : Domain.Environment carriers)
    (types : List Structured.Ty) : Option (Values (Component carriers.Value) types) :=
  if Domain.sortsMatch abi.sorts frame then readComponents frame types abi.locations else none

theorem InputABI.read_iff (abi : InputABI) (frame : Domain.Environment carriers)
    (types : List Structured.Ty) (values : Values (Component carriers.Value) types) :
    abi.read frame types = some values ↔
      Domain.sortsMatch abi.sorts frame = true ∧ ValuesHolds frame abi.locations values := by
  cases shape : Domain.sortsMatch abi.sorts frame <;>
    simp only [InputABI.read, shape, Bool.false_eq_true, ↓reduceIte,
      readComponents_iff, false_and, true_and, reduceCtorEq]

def participantFromABI (model : Structured.DomainModel) (program : Structured.Program)
    (routing : Routing) (self : Nat) (abi : InputABI)
    (inputs : Domain.Environment model.toCarriers) (initial : State model.toCarriers := {}) :
    PIR.Process (Domain.effects model.toCarriers)
      (Values (Component model.Value) program.payload.entry.outputs × State model.toCarriers) :=
  match abi.read inputs program.payload.entry.inputs with
  | none => .halt .refused
  | some originalInputs => participant model program routing self originalInputs initial

/-- Successful ABI normalization is the construction of the actual original
participant at the entire decoded source input tuple. -/
theorem participantFromABI_found (model : Structured.DomainModel) (program : Structured.Program)
    (routing : Routing) (self : Nat) (abi : InputABI)
    (inputs : Domain.Environment model.toCarriers) (initial : State model.toCarriers)
    (originalInputs : Values (Component model.Value) program.payload.entry.inputs)
    (found : abi.read inputs program.payload.entry.inputs = some originalInputs) :
    participantFromABI model program routing self abi inputs initial =
      participant model program routing self originalInputs initial := by
  simp only [participantFromABI, found]

/-- Failed decoding never creates an absent source value or queries a service. -/
theorem participantFromABI_refused (model : Structured.DomainModel) (program : Structured.Program)
    (routing : Routing) (self : Nat) (abi : InputABI)
    (inputs : Domain.Environment model.toCarriers) (initial : State model.toCarriers)
    (missing : abi.read inputs program.payload.entry.inputs = none) :
    participantFromABI model program routing self abi inputs initial = .halt .refused := by
  simp only [participantFromABI, missing]

/-- Bad physical input sorts have a structural correspondence branch. The
artifact's initial checkpoint is retained with an explicit frame obligation. -/
def Simulation.malformedABI {model : Structured.DomainModel} {program : Structured.Program}
    (routing : Routing) (self : Nat) (abi : InputABI) (artifact : Participant)
    (inputs : Domain.Environment model.toCarriers) (initial : State model.toCarriers)
    (returns : (Values (Component model.Value) program.payload.entry.outputs × State model.toCarriers) →
      Domain.Result model.toCarriers → Prop)
    (live : PIR.Process (Domain.effects model.toCarriers)
      (Values (Component model.Value) program.payload.entry.outputs × State model.toCarriers) →
      Domain.Environment model.toCarriers → Prop)
    (declaration : artifact.inputs = abi.sorts)
    (malformed : Domain.sortsMatch abi.sorts inputs = false)
    (frame : live (.halt .refused) inputs) :
    Simulation returns live (participantFromABI model program routing self abi inputs initial)
      (Domain.participant model program routing.context artifact inputs) := by
  have missing : abi.read inputs program.payload.entry.inputs = none := by
    simp only [InputABI.read, malformed, Bool.false_eq_true, ↓reduceIte]
  rw [participantFromABI_refused model program routing self abi inputs initial missing]
  simp only [Domain.participant, declaration, malformed, Bool.false_eq_true, ↓reduceIte]
  exact .checkpoint inputs frame (.halt .refused)

end Zkc.Construction.Original

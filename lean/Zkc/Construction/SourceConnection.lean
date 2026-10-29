module

public import Zkc.Construction.ConnectionRouting
public import Zkc.Construction.ConnectionOutputs
public import Zkc.Construction.ConnectionInputFrames
public import Zkc.Construction.ConnectionRootInputs

@[expose] public section

/-! The semantic source-to-participant boundary, independently of its proof
method. The admitted source, selected role and routing are fixed parameters.
The source signature fixes the input ABI; a certificate cannot choose a weaker
input interpretation. Full nominal simulation and reached-source coverage are
separate obligations. Structural export admission and property proofs retain
their own owners. -/
set_option autoImplicit false
noncomputable section
namespace Zkc.Construction.SourceConnection
open Zkc.Source Zkc.Source.Structured Zkc.Construction ConnectionRoot ConnectionInputs

attribute [local implicit_reducible] CheckedProtocol.signature

/-- Source before routing, including exactly the selected physical ABI refusal. -/
def occurrence (program : Program) (role : Nat) (abi : Original.InputABI)
    (model : DomainModel) (physical : Domain.Environment model.toCarriers) :
    PIR.Process (Occurrence.signature model.toCarriers)
      (Values (Component model.Value) program.payload.entry.outputs) :=
  match abi.read physical program.payload.entry.inputs with
  | none => .halt .refused
  | some values => Occurrence.participant model program role values

def initial (routing : Original.Routing) (artifact : Participant)
    {carriers : Carriers} (physical : Domain.Environment carriers) : Original.State carriers :=
  ⟨[], inputHistory routing.context artifact.inputs physical⟩

def source (program : Program) (routing : Original.Routing) (role : Nat)
    (abi : Original.InputABI) (artifact : Participant)
    (model : DomainModel) (physical : Domain.Environment model.toCarriers) :=
  Original.participantFromABI model program routing role abi physical (initial routing artifact physical)

/-- Canonical source-input order and capability associations. The actual
artifact fixes its physical sorts; certificate evidence cannot hide a visible
source input or permute same-typed statement coordinates. -/
def canonicalABI (program : Program) (role : Nat) (artifact : Participant) :
    Except String Original.InputABI := do
  let signature := program.payload.entry.signature
  let locations ← ConnectionRootInputs.locations signature role
    (ConnectionRootInputs.serviceCapabilities signature.inputs)
  return ⟨artifact.inputs, locations⟩

/-- The proposition does not name a certificate, generator or proof route.
Its parameters are the fixed semantic boundary, not existential evidence fields.
Structural export admission must connect the selected role and profile to the
actual source; this proposition does not infer those selections from evidence. -/
structure Connected (program : Program) (routing : Original.Routing) (role : Nat)
    (abi : Original.InputABI) (artifact : Participant) : Prop where
  snapshot : routing.snapshot = program.snapshot
  roleValid : role < program.payload.entry.roles.length
  canonical : canonicalABI program role artifact = .ok abi
  coverage : ∀ (model : DomainModel) (physical : Domain.Environment model.toCarriers),
    Nonempty (Original.RouteCoverage routing [] [] (occurrence program role abi model physical))
  simulation : ∀ (model : DomainModel) (physical : Domain.Environment model.toCarriers),
    Nonempty (Original.Simulation
      (Original.CompleteReturns program.payload.entry.signature routing.context role artifact)
      (InputFrames abi program.payload.entry.inputs physical)
      (source program routing role abi artifact model physical)
      (Domain.participant model program routing.context artifact physical))

namespace Connected
variable {program : Program} {routing : Original.Routing} {role : Nat}
  {abi : Original.InputABI} {artifact : Participant}

/-- The source equation follows from the fixed snapshot; it is not another
instance obligation or a Boolean check that could replace either semantic field. -/
theorem source_eq_fold (connection : Connected program routing role abi artifact)
    (model : DomainModel) (physical : Domain.Environment model.toCarriers) :
    source program routing role abi artifact model physical =
      Original.fold routing (occurrence program role abi model physical)
        (initial routing artifact physical) := by
  have same : { routing with snapshot := program.snapshot } = routing := by
    rw [← connection.snapshot]
  unfold source Original.participantFromABI occurrence
  cases abi.read physical program.payload.entry.inputs with
  | none => rfl
  | some values => simp only [Original.participant, same]

/-- The canonical layout has only one possible input interpretation. -/
theorem inputABI_unique {other : Original.InputABI}
    (connection : Connected program routing role abi artifact)
    (second : Connected program routing role other artifact) : abi = other :=
  Except.ok.inj (connection.canonical.symm.trans second.canonical)

end Connected

end Zkc.Construction.SourceConnection

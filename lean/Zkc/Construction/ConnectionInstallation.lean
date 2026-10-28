module

public import Zkc.Construction.ConnectionLayout
public import Zkc.Construction.OriginalParticipant
public import Zkc.Construction.DomainCorrespondence

@[expose] public section

/-! Generic assembly of complete participant connections. The finite return
layout is indexed by the source signature, role, profile and actual artifact.
This consumer turns a body derivation into the existing complete root relation;
it is not an alternative admission check or an instance proof callback. -/
set_option autoImplicit false
namespace Zkc.Construction.ConnectionInstallation
open Zkc.Source Zkc.Source.Structured

/-- All static return checks for one actual artifact. Locations are proposals;
the source signature and selected profile determine the required values. -/
structure ReturnLayout (signature : ProtocolSignature) (context : Context)
    (role : Nat) (artifact : Participant) where
  locations : List Original.Location
  dataReferences : List Nat
  historyReference : Option Nat
  dataSorts : List ValueSort
  sourceSorts : Original.roleOutputSorts role signature.outputScopes signature.outputs = some dataSorts
  artifactSorts : artifact.outputs = Original.profileOutputSorts context dataSorts
  selectedData : Original.outputReferences role signature.outputScopes locations = some dataReferences
  selectedProfile : Original.profileReferences context dataReferences historyReference = some artifact.returned

/-- Recover the full source-location row from its scopes and the physical
return selectors. Hidden source outputs occupy absent logical positions. -/
def returnLocations (role : Nat) : List (List Nat) → List Nat → Option (List Original.Location)
  | [], [] => some []
  | [], _ :: _ => none
  | scope :: scopes, references =>
    if role ∈ scope then
      match references with
      | [] => none
      | reference :: rest => (Original.Location.data reference :: ·) <$> returnLocations role scopes rest
    else (Original.Location.absent :: ·) <$> returnLocations role scopes references

/-- Deterministic finite assembly of the return interface. All equations in
the returned record are kernel checked; the artifact supplies locations only,
and cannot alter the source-owned schema or the profile's transcript output. -/
def ReturnLayout.build (signature : ProtocolSignature) (context : Context)
    (role : Nat) (artifact : Participant) : Except String (ReturnLayout signature context role artifact) :=
  match sourceSorts : Original.roleOutputSorts role signature.outputScopes signature.outputs with
  | none => .error "connection-source-output-schema"
  | some dataSorts =>
    if artifactSorts : artifact.outputs = Original.profileOutputSorts context dataSorts then
      let (dataReferences, historyReference) := match context.profile with
        | .plain => (artifact.returned, none)
        | .fiatShamir _ => (artifact.returned.dropLast, artifact.returned.getLast?)
      match returnLocations role signature.outputScopes dataReferences with
      | none => .error "connection-output-arity"
      | some locations =>
        if selectedData : Original.outputReferences role signature.outputScopes locations = some dataReferences then
          if selectedProfile : Original.profileReferences context dataReferences historyReference = some artifact.returned then
            .ok ⟨locations, dataReferences, historyReference, dataSorts,
              sourceSorts, artifactSorts, selectedData, selectedProfile⟩
          else .error "connection-profile-return"
        else .error "connection-output-locations"
    else .error "connection-output-sorts"

/-- The body relation needed by the shared participant assembler. Every source
return is already masked by its own protocol boundary; the exact final history
and empty root stack are retained independently of acceptance. -/
def ReturnLayout.BodyReturns {carriers : Carriers} {signature : ProtocolSignature}
    {context : Context} {role : Nat} {artifact : Participant}
    (layout : ReturnLayout signature context role artifact)
    (captured : Domain.Environment carriers)
    (source : Values (Component carriers.Value) signature.outputs × Original.State carriers)
    (target : Domain.Environment carriers) : Prop :=
  Original.ValuesHolds target layout.locations source.1 ∧
    Original.HistoryLocation context layout.historyReference target source.2.history ∧
    source.2.frames = [] ∧ ArtifactBinding.Captures captured target

/-- Reading all selected data and the exact reached history yields the fixed
root return contract, including its nominal sorts and physical result arity. -/
theorem ReturnLayout.finish {carriers : Carriers} {signature : ProtocolSignature}
    {context : Context} {role : Nat} {artifact : Participant}
    (layout : ReturnLayout signature context role artifact)
    {captured : Domain.Environment carriers}
    {source : Values (Component carriers.Value) signature.outputs × Original.State carriers}
    {target : Domain.Environment carriers}
    (related : layout.BodyReturns captured source target) :
    ∃ output, Domain.read target artifact.returned = some output ∧
      Domain.sortsMatch artifact.outputs output = true ∧
      Original.CompleteReturns signature context role artifact source ⟨output, target⟩ := by
  obtain ⟨data, _, readData⟩ := Original.outputReferences_read source.1 layout.selectedData related.1
  have read := Original.profileReferences_read layout.selectedProfile readData related.2.1
  have complete := Original.CompleteReturns.of_layout
    (target := ⟨Domain.inputFrame context data source.2.history, target⟩) layout.sourceSorts layout.artifactSorts
    layout.selectedData layout.selectedProfile related.1 related.2.1 read related.2.2.1
  exact ⟨_, read, complete.sorts, complete⟩

/-- Install a checked body derivation on the actual constructed participant.
The view correspondence is the existing per-instruction checker theorem;
`body` is supplied by the generic connection engine, never by a new root law.
Full source input locations and final returns are checked through the common
ABI and layout consumers. Malformed inputs have their separate refusal rule. -/
@[no_expose] noncomputable def install
    (model : DomainModel) (program : Program) (routing : Original.Routing)
    (role : Nat) (artifact : Participant) (abi : Original.InputABI)
    (inputs : Values (Component model.Value) program.payload.entry.inputs)
    (physical : Domain.Environment model.toCarriers) (initial : Original.State model.toCarriers)
    (layout : ReturnLayout program.payload.entry.signature routing.context role artifact)
    (view : Domain.View.Block model.toCarriers)
    (inputSchema : artifact.inputs = abi.sorts)
    (correspondence : Domain.Correspondence.Block (model := model) (program := program)
      (context := routing.context) artifact.instructions view)
    (sorts : Domain.sortsMatch abi.sorts physical = true)
    (bounds : Original.LocationsBound physical.length abi.locations)
    (decoded : Original.ValuesHolds physical abi.locations inputs)
    (body : Original.Simulation (layout.BodyReturns physical)
      (fun _ frame => ArtifactBinding.Captures physical frame)
      (Original.participant model program routing role inputs initial) (view physical)) :
    Original.Simulation
      (Original.CompleteReturns program.payload.entry.signature routing.context role artifact)
      (Original.InputLive abi inputs physical)
      (Original.participant model program routing role inputs initial)
      (Domain.participant model program routing.context artifact physical) := by
  rw [Domain.Correspondence.participant artifact correspondence, inputSchema]
  exact Original.Simulation.participant abi inputs physical artifact.outputs artifact.returned view
    _ _ _ sorts bounds decoded body (fun _ _ returned => layout.finish returned)

end Zkc.Construction.ConnectionInstallation

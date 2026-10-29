module

public import Zkc.Construction.ConnectionInstallation
public import Zkc.Construction.ConnectionCertificate
public import Zkc.Construction.ConnectionInputSchema
public import Zkc.Source.Structured.DomainProtocolLinking

@[expose] public section

/-! Install finite body certificates on their actual admitted source root.
Source masks, captured tables, ABI readback and the selected return profile are
assembled here. Protocol instances provide finite certificates and the existing
constructed-view correspondence; they do not prove a source-root equation. -/
set_option autoImplicit false
namespace Zkc.Construction.ConnectionRoot
open Zkc.Source Zkc.Source.Structured NormalForm ConnectionFrame
open ConnectionInstallation

attribute [local implicit_reducible] CheckedProtocol.signature

private theorem participant_body (model : DomainModel) (program : Program)
    (routing : Original.Routing) (role : Nat)
    (snapshot : routing.snapshot = program.snapshot)
    (inputs : Values (Component model.Value) program.payload.entry.inputs)
    (masked : maskValues role program.payload.entry.inputScopes inputs = inputs)
    (state : Original.State model.toCarriers) :
    Original.participant model program routing role inputs state =
      (Original.fold routing (program.payload.entry.body.denote
        (participantMeaningWithOn model (.silent _) Occurrence.actions
          (Occurrence.helpers model program.payload) role (Occurrence.table model program.payload)
          {} Occurrence.iterations) inputs.get) state).bind fun result =>
            .done (maskValues role program.payload.entry.outputScopes result.1, result.2) := by
  have same : { routing with snapshot := program.snapshot } = routing := by
    rw [← snapshot]
  rw [Original.participant, same, Occurrence.participant,
    Occurrence.invoke_body model program.payload _ program.payload.entry_mem]
  simp only [CheckedProtocol.denoteWithOn, ProtocolContext.mapScopes_root]
  rw [masked, Original.fold_bind]
  rfl

private theorem historyLocation {context : Context} {data returned : List Nat}
    {history : Option Nat} {carriers : Carriers}
    {frame : Domain.Environment carriers} {reached : Domain.History carriers}
    (read : match history with
      | none => True
      | some reference => frame[reference]? = some (.transcript context.suite reached))
    (profile : Original.profileReferences context data history = some returned) :
    Original.HistoryLocation context history frame reached := by
  cases selected : context.profile with
  | plain =>
    cases history with
    | none => simp only [Original.HistoryLocation, selected]
    | some reference => simp [Original.profileReferences, selected] at profile
  | fiatShamir replacement =>
    cases history with
    | none => simp [Original.profileReferences, selected] at profile
    | some reference =>
      simpa only [Original.HistoryLocation, selected, Context.suite, Context.replacement?,
        Option.map_some, Option.getD_some] using read

/-- A source-body alignment yields the complete actual-participant connection.
The actual program fixes the source, helper table and protocol table. Masks and
the full return row come from its signature; arbitrary replies and stops remain
inside the common certificate theorem. -/
@[no_expose] noncomputable def fromCertificate
    (program : Program) (routing : Original.Routing) (role : Nat)
    (artifact : Participant) (abi : Original.InputABI)
    (snapshot : routing.snapshot = program.snapshot)
    (pattern : InputPattern program.payload.entry.inputs)
    (inputLayout : Layout pattern.scope)
    (output : ReturnLayout program.payload.entry.signature routing.context role artifact)
    (target : ConnectionCertificate.Block)
    (library : ConnectionLibrary.Bundle program.payload)
    (certificate : ConnectionCertificate.Certificate routing {} program.payload.definitions
      role program.payload.entry.roles.length program.payload.entry pattern
      output.locations output.historyReference [] inputLayout target
      library.keys (.selected program.payload rfl library.library))
    (distinct : RosterDistinct {} role program.payload.entry.roles.length)
    (visibility : inputScopes role program.payload.entry.inputScopes abi.locations = true)
    (inputSchema : artifact.inputs = abi.sorts)
    (model : DomainModel)
    (correspondence : Domain.Correspondence.Block (model := model) (program := program)
      (context := routing.context) artifact.instructions (target model))
    (binders : Binders model pattern.scope)
    (physical : Domain.Environment model.toCarriers) (initial : Original.State model.toCarriers)
    (stack : initial.frames = [])
    (sorts : Domain.sortsMatch abi.sorts physical = true)
    (bounds : Original.LocationsBound physical.length abi.locations)
    (decoded : Original.ValuesHolds physical abi.locations (pattern.environment model binders))
    (related : Holds model binders initial.history inputLayout physical) :
    Original.Simulation
      (Original.CompleteReturns program.payload.entry.signature routing.context role artifact)
      (Original.InputLive abi (pattern.environment model binders) physical)
      (Original.participant model program routing role (pattern.environment model binders) initial)
      (Domain.participant model program routing.context artifact physical) := by
  have body := certificate.selectedSimulation distinct model initial binders stack abi physical
    sorts bounds decoded physical related (by simp [ArtifactBinding.Captures])
  apply ConnectionInstallation.install model program routing role artifact abi
    (pattern.environment model binders) physical initial output (target model)
    inputSchema correspondence sorts bounds decoded
  rw [participant_body model program routing role snapshot _
    (inputScopes_mask _ visibility decoded) initial]
  have assembled := body.bind
    (returnRelation := output.BodyReturns physical)
    (nextLive := fun _ frame => ArtifactBinding.Captures physical frame)
    (sourceNext := fun result => .done
      (maskValues role program.payload.entry.outputScopes result.1, result.2))
    (targetNext := PIR.Process.done)
    (fun _ _ live => live.2.1) (by
      intro source frame returned
      exact .done ⟨returned.1, historyLocation returned.2.2.1 output.selectedProfile,
        returned.2.1.trans stack, returned.2.2.2⟩)
  simpa only [PIR.Process.bind_done, id_eq] using assembled

end Zkc.Construction.ConnectionRoot

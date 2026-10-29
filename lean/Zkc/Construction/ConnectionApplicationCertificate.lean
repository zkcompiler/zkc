module

public import Zkc.Construction.ConnectionCertificate
public import Zkc.Construction.ConnectionSubstitution

@[expose] public section

/-! Placement of a reusable checked source template at an actual linked call.
An instance contains a finite typed argument map and a structural alignment of
the instantiated body. The template body, full declaration signature, role,
pins and helper tables are shared by reference. No process equation or semantic
callback is an instance field. -/
set_option autoImplicit false
namespace Zkc.Construction.ConnectionApplications
open Zkc.Source Zkc.Source.Structured NormalForm ConnectionFrame
open ConnectionLibrary ConnectionCertificate

/-- The whole nominal output tuple, exact enclosing stack, reached transcript
and retained caller frame at an actual application boundary. -/
def Returns {model : DomainModel} {types : List Ty} (history : Option Nat) (suite : String)
    (outputs : List Original.Location) (frames : Original.Frames)
    (captured : Domain.Environment model.toCarriers)
    (source : Values (Component model.Value) types × Original.State model.toCarriers)
    (target : Domain.Environment model.toCarriers) : Prop :=
  Original.ValuesHolds target outputs source.1 ∧ source.2.frames = frames ∧
    (match history with
     | none => True
     | some reference => target[reference]? = some (.transcript suite source.2.history)) ∧
    ArtifactBinding.Captures captured target

/-- All placement data are finite syntax. Ordered outer-frame terms remain in
the caller scope, so the same body supports arbitrary surrounding repeats. -/
structure Certificate {payload : UnitPayload} {callees : List CalleeKey}
    (template : SourceTemplate payload callees) (routing : Original.Routing)
    (context : ProtocolContext) {scope : Scope}
    (arguments : Values (Argument [] scope) template.pattern.scope)
    (outputs : List Original.Location) (history : Option Nat)
    (frames : ScopedFrames scope) (layout : Layout scope) (target : ConnectionCertificate.Block) where
  distinct : RosterDistinct context template.role template.source.roles.length
  alignment : Derivation routing context payload.definitions callees template.source.outputs
    template.role template.source.outputScopes outputs history frames layout
    (ConnectionSubstitution.form template.form (fun binder => entryAt arguments binder)) target

/-- Actual full-table application transport for every model, caller binder,
hidden input component, enclosing frame, checkpoint and service reply. The
normalization equation is taken once from the shared source template. -/
@[no_expose] noncomputable def Certificate.simulation
    {payload : UnitPayload} {callees : List CalleeKey} {template : SourceTemplate payload callees}
    {routing : Original.Routing} {context : ProtocolContext} {scope : Scope}
    {arguments : Values (Argument [] scope) template.pattern.scope}
    {outputs : List Original.Location} {history : Option Nat}
    {frames : ScopedFrames scope} {layout : Layout scope} {target : ConnectionCertificate.Block}
    (certificate : Certificate template routing context arguments outputs history frames layout target)
    (library : Library payload callees) (model : DomainModel)
    (binders : Binders model scope)
    (others : Values (Component model.Value) template.pattern.absentTypes)
    (state : Original.State model.toCarriers) (stack : state.frames = frames.eval model binders)
    (captured environment : Domain.Environment model.toCarriers)
    (related : Holds model binders state.history layout environment)
    (retained : ArtifactBinding.Captures captured environment) :
    Original.Simulation (Returns history routing.context.suite outputs state.frames captured)
      (fun _ frame => ArtifactBinding.Captures captured frame)
      (Original.fold routing
        (invokeProtocol (Occurrence.table model payload) template.source.signature context
          (context.roles template.role)
          (template.pattern.fill model (Arguments.eval (LawResults.empty model) arguments binders) others)) state)
      (target model environment) := by
  let calleeBinders := Arguments.eval (LawResults.empty model) arguments binders
  have inputMask : maskValues (context.roles template.role) (context.mapScopes template.source.inputScopes)
      (template.pattern.fill model calleeBinders others) = template.pattern.environment model calleeBinders :=
    (mask_context certificate.distinct _ template.inputScopes _).trans
      (mask_fill model _ _ _ template.visible calleeBinders others)
  have normalized := normalize_checkedProtocol_soundOn Occurrence.actions Occurrence.iterations
    (Occurrence.helpers model payload) (Occurrence.table model payload) context template.source
    {strict := true, names := true, kept := payload.definitions.map CheckedDefinition.helper, callees := callees}
    template.role template.pattern template.form template.normalized template.matched certificate.distinct
    (LawResults.empty model) (library.processes model) _ calleeBinders inputMask
    (LawsHold.empty _ _) (library.holds model _)
  have instantiated := ConnectionSubstitution.form_denote calleeBinders binders
    (fun binder => entryAt arguments binder) (ConnectionSubstitution.arguments_related arguments binders)
    Occurrence.actions (Occurrence.helpers model payload) context
    (runsAtOn model Occurrence.actions Occurrence.iterations (Occurrence.helpers model payload)
      (Occurrence.table model payload) context template.role) (library.processes model) template.form
  have aligned := Derivation.unselectedLibrarySimulation certificate.alignment library model state captured binders stack
    environment related retained
  apply Original.Simulation.linkedApplication model payload routing template.source
    (List.getElem_mem _) context (context.roles template.role) _ state
  rw [normalized, ← instantiated, Original.fold_bind]
  simp only [Original.fold_done]
  have assembled := aligned.bind
    (returnRelation := Returns history routing.context.suite outputs state.frames captured)
    (nextLive := fun _ frame => ArtifactBinding.Captures captured frame)
    (sourceNext := fun source => .done
      (maskValues (context.roles template.role) (context.mapScopes template.source.outputScopes) source.1, source.2))
    (targetNext := PIR.Process.done)
    (fun _ _ kept => kept) (by
      intro source frame returned
      refine .done ⟨?_, returned.2.1, returned.2.2.1, returned.2.2.2⟩
      rw [mask_context certificate.distinct _ template.outputScopes]
      exact returned.1)
  rw [PIR.Process.bind_done] at assembled
  exact assembled

end Zkc.Construction.ConnectionApplications

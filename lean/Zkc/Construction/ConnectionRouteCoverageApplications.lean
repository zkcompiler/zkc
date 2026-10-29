module

public import Zkc.Construction.ConnectionRouteCoverage
public import Zkc.Construction.ConnectionApplicationCertificate

@[expose] public section

/-! Reusable source coverage at a linked application placement. The exact
source template, declaration, role, helper tables and nominal input row are
shared with the finite application certificate and its simulation theorem. -/
set_option autoImplicit false
namespace Zkc.Construction.ConnectionApplications
open Zkc.Source Zkc.Source.Structured NormalForm ConnectionFrame
open ConnectionLibrary ConnectionCertificate InputVisibility

/-- Every reached effect of the actual linked application is covered, for all
hidden logical inputs, enclosing coordinates, helper stops and typed replies.
The proof refers to the generic alignment theorem, not a protocol proof. -/
@[no_expose] noncomputable def Certificate.routeCoverage
    {payload : UnitPayload} {callees : List CalleeKey} {template : SourceTemplate payload callees}
    {routing : Original.Routing} {context : ProtocolContext} {scope : Scope}
    {arguments : Values (Argument [] scope) template.pattern.scope}
    {outputs : List Original.Location} {history : Option Nat}
    {frames : ScopedFrames scope} {layout : Layout scope} {target : ConnectionCertificate.Block}
    (certificate : Certificate template routing context arguments outputs history frames layout target)
    (library : Library payload callees) (model : DomainModel)
    (binders : Binders model scope)
    (others : Values (Component model.Value) template.pattern.absentTypes)
    (reachedHistory : Domain.History model.toCarriers) (environment : Domain.Environment model.toCarriers)
    (related : Holds model binders reachedHistory layout environment) :
    Original.RouteCoverage routing (frames.eval model binders) (frames.eval model binders)
      (invokeProtocol (Occurrence.table model payload) template.source.signature context
        (context.roles template.role)
        (template.pattern.fill model (Arguments.eval (LawResults.empty model) arguments binders) others)) := by
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
  rw [Occurrence.invoke_body model payload template.source (List.getElem_mem _), normalized, ← instantiated]
  exact (certificate.alignment.covered model (Occurrence.helpers model payload) (fun _ => rfl)
    (Occurrence.table model payload) (library.processes model) (library.holds model)
    binders reachedHistory environment related).coverage.bind fun _ => .done _ _

end Zkc.Construction.ConnectionApplications

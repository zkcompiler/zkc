module

public import Zkc.Source.Structured.DomainParticipant
public import Zkc.Source.Structured.DomainInterpretation

@[expose] public section

/-! Nominal participant semantics is natural in the effect interpreter,
including optional iteration observations. This is the erasure boundary for
source occurrence views, not a compiler-correctness assumption. -/
set_option autoImplicit false
namespace Zkc.Source.Structured

variable {model : DomainModel}

theorem denoteRepeatOn_interpret {carriers : Carriers} {I J : PIR.Signature}
    (operations : PIR.OperationInterpretation I J)
    {left : IterationObservations I} {right : IterationObservations J}
    (iterations : IterationObservations.Interprets operations left right)
    (spec : RepeatSpec) (context : ProtocolContext) (self : Nat) (count : Option Nat)
    (state : Values (Component carriers.Value) spec.state)
    (captures : Values (Component carriers.Value) spec.captures)
    (body : RegionFunction (Component carriers.Value) I
      (.index :: (spec.state ++ spec.captures), spec.state)) (site : String) :
    (denoteRepeatOn spec context self count state captures body left site).interpret operations =
      denoteRepeatOn spec context self count state captures
        (fun args => (body args).interpret operations) right site := by
  unfold denoteRepeatOn
  split
  · cases count with
    | none => rfl
    | some count =>
      dsimp only
      split
      · simp only [Finite.interpret_execute, Repeat.stepOn, PIR.Process.interpret_bind,
          IterationObservations.within_interpret operations iterations, PIR.Process.interpret]
      · rfl
  · rfl

/-- Interpretations preserve the same root coordinates and every child context. -/
theorem protocolOperationWithOn_interpret {I J : PIR.Signature}
    (operations : PIR.OperationInterpretation I J)
    {leftSites : SiteObservations I} {rightSites : SiteObservations J}
    (sites : SiteObservations.Interprets operations leftSites rightSites)
    {leftActions : PIR.OperationInterpretation (participantInterfaceOn model.toCarriers) I}
    {rightActions : PIR.OperationInterpretation (participantInterfaceOn model.toCarriers) J}
    (actions : ∀ action, (leftActions action).interpret operations = rightActions action)
    {left : Evaluation.ComponentTablesOn model.toCarriers I} {right : Evaluation.ComponentTablesOn model.toCarriers J}
    (tables : Evaluation.ComponentTablesOn.Interprets operations left right)
    (self : Nat) (op : ProtocolOp) (args : Values (Component model.Value) op.arguments)
    (callbacks : Values (RegionFunction (Component model.Value) I) op.regions)
    {leftProtocols : ProtocolTable model.Value I}
    {rightProtocols : ProtocolTable model.Value J}
    (protocols : ProtocolTable.Interprets operations leftProtocols rightProtocols)
    (context : ProtocolContext)
    {leftIterations : IterationObservations I} {rightIterations : IterationObservations J}
    (iterations : IterationObservations.Interprets operations leftIterations rightIterations) :
    (protocolOperationWithOn model leftSites leftActions left self op args callbacks leftProtocols context leftIterations).interpret operations =
      protocolOperationWithOn model rightSites rightActions right self op args
        (RegionFunctions.translate (dialect := protocolDialect) operations callbacks) rightProtocols context rightIterations := by
  have actionProcess {A : Type} (process : PIR.Process (participantInterfaceOn model.toCarriers) A) :
      (process.interpret leftActions).interpret operations = process.interpret rightActions :=
    PIR.Process.interpret_interchange leftActions operations rightActions actions process
  cases op with
  | «repeat» spec site =>
    cases args with
    | cons count values =>
      cases callbacks with
      | cons body rest =>
        cases rest
        exact denoteRepeatOn_interpret operations iterations spec context self count
          (Values.split spec.state values).1 (Values.split spec.state values).2 body site
  | calculate op allowed =>
    cases callbacks
    have translated := Evaluation.componentOperationOn_interpret operations sites tables op args
      (op.calculationRegions allowed)
    rw [Op.calculationRegions_translate] at translated
    exact translated
  | localCall helper kind owner site =>
    cases callbacks
    exact Participant.owned_interpret operations self (context.roles owner) _ _ (tables.closed helper) args
  | guard =>
    cases callbacks
    cases args with
    | cons condition rest =>
      cases rest
      change (((Participant.guard (services := services) (Value := model.Value) self _ condition).interpret
        leftActions).bind (fun _ => .done (Values.nil : Values (Component model.Value) []))).interpret operations =
        ((Participant.guard (services := services) (Value := model.Value) self _ condition).interpret
          rightActions).bind (fun _ => .done Values.nil)
      simp only [PIR.Process.interpret_bind, actionProcess, PIR.Process.interpret]
  | exchange ty sender receiver site =>
    cases callbacks
    cases args with
    | cons value rest =>
      cases rest
      change (((Participant.exchange (services := services) self (context.roles sender) (context.roles receiver)
        (qualifyProtocolSite context.applicationPrefix site) value).interpret
        leftActions).bind (fun result => .done
          (Values.cons result Values.nil : Values (Component model.Value) [ty]))).interpret operations =
        ((Participant.exchange (services := services) self (context.roles sender) (context.roles receiver)
          (qualifyProtocolSite context.applicationPrefix site) value).interpret
          rightActions).bind (fun result => .done (Values.cons result Values.nil))
      simp only [PIR.Process.interpret_bind, actionProcess, PIR.Process.interpret]
  | restrict => cases callbacks; cases args with
    | cons value rest => cases rest; rfl
  | draw =>
    cases callbacks
    simp only [protocolOperationWithOn, PIR.Process.interpret_bind, actionProcess, PIR.Process.interpret]
  | statement => cases callbacks; rfl
  | mark site =>
    cases callbacks
    cases args
    change ((leftSites.mark (qualifyProtocolSite context.applicationPrefix site)).bind
      (fun _ => .done (Values.nil : Values (Component model.Value) []))).interpret operations =
      (rightSites.mark (qualifyProtocolSite context.applicationPrefix site)).bind (fun _ => .done Values.nil)
    simp only [PIR.Process.interpret_bind, sites (qualifyProtocolSite context.applicationPrefix site), PIR.Process.interpret]
  | protocolApply signature roles site =>
    cases callbacks
    change (if (context.enter site roles).contains signature self then
      invokeProtocol leftProtocols signature (context.enter site roles) self args
      else .done (Values.absent model.Value signature.outputs)).interpret operations =
      if (context.enter site roles).contains signature self then
        invokeProtocol rightProtocols signature (context.enter site roles) self args
      else .done (Values.absent model.Value signature.outputs)
    split
    · exact protocols signature _ self args
    · rfl

def participantMeaningTranslationOn {I J : PIR.Signature}
    (operations : PIR.OperationInterpretation I J)
    {leftSites : SiteObservations I} {rightSites : SiteObservations J}
    (sites : SiteObservations.Interprets operations leftSites rightSites)
    {leftActions : PIR.OperationInterpretation (participantInterfaceOn model.toCarriers) I}
    {rightActions : PIR.OperationInterpretation (participantInterfaceOn model.toCarriers) J}
    (actions : ∀ action, (leftActions action).interpret operations = rightActions action)
    {left : Evaluation.ComponentTablesOn model.toCarriers I} {right : Evaluation.ComponentTablesOn model.toCarriers J}
    (tables : Evaluation.ComponentTablesOn.Interprets operations left right) (self : Nat)
    {leftProtocols : ProtocolTable model.Value I}
    {rightProtocols : ProtocolTable model.Value J}
    (protocols : ProtocolTable.Interprets operations leftProtocols rightProtocols)
    (context : ProtocolContext)
    {leftIterations : IterationObservations I} {rightIterations : IterationObservations J}
    (iterations : IterationObservations.Interprets operations leftIterations rightIterations) :
    (participantMeaningWithOn model leftSites leftActions left self leftProtocols context leftIterations).Translation operations where
  operation op args callbacks :=
    protocolOperationWithOn model rightSites rightActions right self op args callbacks rightProtocols context rightIterations
  commutes op args callbacks :=
    (protocolOperationWithOn_interpret operations sites actions tables self op args callbacks protocols context iterations).symm

theorem participant_denoteOn_interpret {I J : PIR.Signature}
    (operations : PIR.OperationInterpretation I J)
    {leftSites : SiteObservations I} {rightSites : SiteObservations J}
    (sites : SiteObservations.Interprets operations leftSites rightSites)
    {leftActions : PIR.OperationInterpretation (participantInterfaceOn model.toCarriers) I}
    {rightActions : PIR.OperationInterpretation (participantInterfaceOn model.toCarriers) J}
    (actions : ∀ action, (leftActions action).interpret operations = rightActions action)
    {left : Evaluation.ComponentTablesOn model.toCarriers I} {right : Evaluation.ComponentTablesOn model.toCarriers J}
    (tables : Evaluation.ComponentTablesOn.Interprets operations left right) (self : Nat)
    {Γ out : List Ty} (region : Region protocolDialect Γ out)
    (env : Environment (Component model.Value) Γ)
    {leftProtocols : ProtocolTable model.Value I}
    {rightProtocols : ProtocolTable model.Value J}
    (protocols : ProtocolTable.Interprets operations leftProtocols rightProtocols)
    (context : ProtocolContext)
    {leftIterations : IterationObservations I} {rightIterations : IterationObservations J}
    (iterations : IterationObservations.Interprets operations leftIterations rightIterations) :
    (region.denote (participantMeaningWithOn model leftSites leftActions left self leftProtocols context leftIterations) env).interpret operations =
      region.denote (participantMeaningWithOn model rightSites rightActions right self rightProtocols context rightIterations) env :=
  (region.denote_translate _ operations
    (participantMeaningTranslationOn operations sites actions tables self protocols context iterations) env).symm


theorem CheckedProtocol.denoteWithOn_interpret {I J : PIR.Signature}
    (operations : PIR.OperationInterpretation I J)
    {leftSites : SiteObservations I} {rightSites : SiteObservations J}
    (sites : SiteObservations.Interprets operations leftSites rightSites)
    {leftActions : PIR.OperationInterpretation (participantInterfaceOn model.toCarriers) I}
    {rightActions : PIR.OperationInterpretation (participantInterfaceOn model.toCarriers) J}
    (actions : ∀ action, (leftActions action).interpret operations = rightActions action)
    {left : Evaluation.ComponentTablesOn model.toCarriers I} {right : Evaluation.ComponentTablesOn model.toCarriers J}
    (tables : Evaluation.ComponentTablesOn.Interprets operations left right)
    {leftProtocols : ProtocolTable model.Value I}
    {rightProtocols : ProtocolTable model.Value J}
    (protocols : ProtocolTable.Interprets operations leftProtocols rightProtocols)
    {leftIterations : IterationObservations I} {rightIterations : IterationObservations J}
    (iterations : IterationObservations.Interprets operations leftIterations rightIterations)
    (definition : CheckedProtocol) (context : ProtocolContext) (self : Nat)
    (args : Values (Component model.Value) definition.inputs) :
    (definition.denoteWithOn model leftSites leftActions left leftProtocols leftIterations context self args).interpret operations =
      definition.denoteWithOn model rightSites rightActions right rightProtocols rightIterations context self args := by
  simp only [denoteWithOn, PIR.Process.interpret_bind, PIR.Process.interpret]
  dsimp only [CheckedProtocol.signature]
  rw [participant_denoteOn_interpret operations sites actions tables self _ _ protocols context iterations]

theorem extendProtocolTableOn_interpret {I J : PIR.Signature}
    (operations : PIR.OperationInterpretation I J)
    {leftSites : SiteObservations I} {rightSites : SiteObservations J}
    (sites : SiteObservations.Interprets operations leftSites rightSites)
    {leftActions : PIR.OperationInterpretation (participantInterfaceOn model.toCarriers) I}
    {rightActions : PIR.OperationInterpretation (participantInterfaceOn model.toCarriers) J}
    (actions : ∀ action, (leftActions action).interpret operations = rightActions action)
    {left : Evaluation.ComponentTablesOn model.toCarriers I} {right : Evaluation.ComponentTablesOn model.toCarriers J}
    (tables : Evaluation.ComponentTablesOn.Interprets operations left right)
    {leftProtocols : ProtocolTable model.Value I}
    {rightProtocols : ProtocolTable model.Value J}
    (protocols : ProtocolTable.Interprets operations leftProtocols rightProtocols)
    {leftIterations : IterationObservations I} {rightIterations : IterationObservations J}
    (iterations : IterationObservations.Interprets operations leftIterations rightIterations)
    (definition : CheckedProtocol) :
    ProtocolTable.Interprets operations
      (extendProtocolTableOn model leftSites leftActions left leftProtocols definition leftIterations)
      (extendProtocolTableOn model rightSites rightActions right rightProtocols definition rightIterations) :=
  protocols.cons definition.signature _ _
    (definition.denoteWithOn_interpret operations sites actions tables protocols iterations)

theorem ProtocolTable.foldOn_interpret {I J : PIR.Signature}
    (operations : PIR.OperationInterpretation I J)
    {leftSites : SiteObservations I} {rightSites : SiteObservations J}
    (sites : SiteObservations.Interprets operations leftSites rightSites)
    {leftActions : PIR.OperationInterpretation (participantInterfaceOn model.toCarriers) I}
    {rightActions : PIR.OperationInterpretation (participantInterfaceOn model.toCarriers) J}
    (actions : ∀ action, (leftActions action).interpret operations = rightActions action)
    {left : Evaluation.ComponentTablesOn model.toCarriers I} {right : Evaluation.ComponentTablesOn model.toCarriers J}
    (tables : Evaluation.ComponentTablesOn.Interprets operations left right)
    {leftProtocols : ProtocolTable model.Value I}
    {rightProtocols : ProtocolTable model.Value J}
    (protocols : ProtocolTable.Interprets operations leftProtocols rightProtocols)
    {leftIterations : IterationObservations I} {rightIterations : IterationObservations J}
    (iterations : IterationObservations.Interprets operations leftIterations rightIterations)
    (definitions : List CheckedProtocol) :
    ProtocolTable.Interprets operations
      (definitions.foldl (fun captured definition => extendProtocolTableOn model leftSites leftActions left captured definition leftIterations) leftProtocols)
      (definitions.foldl (fun captured definition => extendProtocolTableOn model rightSites rightActions right captured definition rightIterations) rightProtocols) := by
  induction definitions generalizing leftProtocols rightProtocols with
  | nil => exact protocols
  | cons definition rest ih =>
    exact ih (extendProtocolTableOn_interpret operations sites actions tables protocols iterations definition)

/-- Forgetting source-site observations yields the same nominal plain table. -/
theorem UnitPayload.protocolTableOn_forgetSitesOn (payload : UnitPayload) :
    ProtocolTable.Interprets (forgetSitesOn (carriers := model.toCarriers))
      (payload.protocolTableOn model) (payload.plainProtocolTableOn model) :=
  ProtocolTable.foldOn_interpret forgetSitesOn observedSitesOn_forgetSitesOn
    observeActionOn_forgetSitesOn
    (Evaluation.ComponentTablesOn.fold_interpret forgetSitesOn observedSitesOn_forgetSitesOn
      (.empty _) payload.definitions) (.empty _) (IterationObservations.silent_interpret _) payload.protocols

/-- An equality of the complete participant process, including all failures. -/
theorem Program.participantOn_eq_plain (program : Program) (self : Nat)
    (inputs : Values (Component model.Value) program.payload.entry.inputs) :
    program.participantOn model self inputs =
      invokeProtocol (program.payload.plainProtocolTableOn model)
        program.payload.entry.signature {} self inputs :=
  program.payload.protocolTableOn_forgetSitesOn program.payload.entry.signature {} self inputs

end Zkc.Source.Structured

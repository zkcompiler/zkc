module

public import Zkc.Source.Structured.Interpretation
public import Zkc.Source.Participant
public import Zkc.Source.Structured.ProtocolTable

@[expose] public section

namespace Zkc.Source.Participant

/-- Interpretation preserves ownership, missing inputs, and zero-result stops. -/
theorem owned_interpret {Role Ty : Type} [DecidableEq Role] {Value : Ty → Type}
    {I J : PIR.Signature} {inputs outputs : List Ty}
    (operations : PIR.OperationInterpretation I J) (self owner : Role)
    (left : Values Value inputs → PIR.Proc I (Values Value outputs))
    (right : Values Value inputs → PIR.Proc J (Values Value outputs))
    (work : ∀ args, (left args).interpret operations = right args)
    (args : Values (Component Value) inputs) :
    (owned self owner left args).interpret operations = owned self owner right args := by
  unfold owned
  split
  · cases RoleFamily.sequence args with
    | none => rfl
    | some values => simp only [PIR.Proc.interpret_bind, work, PIR.Proc.interpret]
  · rfl

end Zkc.Source.Participant

namespace Zkc.Source.Structured

/-- Draw uses the actual service operand. No sampling distribution is part of
this signature, and admission checks its exact nominal field/contract. -/
def services : Participant.Services Ty where
  Op := String
  arguments field := [.service ("random." ++ field ++ "/0")]
  result field := .field field

abbrev participantInterface (F G : Type) : PIR.Signature :=
  Participant.interface Nat Ty services (assignment F G)

inductive ObservedAction (F G : Type) where
  | mark (site : String)
  | action (value : (participantInterface F G).Op)

abbrev observedInterface (F G : Type) : PIR.Signature where
  Op := ObservedAction F G
  Reply
    | .mark _ => Unit
    | .action action => (participantInterface F G).Reply action

/-- Site observations are internal and do not acquire provider replies. -/
def observeAction {F G : Type} : PIR.OperationInterpretation
    (participantInterface F G) (observedInterface F G) :=
  fun action => .call (.action action) .done

/-- The logical participant process explicitly forgets only site observations. -/
def forgetSites {F G : Type} : PIR.OperationInterpretation
    (observedInterface F G) (participantInterface F G)
  | .mark _ => .done ()
  | .action action => .call action .done

def observedSites (F G : Type) : SiteObservations (observedInterface F G) where
  mark site := .call (.mark site) .done

/-- Protocol actions retain their actual provider replies in the plain view. -/
def participantActions (F G : Type) : PIR.OperationInterpretation
    (participantInterface F G) (participantInterface F G) := fun action => .call action .done

/-- Calculation callbacks are empty by construction, independently of effects. -/
def Op.calculationRegions {Value : Ty → Type} {I : PIR.Signature}
    (op : Op) (allowed : op.isCalculation = true) : Values (RegionFunction Value I) op.regions := by
  cases op <;> simp_all [Op.isCalculation, Op.regions] <;> exact .nil

theorem Op.calculationRegions_translate {Value : Ty → Type} {I J : PIR.Signature}
    (operations : PIR.OperationInterpretation I J) (op : Op) (allowed : op.isCalculation = true) :
    RegionFunctions.translate (dialect := dialect) operations (op.calculationRegions (Value := Value) allowed) =
      op.calculationRegions allowed := by
  cases op <;> try rfl
  all_goals cases allowed

theorem observedSites_forgetSites {F G : Type} :
    SiteObservations.Interprets forgetSites (observedSites F G) (.silent (participantInterface F G)) := by
  intro site
  rfl

theorem observeAction_forgetSites {F G : Type} (action : (participantInterface F G).Op) :
    (observeAction action).interpret forgetSites = participantActions F G action := by
  simp only [observeAction, forgetSites, participantActions, PIR.Proc.interpret,
    PIR.Proc.bind_done]

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

abbrev OpenTables (F G : Type) := Evaluation.ComponentTables F G (observedInterface F G)

def protocolOperationWith {I : PIR.Signature} (observations : SiteObservations I)
    (actions : PIR.OperationInterpretation (participantInterface F G) I)
    (tables : Evaluation.ComponentTables F G I) (self : Nat)
    (op : ProtocolOp) (args : Values (Component (assignment F G)) op.arguments)
    (_callbacks : Values (RegionFunction (Component (assignment F G)) I) op.regions)
    (protocols : ProtocolTable (assignment F G) I := [])
    (context : ProtocolContext := {}) :
    PIR.Proc I (Values (Component (assignment F G)) op.results) :=
  match op, args with
  | .calculate op allowed, args =>
    Evaluation.componentOperation observations tables op args (op.calculationRegions allowed)
  | .localCall helper _ owner _, args =>
    Participant.owned self (context.roles owner) (invoke tables.closed helper) args
  | .guard owner _, .cons condition .nil =>
    ((Participant.guard (services := services) (Value := assignment F G) self (context.roles owner)
      condition).interpret actions).bind fun _ => .done .nil
  | .exchange _ sender receiver site, .cons value .nil =>
    ((Participant.exchange (services := services) self (context.roles sender) (context.roles receiver)
      (qualifyProtocolSite context.applicationPrefix site) value).interpret
      actions).bind fun result => .done (.cons result .nil)
  | .restrict _ roles, .cons value .nil =>
    .done (.cons (Participant.restrict ((roles.map context.roles).contains self) value) .nil)
  | .draw owner field site, args =>
    ((Participant.query (services := services) self (context.roles owner)
      (qualifyProtocolSite context.applicationPrefix site) field args).interpret
      actions).bind fun result => .done (.cons result .nil)
  | .statement .., _ => .done .nil
  | .mark site, .nil =>
    (observations.mark (qualifyProtocolSite context.applicationPrefix site)).bind fun _ => .done .nil
  | .protocolApply signature roles site, args =>
    let child := context.enter site roles
    if child.contains signature self then invokeProtocol protocols signature child self args
    else .done (Values.absent (assignment F G) signature.outputs)

abbrev participantMeaningWith {I : PIR.Signature} (observations : SiteObservations I)
    (actions : PIR.OperationInterpretation (participantInterface F G) I)
    (tables : Evaluation.ComponentTables F G I) (self : Nat)
    (protocols : ProtocolTable (assignment F G) I := [])
    (context : ProtocolContext := {}) : RegionMeaning protocolDialect I where
  Value := Component (assignment F G)
  operation := fun op args callbacks =>
    protocolOperationWith observations actions tables self op args callbacks protocols context

abbrev protocolOperation (tables : OpenTables F G) (self : Nat)
    (op : ProtocolOp) (args : Values (Component (assignment F G)) op.arguments)
    (callbacks : Values (RegionFunction (Component (assignment F G)) (observedInterface F G)) op.regions)
    (protocols : ProtocolTable (assignment F G) (observedInterface F G) := [])
    (context : ProtocolContext := {}) :=
  protocolOperationWith (observedSites F G) observeAction tables self op args callbacks protocols context

abbrev participantMeaning (tables : OpenTables F G) (self : Nat)
    (protocols : ProtocolTable (assignment F G) (observedInterface F G) := [])
    (context : ProtocolContext := {}) :=
  participantMeaningWith (observedSites F G) observeAction tables self protocols context

/-- Interpretations preserve the same root coordinates and every child context. -/
theorem protocolOperationWith_interpret {I J : PIR.Signature}
    (operations : PIR.OperationInterpretation I J)
    {leftSites : SiteObservations I} {rightSites : SiteObservations J}
    (sites : SiteObservations.Interprets operations leftSites rightSites)
    {leftActions : PIR.OperationInterpretation (participantInterface F G) I}
    {rightActions : PIR.OperationInterpretation (participantInterface F G) J}
    (actions : ∀ action, (leftActions action).interpret operations = rightActions action)
    {left : Evaluation.ComponentTables F G I} {right : Evaluation.ComponentTables F G J}
    (tables : Evaluation.ComponentTables.Interprets operations left right)
    (self : Nat) (op : ProtocolOp) (args : Values (Component (assignment F G)) op.arguments)
    (callbacks : Values (RegionFunction (Component (assignment F G)) I) op.regions)
    {leftProtocols : ProtocolTable (assignment F G) I}
    {rightProtocols : ProtocolTable (assignment F G) J}
    (protocols : ProtocolTable.Interprets operations leftProtocols rightProtocols)
    (context : ProtocolContext) :
    (protocolOperationWith leftSites leftActions left self op args callbacks leftProtocols context).interpret operations =
      protocolOperationWith rightSites rightActions right self op args
        (RegionFunctions.translate (dialect := protocolDialect) operations callbacks) rightProtocols context := by
  have actionProcess {A : Type} (process : PIR.Proc (participantInterface F G) A) :
      (process.interpret leftActions).interpret operations = process.interpret rightActions :=
    PIR.Proc.interpret_interchange leftActions operations rightActions actions process
  cases op with
  | calculate op allowed =>
    cases callbacks
    have translated := Evaluation.componentOperation_interpret operations sites tables op args
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
      change (((Participant.guard (services := services) (Value := assignment F G) self _ condition).interpret
        leftActions).bind (fun _ => .done (Values.nil : Values (Component (assignment F G)) []))).interpret operations =
        ((Participant.guard (services := services) (Value := assignment F G) self _ condition).interpret
          rightActions).bind (fun _ => .done Values.nil)
      simp only [PIR.Proc.interpret_bind, actionProcess, PIR.Proc.interpret]
  | exchange ty sender receiver site =>
    cases callbacks
    cases args with
    | cons value rest =>
      cases rest
      change (((Participant.exchange (services := services) self (context.roles sender) (context.roles receiver)
        (qualifyProtocolSite context.applicationPrefix site) value).interpret
        leftActions).bind (fun result => .done
          (Values.cons result Values.nil : Values (Component (assignment F G)) [ty]))).interpret operations =
        ((Participant.exchange (services := services) self (context.roles sender) (context.roles receiver)
          (qualifyProtocolSite context.applicationPrefix site) value).interpret
          rightActions).bind (fun result => .done (Values.cons result Values.nil))
      simp only [PIR.Proc.interpret_bind, actionProcess, PIR.Proc.interpret]
  | restrict => cases callbacks; cases args with
    | cons value rest => cases rest; rfl
  | draw =>
    cases callbacks
    simp only [protocolOperationWith, PIR.Proc.interpret_bind, actionProcess, PIR.Proc.interpret]
  | statement => cases callbacks; rfl
  | mark site =>
    cases callbacks
    cases args
    change ((leftSites.mark (qualifyProtocolSite context.applicationPrefix site)).bind
      (fun _ => .done (Values.nil : Values (Component (assignment F G)) []))).interpret operations =
      (rightSites.mark (qualifyProtocolSite context.applicationPrefix site)).bind (fun _ => .done Values.nil)
    simp only [PIR.Proc.interpret_bind, sites (qualifyProtocolSite context.applicationPrefix site), PIR.Proc.interpret]
  | protocolApply signature roles site =>
    cases callbacks
    change (if (context.enter site roles).contains signature self then
      invokeProtocol leftProtocols signature (context.enter site roles) self args
      else .done (Values.absent (assignment F G) signature.outputs)).interpret operations =
      if (context.enter site roles).contains signature self then
        invokeProtocol rightProtocols signature (context.enter site roles) self args
      else .done (Values.absent (assignment F G) signature.outputs)
    split
    · exact protocols signature _ self args
    · rfl

def participantMeaningTranslation {I J : PIR.Signature}
    (operations : PIR.OperationInterpretation I J)
    {leftSites : SiteObservations I} {rightSites : SiteObservations J}
    (sites : SiteObservations.Interprets operations leftSites rightSites)
    {leftActions : PIR.OperationInterpretation (participantInterface F G) I}
    {rightActions : PIR.OperationInterpretation (participantInterface F G) J}
    (actions : ∀ action, (leftActions action).interpret operations = rightActions action)
    {left : Evaluation.ComponentTables F G I} {right : Evaluation.ComponentTables F G J}
    (tables : Evaluation.ComponentTables.Interprets operations left right) (self : Nat)
    {leftProtocols : ProtocolTable (assignment F G) I}
    {rightProtocols : ProtocolTable (assignment F G) J}
    (protocols : ProtocolTable.Interprets operations leftProtocols rightProtocols)
    (context : ProtocolContext) :
    (participantMeaningWith leftSites leftActions left self leftProtocols context).Translation operations where
  operation op args callbacks :=
    protocolOperationWith rightSites rightActions right self op args callbacks rightProtocols context
  commutes op args callbacks :=
    (protocolOperationWith_interpret operations sites actions tables self op args callbacks protocols context).symm

theorem participant_denote_interpret {I J : PIR.Signature}
    (operations : PIR.OperationInterpretation I J)
    {leftSites : SiteObservations I} {rightSites : SiteObservations J}
    (sites : SiteObservations.Interprets operations leftSites rightSites)
    {leftActions : PIR.OperationInterpretation (participantInterface F G) I}
    {rightActions : PIR.OperationInterpretation (participantInterface F G) J}
    (actions : ∀ action, (leftActions action).interpret operations = rightActions action)
    {left : Evaluation.ComponentTables F G I} {right : Evaluation.ComponentTables F G J}
    (tables : Evaluation.ComponentTables.Interprets operations left right) (self : Nat)
    {Γ out : List Ty} (region : Region protocolDialect Γ out)
    (env : Environment (Component (assignment F G)) Γ)
    {leftProtocols : ProtocolTable (assignment F G) I}
    {rightProtocols : ProtocolTable (assignment F G) J}
    (protocols : ProtocolTable.Interprets operations leftProtocols rightProtocols)
    (context : ProtocolContext) :
    (region.denote (participantMeaningWith leftSites leftActions left self leftProtocols context) env).interpret operations =
      region.denote (participantMeaningWith rightSites rightActions right self rightProtocols context) env :=
  (region.denote_translate _ operations
    (participantMeaningTranslation operations sites actions tables self protocols context) env).symm

theorem Evaluation.ComponentTables.fold_forgetSites (definitions : List CheckedDefinition) :
    Evaluation.ComponentTables.Interprets (forgetSites (F := F) (G := G))
      (definitions.foldl (Evaluation.ComponentTables.extend (observedSites F G)) ⟨[], []⟩)
      (definitions.foldl (Evaluation.ComponentTables.extend (F := F) (G := G)
        (.silent (participantInterface F G))) ⟨[], []⟩) :=
  Evaluation.ComponentTables.fold_interpret forgetSites observedSites_forgetSites (.empty _) definitions

/-- Scopes hide supplied inputs before work and returned components after work.
They do not discard preceding effects or stops. -/
def maskValues {Value : Ty → Type} (self : Nat) :
    {types : List Ty} → List (List Nat) → Values (Component Value) types →
      Values (Component Value) types
  | [], _, .nil => .nil
  | _ :: _, scopes, .cons value rest =>
    .cons (Participant.restrict ((scopes.headD []).contains self) value)
      (maskValues self scopes.tail rest)

/-- One body denotation, with optional input and output masks at this context. -/
def CheckedProtocol.denoteWith {I : PIR.Signature}
    (definition : CheckedProtocol) (observations : SiteObservations I)
    (actions : PIR.OperationInterpretation (participantInterface F G) I)
    (helpers : Evaluation.ComponentTables F G I)
    (protocols : ProtocolTable (assignment F G) I) :
    ProtocolFunction (assignment F G) I definition.signature :=
  fun context self inputs =>
    (definition.body.denote (participantMeaningWith observations actions helpers self protocols context)
      (maskValues self (context.mapScopes definition.inputScopes) inputs).get).bind fun results =>
        .done (maskValues self (context.mapScopes definition.outputScopes) results)

/-- The new closure captures only the immutable earlier protocol table. -/
def extendProtocolTable {I : PIR.Signature}
    (observations : SiteObservations I)
    (actions : PIR.OperationInterpretation (participantInterface F G) I)
    (helpers : Evaluation.ComponentTables F G I)
    (captured : ProtocolTable (assignment F G) I)
    (definition : CheckedProtocol) : ProtocolTable (assignment F G) I :=
  ⟨definition.signature, definition.denoteWith observations actions helpers captured⟩ :: captured

def CheckedProtocol.observed (root : CheckedProtocol) (tables : OpenTables F G) (self : Nat)
    (inputs : Values (Component (assignment F G)) root.inputs)
    (protocols : ProtocolTable (assignment F G) (observedInterface F G) := [])
    (context : ProtocolContext := {}) :
    PIR.Proc (observedInterface F G) (Values (Component (assignment F G)) root.outputs) :=
  root.denoteWith (observedSites F G) observeAction tables protocols context self inputs

def CheckedProtocol.participant (root : CheckedProtocol) (tables : OpenTables F G) (self : Nat)
    (inputs : Values (Component (assignment F G)) root.inputs)
    (protocols : ProtocolTable (assignment F G) (observedInterface F G) := [])
    (context : ProtocolContext := {}) :
    PIR.Proc (participantInterface F G) (Values (Component (assignment F G)) root.outputs) :=
  (root.observed tables self inputs protocols context).interpret forgetSites

theorem CheckedProtocol.denoteWith_interpret {I J : PIR.Signature}
    (operations : PIR.OperationInterpretation I J)
    {leftSites : SiteObservations I} {rightSites : SiteObservations J}
    (sites : SiteObservations.Interprets operations leftSites rightSites)
    {leftActions : PIR.OperationInterpretation (participantInterface F G) I}
    {rightActions : PIR.OperationInterpretation (participantInterface F G) J}
    (actions : ∀ action, (leftActions action).interpret operations = rightActions action)
    {left : Evaluation.ComponentTables F G I} {right : Evaluation.ComponentTables F G J}
    (tables : Evaluation.ComponentTables.Interprets operations left right)
    {leftProtocols : ProtocolTable (assignment F G) I}
    {rightProtocols : ProtocolTable (assignment F G) J}
    (protocols : ProtocolTable.Interprets operations leftProtocols rightProtocols)
    (definition : CheckedProtocol) (context : ProtocolContext) (self : Nat)
    (args : Values (Component (assignment F G)) definition.inputs) :
    (definition.denoteWith leftSites leftActions left leftProtocols context self args).interpret operations =
      definition.denoteWith rightSites rightActions right rightProtocols context self args := by
  simp only [denoteWith, PIR.Proc.interpret_bind, PIR.Proc.interpret]
  dsimp only [CheckedProtocol.signature]
  rw [participant_denote_interpret operations sites actions tables self _ _ protocols context]

theorem extendProtocolTable_interpret {I J : PIR.Signature}
    (operations : PIR.OperationInterpretation I J)
    {leftSites : SiteObservations I} {rightSites : SiteObservations J}
    (sites : SiteObservations.Interprets operations leftSites rightSites)
    {leftActions : PIR.OperationInterpretation (participantInterface F G) I}
    {rightActions : PIR.OperationInterpretation (participantInterface F G) J}
    (actions : ∀ action, (leftActions action).interpret operations = rightActions action)
    {left : Evaluation.ComponentTables F G I} {right : Evaluation.ComponentTables F G J}
    (tables : Evaluation.ComponentTables.Interprets operations left right)
    {leftProtocols : ProtocolTable (assignment F G) I}
    {rightProtocols : ProtocolTable (assignment F G) J}
    (protocols : ProtocolTable.Interprets operations leftProtocols rightProtocols)
    (definition : CheckedProtocol) :
    ProtocolTable.Interprets operations
      (extendProtocolTable leftSites leftActions left leftProtocols definition)
      (extendProtocolTable rightSites rightActions right rightProtocols definition) :=
  protocols.cons definition.signature _ _
    (definition.denoteWith_interpret operations sites actions tables protocols)

theorem ProtocolTable.fold_interpret {I J : PIR.Signature}
    (operations : PIR.OperationInterpretation I J)
    {leftSites : SiteObservations I} {rightSites : SiteObservations J}
    (sites : SiteObservations.Interprets operations leftSites rightSites)
    {leftActions : PIR.OperationInterpretation (participantInterface F G) I}
    {rightActions : PIR.OperationInterpretation (participantInterface F G) J}
    (actions : ∀ action, (leftActions action).interpret operations = rightActions action)
    {left : Evaluation.ComponentTables F G I} {right : Evaluation.ComponentTables F G J}
    (tables : Evaluation.ComponentTables.Interprets operations left right)
    {leftProtocols : ProtocolTable (assignment F G) I}
    {rightProtocols : ProtocolTable (assignment F G) J}
    (protocols : ProtocolTable.Interprets operations leftProtocols rightProtocols)
    (definitions : List CheckedProtocol) :
    ProtocolTable.Interprets operations
      (definitions.foldl (extendProtocolTable leftSites leftActions left) leftProtocols)
      (definitions.foldl (extendProtocolTable rightSites rightActions right) rightProtocols) := by
  induction definitions generalizing leftProtocols rightProtocols with
  | nil => exact protocols
  | cons definition rest ih =>
    exact ih (extendProtocolTable_interpret operations sites actions tables protocols definition)

/-- The empty default table is the same semantics specialized to flat bodies. -/
theorem CheckedProtocol.participant_direct (root : CheckedProtocol)
    {observed : OpenTables F G} {plain : Evaluation.ComponentTables F G (participantInterface F G)}
    (tables : Evaluation.ComponentTables.Interprets forgetSites observed plain) (self : Nat)
    (inputs : Values (Component (assignment F G)) root.inputs) :
    root.participant observed self inputs =
      (root.body.denote (participantMeaningWith (.silent (participantInterface F G))
        (participantActions F G) plain self) (maskValues self root.inputScopes inputs).get).bind
          (fun results => .done (maskValues self root.outputScopes results)) := by
  have law := root.denoteWith_interpret forgetSites observedSites_forgetSites
    observeAction_forgetSites tables (ProtocolTable.Interprets.empty _) {} self inputs
  simpa only [CheckedProtocol.participant, CheckedProtocol.observed, CheckedProtocol.denoteWith,
    ProtocolContext.mapScopes_root, CheckedProtocol.signature] using law

theorem CheckedProtocol.participant_direct_fold (root : CheckedProtocol)
    (definitions : List CheckedDefinition) (self : Nat)
    (inputs : Values (Component (assignment F G)) root.inputs) :
    root.participant
      (definitions.foldl (Evaluation.ComponentTables.extend (observedSites F G)) ⟨[], []⟩) self inputs =
      (root.body.denote (participantMeaningWith (.silent (participantInterface F G)) (participantActions F G)
        (definitions.foldl (Evaluation.ComponentTables.extend (.silent (participantInterface F G))) ⟨[], []⟩)
        self) (maskValues self root.inputScopes inputs).get).bind
          (fun results => .done (maskValues self root.outputScopes results)) :=
  root.participant_direct (Evaluation.ComponentTables.fold_forgetSites definitions) self inputs

theorem CheckedProtocol.participant_body_view (root : CheckedProtocol)
    (body : Region protocolDialect root.inputs root.outputs)
    (same : root.raw = body.erase) (tables : OpenTables F G) (self : Nat)
    (inputs : Values (Component (assignment F G)) root.inputs) :
    root.participant tables self inputs =
      ((body.denote (participantMeaning tables self) (maskValues self root.inputScopes inputs).get).bind
        fun results => .done (maskValues self root.outputScopes results)).interpret forgetSites := by
  simp only [CheckedProtocol.participant, CheckedProtocol.observed, CheckedProtocol.denoteWith,
    ProtocolContext.mapScopes_root, root.body_eq_of_raw body same]
  rfl

/-- Hiding components never creates a value and preserves the complete ABI. -/
theorem maskValues_absent {Value : Ty → Type} (self : Nat)
    (types : List Ty) (scopes : List (List Nat)) :
    maskValues self scopes (Values.absent Value types) = Values.absent Value types := by
  induction types generalizing scopes with
  | nil => rfl
  | cons ty types ih =>
    simp only [Values.absent, maskValues, ih]
    congr 1
    simp [Participant.restrict]

theorem maskValues_idempotent {Value : Ty → Type} {types : List Ty}
    (self : Nat) (scopes : List (List Nat)) (values : Values (Component Value) types) :
    maskValues self scopes (maskValues self scopes values) = maskValues self scopes values := by
  induction values generalizing scopes with
  | nil => rfl
  | cons value rest ih =>
    simp only [maskValues, ih]
    congr 1
    unfold Participant.restrict
    split <;> rfl

theorem maskValues_commute {Value : Ty → Type} {types : List Ty}
    (self : Nat) (left right : List (List Nat)) (values : Values (Component Value) types) :
    maskValues self left (maskValues self right values) =
      maskValues self right (maskValues self left values) := by
  induction values generalizing left right with
  | nil => rfl
  | cons value rest ih =>
    simp only [maskValues, ih]
    congr 1
    unfold Participant.restrict
    split <;> split <;> rfl

theorem maskValues_enter {Value : Ty → Type} {types : List Ty}
    (self : Nat) (context : ProtocolContext) (site : String) (roles : List Nat)
    (scopes : List (List Nat)) (values : Values (Component Value) types) :
    maskValues self ((context.enter site roles).mapScopes scopes) values =
      maskValues self (context.mapScopes (scopes.map (List.map (roleSubstitution roles)))) values := by
  rw [ProtocolContext.mapScopes_enter]

theorem apply_outside {I : PIR.Signature} (observations : SiteObservations I)
    (actions : PIR.OperationInterpretation (participantInterface F G) I)
    (helpers : Evaluation.ComponentTables F G I) (protocols : ProtocolTable (assignment F G) I)
    (signature : ProtocolSignature) (roles : List Nat) (site : String)
    (context : ProtocolContext) (self : Nat)
    (args : Values (Component (assignment F G)) signature.inputs)
    (outside : (context.enter site roles).contains signature self = false) :
    protocolOperationWith observations actions helpers self (.protocolApply signature roles site)
      args .nil protocols context = .done (Values.absent (assignment F G) signature.outputs) := by
  simp [protocolOperationWith, outside]

theorem apply_inside {I : PIR.Signature} (observations : SiteObservations I)
    (actions : PIR.OperationInterpretation (participantInterface F G) I)
    (helpers : Evaluation.ComponentTables F G I) (protocols : ProtocolTable (assignment F G) I)
    (signature : ProtocolSignature) (roles : List Nat) (site : String)
    (context : ProtocolContext) (self : Nat)
    (args : Values (Component (assignment F G)) signature.inputs)
    (inside : (context.enter site roles).contains signature self = true) :
    protocolOperationWith observations actions helpers self (.protocolApply signature roles site)
      args .nil protocols context = invokeProtocol protocols signature (context.enter site roles) self args := by
  simp [protocolOperationWith, inside]
  rfl

/-- An immediately returned tuple, including an empty tuple, reaches the caller continuation. -/
theorem apply_returns {I : PIR.Signature} {A : Type}
    (observations : SiteObservations I)
    (actions : PIR.OperationInterpretation (participantInterface F G) I)
    (helpers : Evaluation.ComponentTables F G I) (protocols : ProtocolTable (assignment F G) I)
    (signature : ProtocolSignature) (roles : List Nat) (site : String)
    (context : ProtocolContext) (self : Nat)
    (args : Values (Component (assignment F G)) signature.inputs)
    (inside : (context.enter site roles).contains signature self = true)
    (results : Values (Component (assignment F G)) signature.outputs)
    (returns : invokeProtocol protocols signature (context.enter site roles) self args = .done results)
    (next : Values (Component (assignment F G)) signature.outputs → PIR.Proc I A) :
    (protocolOperationWith observations actions helpers self (.protocolApply signature roles site)
      args .nil protocols context).bind next = next results := by
  rw [apply_inside observations actions helpers protocols signature roles site context self args inside, returns]
  rfl

/-- An immediate child halt suppresses the suffix for every output arity, including zero.
For children with preceding marks or actions, use `apply_run_stops`. -/
theorem apply_stops {I : PIR.Signature} {A : Type}
    (observations : SiteObservations I)
    (actions : PIR.OperationInterpretation (participantInterface F G) I)
    (helpers : Evaluation.ComponentTables F G I) (protocols : ProtocolTable (assignment F G) I)
    (signature : ProtocolSignature) (roles : List Nat) (site : String)
    (context : ProtocolContext) (self : Nat)
    (args : Values (Component (assignment F G)) signature.inputs)
    (inside : (context.enter site roles).contains signature self = true)
    (reason : PIR.Stop)
    (stops : invokeProtocol protocols signature (context.enter site roles) self args = .halt reason)
    (next : Values (Component (assignment F G)) signature.outputs → PIR.Proc I A) :
    (protocolOperationWith observations actions helpers self (.protocolApply signature roles site)
      args .nil protocols context).bind next = .halt reason := by
  rw [apply_inside observations actions helpers protocols signature roles site context self args inside, stops]
  rfl

/-- A child may execute marks and actions before stopping. The caller suppresses
its suffix and preserves that complete stopped execution, including state and
ordered events, at every output arity. -/
theorem apply_run_stops {I : PIR.Signature} {A S E : Type}
    (observations : SiteObservations I)
    (actions : PIR.OperationInterpretation (participantInterface F G) I)
    (helpers : Evaluation.ComponentTables F G I) (protocols : ProtocolTable (assignment F G) I)
    (signature : ProtocolSignature) (roles : List Nat) (site : String)
    (context : ProtocolContext) (self : Nat)
    (args : Values (Component (assignment F G)) signature.inputs)
    (inside : (context.enter site roles).contains signature self = true)
    (handler : PIR.Handler I S E) (initial finalState : S) (events : List E) (reason : PIR.Stop)
    (stops : (invokeProtocol protocols signature (context.enter site roles) self args).run
      handler initial = ⟨.stopped reason, finalState, events⟩)
    (next : Values (Component (assignment F G)) signature.outputs → PIR.Proc I A) :
    ((protocolOperationWith observations actions helpers self (.protocolApply signature roles site)
      args .nil protocols context).bind next).run handler initial =
        ⟨.stopped reason, finalState, events⟩ := by
  rw [apply_inside observations actions helpers protocols signature roles site context self args inside]
  change ((invokeProtocol protocols signature (context.enter site roles) self args).bind next).run
    handler initial = _
  rw [PIR.run_bind, stops]
  rfl

end Zkc.Source.Structured

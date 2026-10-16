module

public import Zkc.Source.Structured.Interpretation
public import Zkc.Source.Participant

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
    (tables : Evaluation.ComponentTables F G I) (self : Nat) :
    (op : ProtocolOp) → Values (Component (assignment F G)) op.arguments →
    PIR.Proc I (Values (Component (assignment F G)) op.results)
  | .calculate op allowed, args =>
    Evaluation.componentOperation observations tables op args (op.calculationRegions allowed)
  | .localCall helper _ owner _, args =>
    Participant.owned self owner (invoke tables.closed helper) args
  | .guard owner _, .cons condition .nil =>
    ((Participant.guard (services := services) (Value := assignment F G) self owner condition).interpret
      actions).bind fun _ => .done .nil
  | .exchange _ sender receiver site, .cons value .nil =>
    ((Participant.exchange (services := services) self sender receiver site value).interpret
      actions).bind fun result => .done (.cons result .nil)
  | .restrict _ roles, .cons value .nil =>
    .done (.cons (Participant.restrict (roles.contains self) value) .nil)
  | .draw owner field site, args =>
    ((Participant.query (services := services) self owner site field args).interpret
      actions).bind fun result => .done (.cons result .nil)
  | .statement .., _ => .done .nil
  | .mark site, .nil => (observations.mark site).bind fun _ => .done .nil

abbrev participantMeaningWith {I : PIR.Signature} (observations : SiteObservations I)
    (actions : PIR.OperationInterpretation (participantInterface F G) I)
    (tables : Evaluation.ComponentTables F G I) (self : Nat) :
    RegionMeaning protocolDialect I where
  Value := Component (assignment F G)
  operation := fun op args _ => protocolOperationWith observations actions tables self op args

abbrev protocolOperation (tables : OpenTables F G) (self : Nat) :=
  protocolOperationWith (observedSites F G) observeAction tables self

abbrev participantMeaning (tables : OpenTables F G) (self : Nat) :=
  participantMeaningWith (observedSites F G) observeAction tables self

/-- Site, action, and paired helper-table correspondence suffice for every
protocol operation. Receives keep independent replies; owned work keeps stops. -/
theorem protocolOperationWith_interpret {I J : PIR.Signature}
    (operations : PIR.OperationInterpretation I J)
    {leftSites : SiteObservations I} {rightSites : SiteObservations J}
    (sites : SiteObservations.Interprets operations leftSites rightSites)
    {leftActions : PIR.OperationInterpretation (participantInterface F G) I}
    {rightActions : PIR.OperationInterpretation (participantInterface F G) J}
    (actions : ∀ action, (leftActions action).interpret operations = rightActions action)
    {left : Evaluation.ComponentTables F G I} {right : Evaluation.ComponentTables F G J}
    (tables : Evaluation.ComponentTables.Interprets operations left right)
    (self : Nat) (op : ProtocolOp) (args : Values (Component (assignment F G)) op.arguments) :
    (protocolOperationWith leftSites leftActions left self op args).interpret operations =
      protocolOperationWith rightSites rightActions right self op args := by
  have actionProcess {A : Type} (process : PIR.Proc (participantInterface F G) A) :
      (process.interpret leftActions).interpret operations = process.interpret rightActions :=
    PIR.Proc.interpret_interchange leftActions operations rightActions actions process
  cases op with
  | calculate op allowed =>
    have translated := Evaluation.componentOperation_interpret operations sites tables op args
      (op.calculationRegions allowed)
    rw [Op.calculationRegions_translate] at translated
    exact translated
  | localCall helper kind owner site =>
    exact Participant.owned_interpret operations self owner _ _ (tables.closed helper) args
  | guard =>
    cases args with
    | cons condition rest =>
      cases rest
      change (((Participant.guard (services := services) (Value := assignment F G) self _ condition).interpret
        leftActions).bind (fun _ => .done (Values.nil : Values (Component (assignment F G)) []))).interpret operations =
        ((Participant.guard (services := services) (Value := assignment F G) self _ condition).interpret
          rightActions).bind (fun _ => .done Values.nil)
      simp only [PIR.Proc.interpret_bind, actionProcess, PIR.Proc.interpret]
  | exchange ty sender receiver site =>
    cases args with
    | cons value rest =>
      cases rest
      change (((Participant.exchange (services := services) self sender receiver site value).interpret
        leftActions).bind (fun result => .done
          (Values.cons result Values.nil : Values (Component (assignment F G)) [ty]))).interpret operations =
        ((Participant.exchange (services := services) self sender receiver site value).interpret
          rightActions).bind (fun result => .done (Values.cons result Values.nil))
      simp only [PIR.Proc.interpret_bind, actionProcess, PIR.Proc.interpret]
  | restrict => cases args with
    | cons value rest => cases rest; rfl
  | draw =>
    simp only [protocolOperationWith, PIR.Proc.interpret_bind, actionProcess, PIR.Proc.interpret]
  | statement => rfl
  | mark site =>
    cases args
    simp only [protocolOperationWith, PIR.Proc.interpret_bind, sites site, PIR.Proc.interpret]

def participantMeaningTranslation {I J : PIR.Signature}
    (operations : PIR.OperationInterpretation I J)
    {leftSites : SiteObservations I} {rightSites : SiteObservations J}
    (sites : SiteObservations.Interprets operations leftSites rightSites)
    {leftActions : PIR.OperationInterpretation (participantInterface F G) I}
    {rightActions : PIR.OperationInterpretation (participantInterface F G) J}
    (actions : ∀ action, (leftActions action).interpret operations = rightActions action)
    {left : Evaluation.ComponentTables F G I} {right : Evaluation.ComponentTables F G J}
    (tables : Evaluation.ComponentTables.Interprets operations left right) (self : Nat) :
    (participantMeaningWith leftSites leftActions left self).Translation operations where
  operation op args _ := protocolOperationWith rightSites rightActions right self op args
  commutes op args _ := (protocolOperationWith_interpret operations sites actions tables self op args).symm

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
    (env : Environment (Component (assignment F G)) Γ) :
    (region.denote (participantMeaningWith leftSites leftActions left self) env).interpret operations =
      region.denote (participantMeaningWith rightSites rightActions right self) env :=
  (region.denote_translate _ operations (participantMeaningTranslation operations sites actions tables self) env).symm

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

def CheckedProtocol.observed (root : CheckedProtocol) (tables : OpenTables F G) (self : Nat)
    (inputs : Values (Component (assignment F G)) root.inputs) :
    PIR.Proc (observedInterface F G) (Values (Component (assignment F G)) root.outputs) :=
  (root.body.denote (participantMeaning tables self)
    (maskValues self root.inputScopes inputs).get).bind fun results =>
      .done (maskValues self root.outputScopes results)

def CheckedProtocol.participant (root : CheckedProtocol) (tables : OpenTables F G) (self : Nat)
    (inputs : Values (Component (assignment F G)) root.inputs) :
    PIR.Proc (participantInterface F G) (Values (Component (assignment F G)) root.outputs) :=
  (root.observed tables self inputs).interpret forgetSites

/-- Direct plain interpretation of the existing erased observed meaning. The
table premise follows from `ComponentTables.fold_forgetSites` for stored bodies. -/
theorem CheckedProtocol.participant_direct (root : CheckedProtocol)
    {observed : OpenTables F G} {plain : Evaluation.ComponentTables F G (participantInterface F G)}
    (tables : Evaluation.ComponentTables.Interprets forgetSites observed plain) (self : Nat)
    (inputs : Values (Component (assignment F G)) root.inputs) :
    root.participant observed self inputs =
      (root.body.denote (participantMeaningWith (.silent (participantInterface F G))
        (participantActions F G) plain self) (maskValues self root.inputScopes inputs).get).bind
          (fun results => .done (maskValues self root.outputScopes results)) := by
  simp only [CheckedProtocol.participant, CheckedProtocol.observed, PIR.Proc.interpret_bind,
    PIR.Proc.interpret]
  rw [participant_denote_interpret forgetSites observedSites_forgetSites
    observeAction_forgetSites tables self]

/-- The direct view is obtained from the actual prefix fold, without an assumed
equation for any source body. No input availability or totality is asserted. -/
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
  simp only [CheckedProtocol.participant, CheckedProtocol.observed, root.body_eq_of_raw body same]

end Zkc.Source.Structured

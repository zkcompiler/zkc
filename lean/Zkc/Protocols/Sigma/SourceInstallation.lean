module

public import Zkc.Protocols.Sigma.SourceBodies

@[expose] public section

/-! Full optional source equations for module protocols. The reference uses
ordinary optional arithmetic and the existing open participant actions. Every
reply and stop is preserved, independently of honest execution or sampling. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace Zkc.Protocols.Sigma.Source
open Zkc.Source Zkc.Source.Structured

/-- Strict optional arithmetic has no fabricated default value. -/
def optional₂ {A B C : Type} (f : A → B → C) (a : Option A) (b : Option B) : Option C :=
  match a, b with | some a, some b => some (f a b) | _, _ => none

def scale (model : DomainModel) (d : Domains) :=
  optional₂ (fun (point : model.Group d.group) (scalar : model.Field d.scalar) =>
    model.smul d.group d.scalar scalar point)

def equal (model : DomainModel) (group : String) :=
  optional₂ (fun (a b : model.Group group) => decide (a = b))

private theorem silent_mark {I : PIR.Signature} (site : String) :
    (SiteObservations.silent I).mark site = .done () := rfl

private theorem get_here {V : Ty → Type} {ty : Ty} {types : List Ty}
    (value : V ty) (rest : Values V types) : (Values.cons value rest).get .here = value := rfl

private theorem get_there {V : Ty → Type} {ty other : Ty} {types : List Ty}
    (value : V ty) (rest : Values V types) (position : Var types other) :
    (Values.cons value rest).get (.there position) = rest.get position := rfl

private theorem push_here {V : Ty → Type} {ty : Ty} {types : List Ty}
    (env : Environment V types) (value : V ty) : env.push value .here = value := rfl

private theorem push_there {V : Ty → Type} {ty other : Ty} {types : List Ty}
    (env : Environment V types) (value : V ty) (position : Var types other) :
    env.push value (.there position) = env position := rfl

section Leaves
variable (model : DomainModel) {I : PIR.Signature}
  (tables : Evaluation.ComponentTablesOn model.toCarriers I)

@[simp] theorem calculate_scale (d : Domains) (point : Option (model.Group d.group))
    (scalar : Option (model.Field d.scalar)) :
    Evaluation.componentOperationOn model (.silent I) tables (.groupScale d.group d.scalar)
      (.cons point (.cons scalar .nil)) .nil = .done (.cons (scale model d point scalar) .nil) := by
  cases point <;> cases scalar <;> rfl

@[simp] theorem calculate_add (group : String) (a b : Option (model.Group group)) :
    Evaluation.componentOperationOn model (.silent I) tables (.groupAdd group)
      (.cons a (.cons b .nil)) .nil = .done (.cons (optional₂ (· + ·) a b) .nil) := by
  cases a <;> cases b <;> rfl

@[simp] theorem calculate_equal (group : String) (a b : Option (model.Group group)) :
    Evaluation.componentOperationOn model (.silent I) tables (.groupEqual group)
      (.cons a (.cons b .nil)) .nil = .done (.cons (equal model group a b) .nil) := by
  cases a <;> cases b <;> rfl

@[simp] theorem calculate_fieldAdd (field : String) (a b : Option (model.Field field)) :
    Evaluation.componentOperationOn model (.silent I) tables (.fieldAdd field)
      (.cons a (.cons b .nil)) .nil = .done (.cons (optional₂ (· + ·) a b) .nil) := by
  cases a <;> cases b <;> rfl

@[simp] theorem calculate_fieldMultiply (field : String) (a b : Option (model.Field field)) :
    Evaluation.componentOperationOn model (.silent I) tables (.fieldMultiply field)
      (.cons a (.cons b .nil)) .nil = .done (.cons (optional₂ (· * ·) a b) .nil) := by
  cases a <;> cases b <;> rfl

@[simp] theorem calculate_and (a b : Option Bool) :
    Evaluation.componentOperationOn model (.silent I) tables .booleanAnd
      (.cons a (.cons b .nil)) .nil = .done (.cons (optional₂ (· && ·) a b) .nil) := by
  cases a <;> cases b <;> rfl
end Leaves

section Processes
variable (model : DomainModel) (d : Domains) (sites : Sites)
  {I : PIR.Signature}
  (actions : PIR.OperationInterpretation (participantInterfaceOn model.toCarriers) I)
  (ctx : ProtocolContext) (self : Nat)

/-- Query the actual service input, retaining the qualified occurrence and role. -/
def draw (owner : Nat) (site : String) (service : Option Nat) :
    PIR.Process I (Option (model.Field d.scalar)) :=
  (Participant.query (services := services) (Value := model.Value) self (ctx.roles owner) (qualifyProtocolSite ctx.applicationPrefix site)
    d.scalar (.cons service .nil)).interpret actions

def exchange {ty : Ty} (sender receiver : Nat) (site : String)
    (value : Option (model.Value ty)) : PIR.Process I (Option (model.Value ty)) :=
  (Participant.exchange (services := services) self (ctx.roles sender) (ctx.roles receiver)
    (qualifyProtocolSite ctx.applicationPrefix site) value).interpret actions

/-- The value is retained only at the selected declaration-local role. -/
def atRole {A : Type} (role : Nat) (value : Option A) : Option A :=
  Participant.restrict (([role].map ctx.roles).contains self) value

def singleReference (base point : Option (model.Group d.group))
    (witness : Option (model.Field d.scalar)) (nonceService challengeService : Option Nat) :
    PIR.Process I (Values (Component model.Value) [.boolean]) := do
  let nonce ← draw model d actions ctx self 0 sites.nonce nonceService
  let commitment ← exchange model actions ctx self 0 1 sites.commitment (ty := .group d.group) (scale model d base nonce)
  let challenge ← draw model d actions ctx self 1 sites.challenge challengeService
  let delivered ← exchange model actions ctx self 1 0 sites.delivery (ty := .field d.scalar) challenge
  let response := optional₂ (· + ·) nonce
    (optional₂ (· * ·) (atRole ctx self 0 delivered) witness)
  let received ← exchange model actions ctx self 0 1 sites.response (ty := .field d.scalar) response
  pure (.cons (equal model d.group (scale model d base (atRole ctx self 1 received))
    (optional₂ (· + ·) (atRole ctx self 1 commitment) (scale model d point challenge))) .nil)

/-- Independent witnesses and nonces share the delivered public challenge.
The second query remains present even if a service aliases its state. -/
def independentReference (firstBase firstPoint secondBase secondPoint : Option (model.Group d.group))
    (firstWitness secondWitness : Option (model.Field d.scalar))
    (nonceService challengeService : Option Nat) :
    PIR.Process I (Values (Component model.Value) [.boolean]) := do
  let firstNonce ← draw model d actions ctx self 0 sites.nonce nonceService
  let secondNonce ← draw model d actions ctx self 0 sites.secondNonce nonceService
  let firstCommitment ← exchange model actions ctx self 0 1 sites.commitment (ty := .group d.group) (scale model d firstBase firstNonce)
  let secondCommitment ← exchange model actions ctx self 0 1 sites.secondCommitment (ty := .group d.group)
    (scale model d secondBase secondNonce)
  let challenge ← draw model d actions ctx self 1 sites.challenge challengeService
  let delivered ← exchange model actions ctx self 1 0 sites.delivery (ty := .field d.scalar) challenge
  let firstResponse := optional₂ (· + ·) firstNonce
    (optional₂ (· * ·) (atRole ctx self 0 delivered) firstWitness)
  let firstReceived ← exchange model actions ctx self 0 1 sites.response (ty := .field d.scalar) firstResponse
  let secondResponse := optional₂ (· + ·) secondNonce
    (optional₂ (· * ·) (atRole ctx self 0 delivered) secondWitness)
  let secondReceived ← exchange model actions ctx self 0 1 sites.secondResponse
    (ty := .field d.scalar) secondResponse
  pure (.cons (optional₂ (· && ·)
    (equal model d.group (scale model d firstBase (atRole ctx self 1 firstReceived))
      (optional₂ (· + ·) (atRole ctx self 1 firstCommitment) (scale model d firstPoint challenge)))
    (equal model d.group (scale model d secondBase (atRole ctx self 1 secondReceived))
      (optional₂ (· + ·) (atRole ctx self 1 secondCommitment) (scale model d secondPoint challenge)))) .nil)

/-- Shared witness, nonce and response across two bases. -/
def sharedReference (firstBase firstPoint secondBase secondPoint : Option (model.Group d.group))
    (witness : Option (model.Field d.scalar)) (nonceService challengeService : Option Nat) :
    PIR.Process I (Values (Component model.Value) [.boolean]) := do
  let nonce ← draw model d actions ctx self 0 sites.nonce nonceService
  let firstCommitment ← exchange model actions ctx self 0 1 sites.commitment (ty := .group d.group) (scale model d firstBase nonce)
  let secondCommitment ← exchange model actions ctx self 0 1 sites.secondCommitment (ty := .group d.group) (scale model d secondBase nonce)
  let challenge ← draw model d actions ctx self 1 sites.challenge challengeService
  let delivered ← exchange model actions ctx self 1 0 sites.delivery (ty := .field d.scalar) challenge
  let response := optional₂ (· + ·) nonce
    (optional₂ (· * ·) (atRole ctx self 0 delivered) witness)
  let received ← exchange model actions ctx self 0 1 sites.response (ty := .field d.scalar) response
  pure (.cons (optional₂ (· && ·)
    (equal model d.group (scale model d firstBase (atRole ctx self 1 received))
      (optional₂ (· + ·) (atRole ctx self 1 firstCommitment) (scale model d firstPoint challenge)))
    (equal model d.group (scale model d secondBase (atRole ctx self 1 received))
      (optional₂ (· + ·) (atRole ctx self 1 secondCommitment) (scale model d secondPoint challenge)))) .nil)
end Processes

section Equations
variable (model : DomainModel) (d : Domains) (metadata : Metadata) (sites : Sites)
  {I : PIR.Signature}
  (actions : PIR.OperationInterpretation (participantInterfaceOn model.toCarriers) I)
  (tables : Evaluation.ComponentTablesOn model.toCarriers I)
  (protocols : ProtocolTable model.Value I) (ctx : ProtocolContext) (self : Nat)
  (iterations : IterationObservations I)

def singleView (arguments : Values (Component model.Value) (singleSignature d metadata).inputs) :
    PIR.Process I (Values (Component model.Value) [.boolean]) :=
  singleReference model d sites actions ctx self (arguments.get .here) (arguments.get (.there .here)) (arguments.get (.there (.there .here))) (arguments.get (.there (.there (.there .here)))) (arguments.get (.there (.there (.there (.there .here)))))

/-- One complete equation for all optional inputs, roles and replies. -/
theorem single_body (arguments : Values (Component model.Value) (singleSignature d metadata).inputs) :
    (singleBody d metadata sites).denote
      (participantMeaningWithOn model (.silent I) actions tables self protocols ctx iterations)
      arguments.get = singleView model d metadata sites actions ctx self arguments := by
  match arguments with
  | (.cons base (.cons point (.cons witness (.cons nonceService (.cons challengeService .nil))))) =>
    cases statement : metadata.statement <;>
      simp only [singleBody, annotate, statement] <;>
      simp only [singleView, singleReference,
        Region.denote, Operands.eval, Regions.denote, get_here, get_there,
        Environment.prepend, push_here, push_there, participantMeaningWithOn,
        protocolOperationWithOn, silent_mark, Op.calculationRegions, id_eq,
        calculate_scale model tables d, calculate_add model tables d.group,
        calculate_equal model tables d.group, calculate_fieldAdd model tables d.scalar,
        calculate_fieldMultiply model tables d.scalar, calculate_and model tables, draw, exchange, atRole,
        PIR.Process.bind_assoc, PIR.Process.bind] <;> rfl

def independentView (arguments : Values (Component model.Value) (independentSignature d metadata).inputs) :
    PIR.Process I (Values (Component model.Value) [.boolean]) :=
  independentReference model d sites actions ctx self (arguments.get .here) (arguments.get (.there .here)) (arguments.get (.there (.there .here))) (arguments.get (.there (.there (.there .here)))) (arguments.get (.there (.there (.there (.there .here))))) (arguments.get (.there (.there (.there (.there (.there .here)))))) (arguments.get (.there (.there (.there (.there (.there (.there .here))))))) (arguments.get (.there (.there (.there (.there (.there (.there (.there .here))))))))

/-- One complete equation for all optional inputs, roles and replies. -/
theorem independent_body (arguments : Values (Component model.Value) (independentSignature d metadata).inputs) :
    (independentBody d metadata sites).denote
      (participantMeaningWithOn model (.silent I) actions tables self protocols ctx iterations)
      arguments.get = independentView model d metadata sites actions ctx self arguments := by
  match arguments with
  | (.cons firstBase (.cons firstPoint (.cons secondBase (.cons secondPoint (.cons firstWitness (.cons secondWitness (.cons nonceService (.cons challengeService .nil)))))))) =>
    cases statement : metadata.statement <;>
      simp only [independentBody, annotate, statement] <;>
      simp only [independentView, independentReference,
        Region.denote, Operands.eval, Regions.denote, get_here, get_there,
        Environment.prepend, push_here, push_there, participantMeaningWithOn,
        protocolOperationWithOn, silent_mark, Op.calculationRegions, id_eq,
        calculate_scale model tables d, calculate_add model tables d.group,
        calculate_equal model tables d.group, calculate_fieldAdd model tables d.scalar,
        calculate_fieldMultiply model tables d.scalar, calculate_and model tables, draw, exchange, atRole,
        PIR.Process.bind_assoc, PIR.Process.bind] <;> rfl

def sharedView (arguments : Values (Component model.Value) (sharedSignature d metadata).inputs) :
    PIR.Process I (Values (Component model.Value) [.boolean]) :=
  sharedReference model d sites actions ctx self (arguments.get .here) (arguments.get (.there .here)) (arguments.get (.there (.there .here))) (arguments.get (.there (.there (.there .here)))) (arguments.get (.there (.there (.there (.there .here))))) (arguments.get (.there (.there (.there (.there (.there .here)))))) (arguments.get (.there (.there (.there (.there (.there (.there .here)))))))

/-- One complete equation for all optional inputs, roles and replies. -/
theorem shared_body (arguments : Values (Component model.Value) (sharedSignature d metadata).inputs) :
    (sharedBody d metadata sites).denote
      (participantMeaningWithOn model (.silent I) actions tables self protocols ctx iterations)
      arguments.get = sharedView model d metadata sites actions ctx self arguments := by
  match arguments with
  | (.cons firstBase (.cons firstPoint (.cons secondBase (.cons secondPoint (.cons witness (.cons nonceService (.cons challengeService .nil))))))) =>
    cases statement : metadata.statement <;>
      simp only [sharedBody, annotate, statement] <;>
      simp only [sharedView, sharedReference,
        Region.denote, Operands.eval, Regions.denote, get_here, get_there,
        Environment.prepend, push_here, push_there, participantMeaningWithOn,
        protocolOperationWithOn, silent_mark, Op.calculationRegions, id_eq,
        calculate_scale model tables d, calculate_add model tables d.group,
        calculate_equal model tables d.group, calculate_fieldAdd model tables d.scalar,
        calculate_fieldMultiply model tables d.scalar, calculate_and model tables, draw, exchange, atRole,
        PIR.Process.bind_assoc, PIR.Process.bind] <;> rfl

end Equations

/-- Install the complete single-witness schedule at any exactly associated
source declaration. Visibility and role mapping use the shared template API. -/
theorem single_install (model : DomainModel) (d : Domains) (metadata : Metadata) (sites : Sites)
    {payload : UnitPayload}
    (associated : Template.Association payload (singleSignature d metadata) (singleBody d metadata sites))
    (role : Nat) (ctx : ProtocolContext) (distinct : NormalForm.RosterDistinct ctx role 2)
    (pattern : NormalForm.InputPattern (singleSignature d metadata).inputs)
    (visible : InputVisibility.patternVisible role pattern (singleSignature d metadata).inputScopes = true)
    (arguments : NormalForm.Binders model pattern.scope)
    (others : Values (Component model.Value) pattern.absentTypes) :
    invokeProtocol (Occurrence.table model payload) (singleSignature d metadata) ctx (ctx.roles role)
      (pattern.fill model arguments others) =
    (singleView model d metadata sites Occurrence.actions ctx (ctx.roles role)
      (pattern.environment model arguments)).bind fun out =>
        .done (NormalForm.staticMask role out [[1]] (Operands.identity [Ty.boolean])) := by
  apply associated.invoke role ctx distinct pattern visible arguments others
  · exact single_body model d metadata sites Occurrence.actions
      (Occurrence.helpers model payload) (Occurrence.table model payload) ctx (ctx.roles role)
      Occurrence.iterations _
  · rfl
  · rfl

/-- Install the complete independent-witness schedule at any exactly associated
source declaration. Visibility and role mapping use the shared template API. -/
theorem independent_install (model : DomainModel) (d : Domains) (metadata : Metadata) (sites : Sites)
    {payload : UnitPayload}
    (associated : Template.Association payload (independentSignature d metadata) (independentBody d metadata sites))
    (role : Nat) (ctx : ProtocolContext) (distinct : NormalForm.RosterDistinct ctx role 2)
    (pattern : NormalForm.InputPattern (independentSignature d metadata).inputs)
    (visible : InputVisibility.patternVisible role pattern (independentSignature d metadata).inputScopes = true)
    (arguments : NormalForm.Binders model pattern.scope)
    (others : Values (Component model.Value) pattern.absentTypes) :
    invokeProtocol (Occurrence.table model payload) (independentSignature d metadata) ctx (ctx.roles role)
      (pattern.fill model arguments others) =
    (independentView model d metadata sites Occurrence.actions ctx (ctx.roles role)
      (pattern.environment model arguments)).bind fun out =>
        .done (NormalForm.staticMask role out [[1]] (Operands.identity [Ty.boolean])) := by
  apply associated.invoke role ctx distinct pattern visible arguments others
  · exact independent_body model d metadata sites Occurrence.actions
      (Occurrence.helpers model payload) (Occurrence.table model payload) ctx (ctx.roles role)
      Occurrence.iterations _
  · rfl
  · rfl

/-- Install the complete shared-witness schedule at any exactly associated
source declaration. Visibility and role mapping use the shared template API. -/
theorem shared_install (model : DomainModel) (d : Domains) (metadata : Metadata) (sites : Sites)
    {payload : UnitPayload}
    (associated : Template.Association payload (sharedSignature d metadata) (sharedBody d metadata sites))
    (role : Nat) (ctx : ProtocolContext) (distinct : NormalForm.RosterDistinct ctx role 2)
    (pattern : NormalForm.InputPattern (sharedSignature d metadata).inputs)
    (visible : InputVisibility.patternVisible role pattern (sharedSignature d metadata).inputScopes = true)
    (arguments : NormalForm.Binders model pattern.scope)
    (others : Values (Component model.Value) pattern.absentTypes) :
    invokeProtocol (Occurrence.table model payload) (sharedSignature d metadata) ctx (ctx.roles role)
      (pattern.fill model arguments others) =
    (sharedView model d metadata sites Occurrence.actions ctx (ctx.roles role)
      (pattern.environment model arguments)).bind fun out =>
        .done (NormalForm.staticMask role out [[1]] (Operands.identity [Ty.boolean])) := by
  apply associated.invoke role ctx distinct pattern visible arguments others
  · exact shared_body model d metadata sites Occurrence.actions
      (Occurrence.helpers model payload) (Occurrence.table model payload) ctx (ctx.roles role)
      Occurrence.iterations _
  · rfl
  · rfl

end Zkc.Protocols.Sigma.Source

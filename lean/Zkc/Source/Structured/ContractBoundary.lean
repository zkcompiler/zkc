module

public import Zkc.Source.Structured.ContractBinding
public import Zkc.Source.Structured.ProtocolLinking

@[expose] public section

/-! Contract values use the existing typed contexts and participant components.
Selectors preserve roles and repeated positions. Quantification over parameters
and witnesses belongs to a property consumer, outside these definitions. -/
set_option autoImplicit false
namespace Zkc.Source.Structured

inductive BoundaryPort (inputs outputs : List Ty) (type : Ty) where
  | input (ref : Var inputs type)
  | output (ref : Var outputs type)

def BoundaryPort.direction {inputs outputs : List Ty} {type : Ty} :
    BoundaryPort inputs outputs type → ContractDirection
  | .input _ => .input
  | .output _ => .output

def BoundaryPort.index {inputs outputs : List Ty} {type : Ty} :
    BoundaryPort inputs outputs type → Nat
  | .input ref | .output ref => ref.index

structure BoundarySelector (signature : ProtocolSignature) (type : Ty) where
  port : BoundaryPort signature.inputs signature.outputs type
  role : Fin signature.roles.length
  inScope : ((match port with
    | .input _ => signature.inputScopes
    | .output _ => signature.outputScopes)[port.index]?.getD []).contains role.val = true

def BoundarySelector.erase {signature : ProtocolSignature} {type : Ty}
    (selector : BoundarySelector signature type) : ContractSelector :=
  ⟨selector.port.direction, selector.port.index, signature.roles.get selector.role⟩

structure BoundaryValuation (Value : Ty → Type) (inputs outputs : List Ty) where
  inputs : Nat → Values (Component Value) inputs
  outputs : Nat → Values (Component Value) outputs

/-- Logical proof labels are separate from operational site names. Retained
repeat does not change ProtocolContext between iterations. Frames record checked
tree positions and explicitly chosen indices; they are not execution traces and
do not establish that a call or iteration was reached. -/
inductive InvocationFrame where
  | application (caller : Nat) (position : List Nat)
  | iteration (owner : Nat) (position : List Nat) (index : Nat)
  deriving DecidableEq, Repr

structure InvocationCoordinate where
  root : Nat
  frames : List InvocationFrame := []
  deriving DecidableEq, Repr

def BoundarySelector.read {signature : ProtocolSignature} {type : Ty} {Value : Ty → Type}
    (selector : BoundarySelector signature type) (context : ProtocolContext)
    (values : BoundaryValuation Value signature.inputs signature.outputs) : Option (Value type) :=
  match selector.port with
  | .input ref => (values.inputs (context.roles selector.role)).get ref
  | .output ref => (values.outputs (context.roles selector.role)).get ref

/-- One assignment is shared by all clauses. Keys include direction, port and
role: repeated selectors share a value; different role copies remain distinct.
Assignments may model fixed experiment parameters or an extracted witness.
Agreement with runtime ports is a separate, explicit premise when required. -/
structure LogicalAssignments (Value : Ty → Type) {snapshot : Snapshot} {imported : Imported snapshot}
    (owner : ContractBinding imported) (invocation : InvocationCoordinate) where
  parameters : (type : Ty) → BoundarySelector owner.protocol.signature type → Option (Value type)
  witnesses : (type : Ty) → BoundarySelector owner.protocol.signature type → Option (Value type)

def eraseSelectors {signature : ProtocolSignature} {types : List Ty} :
    Values (BoundarySelector signature) types → List ContractSelector
  | .nil => []
  | .cons selector rest => selector.erase :: eraseSelectors rest

def readSelectors {Value : Ty → Type} {snapshot : Snapshot} {imported : Imported snapshot}
    {owner : ContractBinding imported} {invocation : InvocationCoordinate}
    (context : ProtocolContext) (boundary : BoundaryValuation Value owner.protocol.inputs owner.protocol.outputs)
    (assignments : LogicalAssignments Value owner invocation) : (purposes : List String) → {types : List Ty} →
    Values (BoundarySelector owner.protocol.signature) types → Values (Component Value) types
  | _, _, .nil => .nil
  | purposes, _, .cons selector rest =>
    .cons (match purposes.head? with
      | some "parameter" => assignments.parameters _ selector
      | some "witness" => assignments.witnesses _ selector
      | _ => selector.read context boundary)
      (readSelectors context boundary assignments purposes.tail rest)

/-- Typed ordered selectors must erase to the actual retained application. -/
structure ApplicationBinding {snapshot : Snapshot} {imported : Imported snapshot}
    (owner : ContractBinding imported) (application : RelationApplication) where
  relation : RelationBinding snapshot application
  selectors : Values (BoundarySelector owner.protocol.signature) relation.declaration.inputs
  exactSelectors : eraseSelectors selectors = application.selectors

namespace ApplicationBinding
variable {snapshot : Snapshot} {imported : Imported snapshot} {owner : ContractBinding imported}
variable {application : RelationApplication} {Value : Ty → Type}
variable {invocation : InvocationCoordinate}

def read (binding : ApplicationBinding owner application) (context : ProtocolContext)
    (boundary : BoundaryValuation Value owner.protocol.inputs owner.protocol.outputs)
    (assignments : LogicalAssignments Value owner invocation) : Option (Values Value binding.relation.declaration.inputs) :=
  RoleFamily.sequence (readSelectors context boundary assignments
    binding.relation.declaration.purposes binding.selectors)

/-- Linking an experiment's fixed parameters or honest witness to runtime inputs
requires this explicit agreement. Extraction may instead quantify a new shared
witness assignment without claiming equality with the prover's private input. -/
def Agrees (binding : ApplicationBinding owner application) (context : ProtocolContext)
    (boundary : BoundaryValuation Value owner.protocol.inputs owner.protocol.outputs)
    (assignments : LogicalAssignments Value owner invocation) : Prop :=
  readSelectors context boundary assignments binding.relation.declaration.purposes binding.selectors =
    readSelectors context boundary assignments [] binding.selectors


end ApplicationBinding

/-- Occurrence evidence is indexed by the actual checked tree and its operands.
No unchecked name or precomputed inspector answer can construct this evidence. -/
inductive ApplicationOccurrence (signature : ProtocolSignature) (roles : List Nat) (site : String)
    {Γ : List Ty} (operands : Operands Γ signature.inputs) :
    {Δ out : List Ty} → Region protocolDialect Δ out → Type where
  | here {out} (next : Region protocolDialect (signature.outputs ++ Γ) out) :
      ApplicationOccurrence signature roles site operands
        (.letOp (.protocolApply signature roles site) operands .nil next)
  | next {Δ out} (op : ProtocolOp) (args : Operands Δ op.arguments)
      (bodies : Regions protocolDialect op.regions) (tail : Region protocolDialect (op.results ++ Δ) out) :
      ApplicationOccurrence signature roles site operands tail →
      ApplicationOccurrence signature roles site operands (.letOp op args bodies tail)
  | bindBody {Δ mid out} (body : Region protocolDialect Δ mid)
      (next : Region protocolDialect (mid ++ Δ) out) :
      ApplicationOccurrence signature roles site operands body →
      ApplicationOccurrence signature roles site operands (.bind body next)
  | bindNext {Δ mid out} (body : Region protocolDialect Δ mid)
      (next : Region protocolDialect (mid ++ Δ) out) :
      ApplicationOccurrence signature roles site operands next →
      ApplicationOccurrence signature roles site operands (.bind body next)
  | repeatBody {Δ out} (spec : RepeatSpec) (repeatSite : String)
      (args : Operands Δ (.index :: (spec.state ++ spec.captures)))
      (body : Region protocolDialect (.index :: (spec.state ++ spec.captures)) spec.state)
      (next : Region protocolDialect (spec.state ++ Δ) out) :
      ApplicationOccurrence signature roles site operands body →
      ApplicationOccurrence signature roles site operands
        (.letOp (.repeat spec repeatSite) args (.cons body .nil) next)

structure CheckedApplication {snapshot : Snapshot} {imported : Imported snapshot}
    (callee : ContractBinding imported) (Γ : List Ty) where
  caller : ContractBinding imported
  roles : List Nat
  site : String
  operands : Operands Γ callee.protocol.inputs
  occurrence : ApplicationOccurrence callee.protocol.signature roles site operands caller.protocol.body
  substitution : ValidSubstitution caller.protocol.roles callee.protocol.signature roles

/-- Pure tuple substitution under the entered context. This helper assumes a
returned tuple for each role and supplies no execution or reachability evidence.
Use `boundaryOfOutcome` for a participant's actual application outcome; stopped
applications then have no outputs. -/
def CheckedApplication.boundary {snapshot : Snapshot} {imported : Imported snapshot}
    {callee : ContractBinding imported} {Γ : List Ty} {Value : Ty → Type}
    (call : CheckedApplication callee Γ) (context : ProtocolContext)
    (environment : Nat → Environment (Component Value) Γ)
    (returned : Nat → Values (Component Value) callee.protocol.outputs) :
    BoundaryValuation Value callee.protocol.inputs callee.protocol.outputs :=
  let entered := context.enter call.site call.roles
  ⟨fun self => maskValues self (entered.mapScopes callee.protocol.inputScopes)
      (call.operands.eval (environment self)),
   fun self => maskValues self (entered.mapScopes callee.protocol.outputScopes) (returned self)⟩

/-- Generic selector substitution at an actual checked application. This equation
includes input/output masks, exact returned order and composed role mapping. -/
theorem CheckedApplication.selector_substitution
    {snapshot : Snapshot} {imported : Imported snapshot} {callee : ContractBinding imported}
    {Γ : List Ty} {Value : Ty → Type} (call : CheckedApplication callee Γ)
    (context : ProtocolContext) (environment : Nat → Environment (Component Value) Γ)
    (returned : Nat → Values (Component Value) callee.protocol.outputs)
    {type : Ty} (selector : BoundarySelector callee.protocol.signature type) :
    selector.read (context.enter call.site call.roles) (call.boundary context environment returned) =
      let self := context.roles (roleSubstitution call.roles selector.role)
      match selector.port with
      | .input ref => (maskValues self
          (context.mapScopes (callee.protocol.inputScopes.map (List.map (roleSubstitution call.roles))))
          (call.operands.eval (environment self))).get ref
      | .output ref => (maskValues self
          (context.mapScopes (callee.protocol.outputScopes.map (List.map (roleSubstitution call.roles))))
          (returned self)).get ref := by
  unfold BoundarySelector.read CheckedApplication.boundary
  simp only [ProtocolContext.mapScopes_enter]
  cases selector.port <;> rfl

/-- Reading a masked tuple keeps the exact selected component and its scope. -/
theorem contract_mask_get {Value : Ty → Type} {types : List Ty}
    (self : Nat) (scopes : List (List Nat)) (values : Values (Component Value) types)
    {type : Ty} (ref : Var types type) :
    (maskValues self scopes values).get ref =
      Participant.restrict ((scopes[ref.index]?.getD []).contains self) (values.get ref) := by
  induction values generalizing scopes with
  | nil => cases ref
  | cons value rest ih =>
    cases ref with
    | here => cases scopes <;> rfl
    | there ref =>
      cases scopes with
      | nil => exact ih [] ref
      | cons scope scopes => exact ih scopes ref

/-- Input substitution reads the actual SSA operand at the composed role. -/
theorem CheckedApplication.input_substitution
    {snapshot : Snapshot} {imported : Imported snapshot} {callee : ContractBinding imported}
    {Γ : List Ty} {Value : Ty → Type} (call : CheckedApplication callee Γ)
    (context : ProtocolContext) (environment : Nat → Environment (Component Value) Γ)
    (returned : Nat → Values (Component Value) callee.protocol.outputs)
    {type : Ty} (selector : BoundarySelector callee.protocol.signature type)
    (ref : Var callee.protocol.inputs type) (selected : selector.port = .input ref) :
    selector.read (context.enter call.site call.roles) (call.boundary context environment returned) =
      let self := context.roles (roleSubstitution call.roles selector.role)
      Participant.restrict
        (((context.mapScopes (callee.protocol.inputScopes.map (List.map (roleSubstitution call.roles))))[ref.index]?.getD []).contains self) (environment self (call.operands.get ref)) := by
  simp only [call.selector_substitution, selected, contract_mask_get, Operands.get_eval]

/-- Output substitution observes the exact returned position at the chosen role. -/
theorem CheckedApplication.output_substitution
    {snapshot : Snapshot} {imported : Imported snapshot} {callee : ContractBinding imported}
    {Γ : List Ty} {Value : Ty → Type} (call : CheckedApplication callee Γ)
    (context : ProtocolContext) (environment : Nat → Environment (Component Value) Γ)
    (returned : Nat → Values (Component Value) callee.protocol.outputs)
    {type : Ty} (selector : BoundarySelector callee.protocol.signature type)
    (ref : Var callee.protocol.outputs type) (selected : selector.port = .output ref) :
    selector.read (context.enter call.site call.roles) (call.boundary context environment returned) =
      let self := context.roles (roleSubstitution call.roles selector.role)
      Participant.restrict
        (((context.mapScopes (callee.protocol.outputScopes.map (List.map (roleSubstitution call.roles))))[ref.index]?.getD []).contains self) ((returned self).get ref) := by
  simp only [call.selector_substitution, selected, contract_mask_get]

/-- Valid checked role substitutions compose at the same application boundary. -/
theorem CheckedApplication.context_valid
    {snapshot : Snapshot} {imported : Imported snapshot} {callee : ContractBinding imported}
    {Γ : List Ty} (call : CheckedApplication callee Γ) {rootRoles : List String}
    {context : ProtocolContext} (valid : context.Valid rootRoles call.caller.protocol.roles) :
    (context.enter call.site call.roles).Valid rootRoles callee.protocol.roles :=
  valid.enter call.substitution call.site

/-- The source-bound call enters the linked callee's actual body with precisely
these masks. Stops and preceding effects remain in the returned process. -/
theorem CheckedApplication.invoke_body
    {snapshot : Snapshot} {imported : Imported snapshot} {callee : ContractBinding imported}
    {Γ : List Ty} (call : CheckedApplication callee Γ)
    (F G : Type) [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]
    (context : ProtocolContext) (self : Nat)
    (environment : Environment (Component (assignment F G)) Γ)
    (inside : (context.enter call.site call.roles).contains callee.protocol.signature self = true) :
    protocolOperationWith (observedSites F G) observeAction (imported.program.payload.tables F G) self
      (.protocolApply callee.protocol.signature call.roles call.site)
      (call.operands.eval environment) .nil (imported.program.payload.protocolTable F G) context =
      (callee.protocol.body.denote
        (participantMeaning (imported.program.payload.tables F G) self
          (imported.program.payload.protocolTable F G) (context.enter call.site call.roles))
        (maskValues self ((context.enter call.site call.roles).mapScopes callee.protocol.inputScopes)
          (call.operands.eval environment)).get).bind
        (fun results => .done (maskValues self
          ((context.enter call.site call.roles).mapScopes callee.protocol.outputScopes) results)) := by
  exact (apply_inside (observedSites F G) observeAction (imported.program.payload.tables F G)
    (imported.program.payload.protocolTable F G) callee.protocol.signature call.roles call.site
    context self (call.operands.eval environment) inside).trans
    (imported.program.payload.protocol_body_view_as callee.protocol callee.retained.2.1
    callee.protocol.signature rfl callee.protocol.body callee.protocol.exactBody.symm
    (context.enter call.site call.roles) self (call.operands.eval environment))

end Zkc.Source.Structured

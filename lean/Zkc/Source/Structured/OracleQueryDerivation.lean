module

public import Zkc.Source.DerivationLaws
public import Zkc.Source.Structured.OracleProtocol

@[expose] public section

/-! Return views for checked scalar queries. The source service receives the
raw request, and only a reply inside the requested finite range reaches the
consumer. The source occurrence, stop and role substitution survive. -/
set_option autoImplicit false
namespace Zkc.Source.Structured.OracleProtocol
attribute [local implicit_reducible] ServiceOp.contract
variable (model : DomainModel)
variable {self owner : Nat} {context : ProtocolContext} {site contract : String}
  {ordinary : Evaluation.ComponentTablesOn model.toCarriers (Interface model)}
  {helpers : ProtocolCalculation.Tables model.toCarriers (Interface model)}
  {table : ProtocolTable (ProtocolValue model.toCarriers) (Interface model)}

def finiteIndex (site contract : String) (handle bound : Nat) :
    PIR.Process (Interface model) (Fin bound) :=
  if 0 < bound ∧ bound < indexLimit then
    .call (.ordinary (.query site (.sampleIndex contract) (.cons handle (.cons bound .nil))))
      fun reply ↦ if h : reply < bound then .done ⟨reply, h⟩ else .halt .refused
  else .halt .refused

abbrev concrete (ty : Ty) (value : model.Value ty) : Component (ProtocolValue model.toCarriers) ty :=
  some (ProtocolValue.ofConcrete ty value)

theorem scalarQuery (atOwner : context.roles owner = self) (handle bound : Nat) :
    ((algebra model self ordinary helpers).meaning table context self).OperationLaw
      (fun op ↦ .call op .done) (.query owner (.sampleIndex contract) site)
      (.cons (concrete model (.service contract) handle) (.cons (concrete model .index bound) .nil)) .nil
      ((finiteIndex model (qualifyProtocolSite context.applicationPrefix site) contract handle bound).bind
        (fun i ↦ .done (.cons (concrete model .index i.val) .nil))) := by
  apply RegionMeaning.OperationLaw.identity
  change (((Participant.query (services := services) self (context.roles owner)
    (qualifyProtocolSite context.applicationPrefix site) (.sampleIndex contract)
    (ProtocolValue.concreteComponents (.cons (concrete model (.service contract) handle)
      (.cons (concrete model .index bound) .nil)))).interpret serviceAction |>.interpret
    (actions model)).bind _) = _
  let arguments : Values model.Value [.service contract, .index] := .cons handle (.cons bound .nil)
  rw [show Values.cons (concrete model (.service contract) handle) (.cons (concrete model .index bound) .nil) =
    ProtocolValue.embedComponents arguments.present from rfl, ProtocolValue.concreteComponents_embedComponents]
  simp only [Participant.query, atOwner, ↓reduceIte, RoleFamily.sequence_present, arguments]
  have formed : (ServiceOp.sampleIndex contract).validInputs (carriers := model.toCarriers)
      (.cons handle (.cons bound .nil)) = decide (0 < bound ∧ bound < indexLimit) := by
    change (decide (0 < bound) && decide (bound < indexLimit)) = _
    simp
  by_cases valid : 0 < bound ∧ bound < indexLimit
  · simp [PIR.Process.interpret, serviceAction, formed, valid, finiteIndex, actions, PIR.Process.bind]
    funext reply
    have checked : (ServiceOp.sampleIndex contract).validReply (carriers := model.toCarriers)
        (.cons handle (.cons bound .nil)) reply = decide (reply < bound) := rfl
    by_cases inside : reply < bound <;> simp [checked, inside, PIR.Process.interpret, PIR.Process.bind]
  · simp [PIR.Process.interpret, serviceAction, formed, valid, finiteIndex, PIR.Process.bind]

theorem sendConcrete {ty : Ty} {peer : Nat} (atOwner : context.roles owner = self)
    (value : model.Value ty) :
    ((algebra model self ordinary helpers).meaning table context self).OperationLaw
      (fun op ↦ .call op .done) (.exchange ty owner peer site)
      (.cons (concrete model ty value) .nil) .nil
      (.call (.ordinary (.send (qualifyProtocolSite context.applicationPrefix site)
        (context.roles peer) value)) fun _ ↦ .done (.cons (concrete model ty value) .nil)) := by
  apply RegionMeaning.OperationLaw.identity
  change (exchange model context self owner peer site (concrete model ty value)).bind _ = _
  simp [exchange, Participant.exchange, atOwner, concrete, ProtocolValue.materializeWith_ofConcrete,
    actions, PIR.Process.interpret, PIR.Process.bind]

/-- The receiving role gets the peer's concrete message, independently
of its local operand. The selected handler controls every reply and stop. -/
theorem receiveConcrete {ty : Ty} {sender : Nat} (other : context.roles sender ≠ self)
    (active : context.roles owner = self) (value : Component (ProtocolValue model.toCarriers) ty) :
    ((algebra model self ordinary helpers).meaning table context self).operation (.exchange ty sender owner site)
      (.cons value .nil) .nil =
      .call (.ordinary (.receive ty (qualifyProtocolSite context.applicationPrefix site) (context.roles sender)))
        (fun reply ↦ .done (.cons (concrete model ty reply) .nil)) := by
  change (exchange model context self sender owner site value).bind _ = _
  simp [exchange, Participant.exchange, other, active, concrete, actions, PIR.Process.interpret, PIR.Process.bind]

theorem restrictActive {ty : Ty} (active : context.roles owner = self) (value : Component (ProtocolValue model.toCarriers) ty) :
    ((algebra model self ordinary helpers).meaning table context self).operation (.restrict ty [owner])
      (.cons value .nil) .nil = .done (.cons value .nil) := by
  change PIR.Process.done (I := Interface model)
    (Values.cons (Value := Component (ProtocolValue model.toCarriers)) (ty := ty)
      (Participant.restrict ([context.roles owner].contains self) value) .nil) = _
  congr 2
  simp [Participant.restrict, active]

/-- In a two-owner assembly the second component belongs to this participant.
The first owner's value may be absent or deferred. -/
theorem assembleSecond {first second : Nat} {ty : Ty}
    (other : context.roles first ≠ self) (active : context.roles second = self)
    (x y : Component (ProtocolValue model.toCarriers) ty) :
    ((algebra model self ordinary helpers).meaning table context self).operation
      (.assemble ty [first, second]) (.cons x (.cons y .nil)) .nil = .done (.cons y .nil) := by
  change PIR.Process.done (I := Interface model)
    (Values.cons (Value := Component (ProtocolValue model.toCarriers)) (ty := ty)
      (assembleComponent (fun r ↦ context.roles r == self) none [first, second] (.cons x (.cons y .nil))) .nil) = _
  congr 2
  simp [assembleComponent, active, other]

theorem compareIndex (a b : Nat) :
    ((algebra model self ordinary helpers).meaning table context self).operation (.calculate .indexEqual rfl)
      (.cons (concrete model .index a) (.cons (concrete model .index b) .nil)) .nil =
      .done (.cons (concrete model .boolean (decide (a = b))) .nil) := by
  change ProtocolCalculation.strict model (demand model) self ordinary .indexEqual
    (ProtocolValue.embedComponents (.cons (some a) (.cons (some b) .nil))) rfl = _
  erw [ProtocolCalculation.strict_embed model (demand model) self ordinary .indexEqual
    (.cons (some a) (.cons (some b) .nil)) rfl]
  rfl

/-- A missing first operand keeps the comparison absent. In particular it
does not demand a deferred second operand or invent a Boolean for another role. -/
theorem compareMissingIndexLeft (right : Component (ProtocolValue model.toCarriers) .index) :
    ((algebra model self ordinary helpers).meaning table context self).operation (.calculate .indexEqual rfl)
      (.cons none (.cons right .nil)) .nil = .done (.cons none .nil) := by
  rfl

theorem equalIndex (i : Nat) :
    ((algebra model self ordinary helpers).meaning table context self).OperationLaw
      (fun op ↦ .call op .done) (.calculate .indexEqual rfl)
      (.cons (concrete model .index i) (.cons (concrete model .index i) .nil)) .nil
      (.done (.cons (concrete model .boolean true) .nil)) := by
  apply RegionMeaning.OperationLaw.identity
  simpa only [decide_true] using compareIndex (context := context) (self := self)
    (ordinary := ordinary) (helpers := helpers) (table := table) model i i

theorem guardFalse (active : context.roles owner = self) :
    ((algebra model self ordinary helpers).meaning table context self).operation (.guard owner site)
      (.cons (concrete model .boolean false) .nil) .nil = .halt .reject := by
  change ((Participant.guard (services := services) (Value := model.Value) self (context.roles owner)
    ((concrete model .boolean false).bind ProtocolValue.toConcrete)).interpret (actions model)).bind _ = _
  simp [active, concrete, Participant.guard, PIR.Process.interpret, PIR.Process.bind]

/-- A helper owned by another participant consumes no local operands.
Its returned ABI is absent even when an input holds deferred oracle data. -/
theorem localCallInactive (helper : Helper) (localKind : helper.kind = .local)
    (other : context.roles owner ≠ self)
    (args : Values (Component (ProtocolValue model.toCarriers)) helper.inputs) :
    ((algebra model self ordinary helpers).meaning table context self).OperationLaw
      (fun op ↦ .call op .done) (.localCall helper localKind owner site) args .nil
      (.done (Values.absent _ helper.outputs)) := by
  apply RegionMeaning.OperationLaw.identity
  change owned model self (context.roles owner) ordinary helper args = _
  simp [owned, other]
  rfl

theorem guardInactive (other : context.roles owner ≠ self)
    (condition : Component (ProtocolValue model.toCarriers) .boolean) :
    ((algebra model self ordinary helpers).meaning table context self).OperationLaw
      (fun op ↦ .call op .done) (.guard owner site) (.cons condition .nil) .nil (.done .nil) := by
  apply RegionMeaning.OperationLaw.identity
  change ((Participant.guard (services := services) (Value := model.Value) self (context.roles owner)
    (condition.bind ProtocolValue.toConcrete)).interpret (actions model)).bind _ = _
  simp [Participant.guard, other, PIR.Process.interpret, PIR.Process.bind]

theorem guardTrue (owner : Nat) :
    ((algebra model self ordinary helpers).meaning table context self).OperationLaw
      (fun op ↦ .call op .done) (.guard owner site) (.cons (concrete model .boolean true) .nil) .nil
      (.done .nil) := by
  apply RegionMeaning.OperationLaw.identity
  change ((Participant.guard (services := services) (Value := model.Value) self (context.roles owner)
    ((concrete model .boolean true).bind ProtocolValue.toConcrete)).interpret (actions model)).bind _ = _
  simp [concrete, Participant.guard, PIR.Process.interpret, PIR.Process.bind]

end Zkc.Source.Structured.OracleProtocol

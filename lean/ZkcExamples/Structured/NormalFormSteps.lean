module

public import Zkc.Source.Participant
public import Zkc.Source.DenotationLaws
public import Zkc.Source.Structured.ContractComposition
public import Zkc.Source.Structured.RepeatLaws

@[expose] public section

/-! Steps cited by generated participant normal forms
(`lean/bridges/structured/normal_forms.py`): an owned Local call whose helper
law returns or stops behaves as that law at its owner; an operation whose
meaning is a process followed by a returned tuple continues with that tuple; an
active protocol application continues with the callee's masked returned
tuple, also under the outer bind of a repeat callback's normal form; and a repeat
whose callback has a role-local normal form is the fold of that form. -/
namespace ZkcExamples.Structured.NormalFormSteps
open Zkc.Source

theorem owned_done {Role : Type} [DecidableEq Role] {Ty : Type} {Value : Ty → Type}
    {I : PIR.Signature} {inputs outputs : List Ty} (self : Role)
    {work : Values Value inputs → PIR.Proc I (Values Value outputs)}
    (args : Values Value inputs) {results : Values Value outputs}
    (law : work args = .done results) :
    Participant.owned self self work args.present = .done results.present := by
  rw [Participant.owned_present, law]
  rfl

theorem owned_halt {Role : Type} [DecidableEq Role] {Ty : Type} {Value : Ty → Type}
    {I : PIR.Signature} {inputs outputs : List Ty} (self : Role)
    {work : Values Value inputs → PIR.Proc I (Values Value outputs)}
    (args : Values Value inputs) {reason : PIR.Stop}
    (law : work args = .halt reason) :
    Participant.owned self self work args.present = .halt reason := by
  rw [Participant.owned_present, law]
  rfl

/-- An operation whose meaning is a process followed by a returned tuple extends
the value tuple with that tuple in every continuation. -/
theorem denote_letOp_bind {d : Dialect} {I : PIR.Signature} (m : RegionMeaning d I)
    {Γ out : List d.Ty} (op : d.Op) (args : Operands Γ (d.arguments op))
    (bodies : Regions d (d.regions op)) (next : Region d (d.results op ++ Γ) out)
    (before : Values m.Value Γ) {A : Type} (process : PIR.Proc I A)
    (added : A → Values m.Value (d.results op)) (result : A → PIR.Proc I (Values m.Value out))
    (operation : m.operation op (args.eval before.get) (bodies.denote m) =
      process.bind (fun value => .done (added value)))
    (continuation : ∀ value, next.denote m ((added value).append before).get = result value) :
    (Region.letOp op args bodies next).denote m before.get = process.bind result := by
  rw [Region.denote_letOp_values, operation, PIR.Proc.bind_assoc]
  apply congrArg (PIR.Proc.bind process)
  funext value
  exact continuation value

/-- The same step under an outer bind, as in the normal form of a repeat callback
followed by the embedding of its carried state. -/
theorem denote_letOp_bind_after {d : Dialect} {I : PIR.Signature} (m : RegionMeaning d I)
    {Γ out : List d.Ty} (op : d.Op) (args : Operands Γ (d.arguments op))
    (bodies : Regions d (d.regions op)) (next : Region d (d.results op ++ Γ) out)
    (before : Values m.Value Γ) {A B : Type} (process : PIR.Proc I A)
    (added : A → Values m.Value (d.results op)) (result : A → PIR.Proc I B)
    (after : B → PIR.Proc I (Values m.Value out))
    (operation : m.operation op (args.eval before.get) (bodies.denote m) =
      process.bind (fun value => .done (added value)))
    (continuation : ∀ value,
      next.denote m ((added value).append before).get = (result value).bind after) :
    (Region.letOp op args bodies next).denote m before.get = (process.bind result).bind after := by
  rw [PIR.Proc.bind_assoc]
  exact denote_letOp_bind m op args bodies next before process added _ operation continuation

open Zkc.Source.Structured

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- Plain participant denotation is the observed one with its site marks forgotten. -/
theorem plain_denote (payload : UnitPayload) (self : Nat) {Γ out : List Ty}
    (region : Region protocolDialect Γ out) (environment : Environment (Component (assignment F G)) Γ)
    (ctx : ProtocolContext) :
    (region.denote (participantMeaning (payload.tables F G) self (payload.protocolTable F G) ctx)
      environment).interpret forgetSites =
    region.denote (participantMeaningWith (.silent _) (participantActions F G)
      (payload.definitions.foldl (Evaluation.ComponentTables.extend (.silent _)) ⟨[], []⟩) self
      (payload.plainProtocolTable F G) ctx) environment :=
  participant_denote_interpret forgetSites observedSites_forgetSites observeAction_forgetSites
    (Evaluation.ComponentTables.fold_forgetSites payload.definitions) self region environment
    payload.protocolTable_forgetSites ctx

/-- A protocol application at a participant of the callee's roster, by the generic
call substitution rule: the callee's checked body at the application's child
context (its qualified sites and mapped roles) on the masked operands, then the
caller's continuation on the callee's masked returned tuple. -/
theorem apply_step (payload : UnitPayload)
    (definition : CheckedProtocol) (member : definition ∈ payload.protocols)
    (signature : ProtocolSignature) (sameSignature : definition.signature = signature)
    (body : Region protocolDialect signature.inputs signature.outputs)
    (exactRaw : definition.raw = body.erase)
    (roles : List Nat) (site : String) (ctx : ProtocolContext) (self : Nat)
    {Γ out : List Ty} (operands : Operands Γ signature.inputs)
    (next : Region protocolDialect (signature.outputs ++ Γ) out)
    (before : Values (Component (assignment F G)) Γ)
    (inside : (ctx.enter site roles).contains signature self = true)
    (masked : Values (Component (assignment F G)) signature.inputs)
    (mask : maskValues self ((ctx.enter site roles).mapScopes signature.inputScopes)
      (operands.eval before.get) = masked)
    (process : PIR.Proc (participantInterface F G) (Values (Component (assignment F G)) signature.outputs))
    (callee : body.denote (participantMeaningWith (.silent _) (participantActions F G)
      (payload.definitions.foldl (Evaluation.ComponentTables.extend (.silent _)) ⟨[], []⟩) self
      (payload.plainProtocolTable F G) (ctx.enter site roles)) masked.get = process)
    (added : Values (Component (assignment F G)) signature.outputs →
      Values (Component (assignment F G)) signature.outputs)
    (outputs : ∀ values,
      maskValues self ((ctx.enter site roles).mapScopes signature.outputScopes) values = added values)
    (result : Values (Component (assignment F G)) signature.outputs →
      PIR.Proc (participantInterface F G) (Values (Component (assignment F G)) out))
    (continuation : ∀ values,
      next.denote (participantMeaningWith (.silent _) (participantActions F G)
        (payload.definitions.foldl (Evaluation.ComponentTables.extend (.silent _)) ⟨[], []⟩) self
        (payload.plainProtocolTable F G) ctx) ((added values).append before).get = result values) :
    (Region.letOp (dialect := protocolDialect) (.protocolApply signature roles site) operands .nil
      next).denote (participantMeaningWith (.silent _) (participantActions F G)
        (payload.definitions.foldl (Evaluation.ComponentTables.extend (.silent _)) ⟨[], []⟩) self
        (payload.plainProtocolTable F G) ctx) before.get =
      process.bind result := by
  rw [← plain_denote, payload.protocolApply_interpret_substitute definition member signature
    sameSignature body exactRaw roles site ctx self operands next before.get inside forgetSites _ rfl,
    plain_denote, mask, callee]
  apply congrArg (PIR.Proc.bind process)
  funext values
  rw [plain_denote, outputs, ← continuation, Environment.prepend_values_get]

/-- The same application step under an outer bind, as in the normal form of a repeat
callback followed by the embedding of its carried state. -/
theorem apply_step_after (payload : UnitPayload)
    (definition : CheckedProtocol) (member : definition ∈ payload.protocols)
    (signature : ProtocolSignature) (sameSignature : definition.signature = signature)
    (body : Region protocolDialect signature.inputs signature.outputs)
    (exactRaw : definition.raw = body.erase)
    (roles : List Nat) (site : String) (ctx : ProtocolContext) (self : Nat)
    {Γ out : List Ty} (operands : Operands Γ signature.inputs)
    (next : Region protocolDialect (signature.outputs ++ Γ) out)
    (before : Values (Component (assignment F G)) Γ)
    (inside : (ctx.enter site roles).contains signature self = true)
    (masked : Values (Component (assignment F G)) signature.inputs)
    (mask : maskValues self ((ctx.enter site roles).mapScopes signature.inputScopes)
      (operands.eval before.get) = masked)
    (process : PIR.Proc (participantInterface F G) (Values (Component (assignment F G)) signature.outputs))
    (callee : body.denote (participantMeaningWith (.silent _) (participantActions F G)
      (payload.definitions.foldl (Evaluation.ComponentTables.extend (.silent _)) ⟨[], []⟩) self
      (payload.plainProtocolTable F G) (ctx.enter site roles)) masked.get = process)
    (added : Values (Component (assignment F G)) signature.outputs →
      Values (Component (assignment F G)) signature.outputs)
    (outputs : ∀ values,
      maskValues self ((ctx.enter site roles).mapScopes signature.outputScopes) values = added values)
    {B : Type} (result : Values (Component (assignment F G)) signature.outputs →
      PIR.Proc (participantInterface F G) B)
    (after : B → PIR.Proc (participantInterface F G) (Values (Component (assignment F G)) out))
    (continuation : ∀ values,
      next.denote (participantMeaningWith (.silent _) (participantActions F G)
        (payload.definitions.foldl (Evaluation.ComponentTables.extend (.silent _)) ⟨[], []⟩) self
        (payload.plainProtocolTable F G) ctx) ((added values).append before).get =
          (result values).bind after) :
    (Region.letOp (dialect := protocolDialect) (.protocolApply signature roles site) operands .nil
      next).denote (participantMeaningWith (.silent _) (participantActions F G)
        (payload.definitions.foldl (Evaluation.ComponentTables.extend (.silent _)) ⟨[], []⟩) self
        (payload.plainProtocolTable F G) ctx) before.get =
      (process.bind result).bind after := by
  rw [PIR.Proc.bind_assoc]
  exact apply_step payload definition member signature sameSignature body exactRaw roles site ctx self
    operands next before inside masked mask process callee added outputs _ continuation

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
/-- A repeat on an admitted count at a participant of its roster, whose callback has a
role-local normal form over an embedding of the participant's carried slots, is the
fold of that normal form over the iteration indices followed by the embedding. The
initial state need only agree with the embedding after the state masks. -/
theorem repeat_embed {I : PIR.Signature} (spec : RepeatSpec) (ctx : ProtocolContext) (self : Nat)
    (inside : (spec.roles.map ctx.roles).contains self = true)
    (captures : Values (Component (assignment F G)) spec.captures)
    (body : RegionFunction (Component (assignment F G)) I
      (.index :: (spec.state ++ spec.captures), spec.state))
    {S : Type} (embed : S → Values (Component (assignment F G)) spec.state)
    (masked : ∀ value, maskValues self (ctx.mapScopes spec.stateScopes) (embed value) = embed value)
    (process : S → Nat → PIR.Proc I S)
    (equation : ∀ value index, body (.cons (some index) ((embed value).append captures)) =
      (process value index).bind (fun result => .done (embed result)))
    (count : Nat) (bounded : count ≤ spec.maximum)
    (state : Values (Component (assignment F G)) spec.state) (initial : S)
    (start : maskValues self (ctx.mapScopes spec.stateScopes) state = embed initial) :
    denoteRepeat spec ctx self (some count) state captures body =
      (Finite.fold process (List.range' 0 count) initial).bind (fun result => .done (embed result)) := by
  rw [repeat_admitted spec ctx self state captures body count inside bounded, start]
  apply Repeat.loop_embed
  intro value index
  rw [Repeat.step_equation, masked, equation, PIR.Proc.bind_assoc]
  apply congrArg (PIR.Proc.bind _)
  funext result
  simp only [PIR.Proc.bind, masked]

end ZkcExamples.Structured.NormalFormSteps
